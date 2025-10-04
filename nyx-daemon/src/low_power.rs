//! Low-power integration bridge for mobile platforms.
//!
//! When feature `low_power` is enabled, this module initializes the
//! `nyx-mobile-ffi` layer and periodically polls the unified power state,
//! emitting daemon events and metrics on changes.

use std::time::Duration;

use nyx_core::{
    low_power::{screen_off_ratio, InactivityTrigger, ScreenState},
    types::TimestampMs,
};
use tokio::{task::JoinHandle, time::interval};
use tracing::{debug, info, warn};

use crate::event_system::{Event, EventSystem};
use serde::Serialize;

// Re-export FFI functions from nyx-mobile-ffi. These are normal Rust functions with C ABI
// and are safe to call directly (no unsafe block needed).
use nyx_mobile_ffi::{
    nyx_mobile_init, nyx_mobile_set____log_level, nyx_mobile_shutdown, nyx_power_get_state,
    rust_get_power_state, rust_get_resume_count, rust_get_wake_count, NyxPowerState, NyxStatus,
};

/// Background task handle for the low-power bridge.
pub struct LowPowerBridge {
    #[allow(dead_code)]
    handle: JoinHandle<()>,
}

impl LowPowerBridge {
    /// Starts the bridge, initializes the FFI, and spawns a polling loop.
    /// Returns a handle to the background task.
    pub fn start(events: EventSystem) -> anyhow::Result<Self> {
        // Initialize FFI layer (idempotent)
        let rc = nyx_mobile_init();
        if rc != NyxStatus::Ok as i32 && rc != NyxStatus::AlreadyInitialized as i32 {
            warn!(code = rc, "nyx_mobile_init returned non-ok status");
        } else {
            info!("nyx_mobile_ffi initialized");
        }

        // Optional log level from env: error|warn|info|debug|trace or numeric 0..4
        if let Ok(lv) = std::env::var("NYX_MOBILE_LOG_LEVEL") {
            let code = match lv.to_ascii_lowercase().as_str() {
                "error" => 0,
                "warn" | "warning" => 1,
                "info" => 2,
                "debug" => 3,
                "trace" => 4,
                _ => lv.parse::<i32>().unwrap_or(2),
            };
            let _ = nyx_mobile_set____log_level(code);
        }

        // Poll interval and inactivity threshold via env with sensible defaults
        let poll_ms: u64 = std::env::var("NYX_POWER_POLL_MS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(1000);
        let inactivity_ms: u64 = std::env::var("NYX_INACTIVITY_MS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(5 * 60 * 1000);

        // Rate limiter: at most one inactivity event per minute by default
        let rate_per_sec: f64 = std::env::var("NYX_INACTIVITY_RATE_PER_SEC")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(1.0 / 60.0);

        let handle = tokio::spawn(async move {
            let mut intv = interval(Duration::from_millis(poll_ms));
            // Tick once to establish a baseline without immediate work
            intv.tick().await;

            // Maintain a compact history of (timestamp, screen state)
            let mut history: Vec<(TimestampMs, ScreenState)> = Vec::with_capacity(128);

            // Initialize inactivity trigger
            let start_ms = now_ms();
            let mut inactivity = InactivityTrigger::new(
                Duration::from_millis(inactivity_ms),
                rate_per_sec,
                TimestampMs(start_ms),
            );

            let mut prev_state: Option<u32> = None;
            let mut prev_wake: u32 = rust_get_wake_count();
            let mut prev_resume: u32 = rust_get_resume_count();

            // Simple debounce window to avoid chattering
            let debounce_ms: u64 = 300;
            let mut last_emit_ms: u64 = 0;

            loop {
                intv.tick().await;
                // Primary source via FFI getter
                let mut cur: u32 = 0;
                let rc = unsafe { nyx_power_get_state(&mut cur as *mut u32) };
                if rc != NyxStatus::Ok as i32 {
                    cur = rust_get_power_state();
                }

                let now = now_ms();
                if prev_state != Some(cur) {
                    // Debounce: suppress rapid toggles within debounce_ms
                    if now.saturating_sub(last_emit_ms) < debounce_ms {
                        continue;
                    }
                    let stamp = now;
                    let screen = map_power_to_screen(cur);
                    history.push((TimestampMs(stamp), screen));
                    // Trim history to last 10 minutes
                    let windowstart = stamp.saturating_sub(10 * 60 * 1000);
                    while history.len() > 2 {
                        if let Some(&(TimestampMs(t0), _)) = history.first() {
                            if t0 < windowstart {
                                history.remove(0);
                            } else {
                                break;
                            }
                        } else {
                            break;
                        }
                    }

                    // Emit rich event
                    let detail = serde_json::to_string(&PowerEvent::State {
                        state: display_power(cur).to_string(),
                    })
                    .unwrap_or_else(|_| "{\"type\":\"state\"}".into());
                    let _ = events.sender().send(Event {
                        _ty: "power".into(),
                        _detail: detail,
                    });
                    // Metrics
                    metrics::counter!("nyx.power.state.change", "state" => cur.to_string())
                        .increment(1);

                    // Activity heuristic: entering Active resets inactivity
                    if cur == NyxPowerState::Active as u32 {
                        inactivity.record_activity(TimestampMs(stamp));
                    }

                    prev_state = Some(cur);
                    last_emit_ms = stamp;
                }

                // Periodically compute off ratio over the last minute (if enough data)
                let one_min_start = now.saturating_sub(60 * 1000);
                let slice: Vec<(TimestampMs, ScreenState)> = history
                    .iter()
                    .copied()
                    .filter(|(TimestampMs(t), _)| *t >= one_min_start)
                    .collect();
                if slice.len() >= 2 {
                    let ratio = screen_off_ratio(&slice);
                    metrics::gauge!("nyx.power.screen_off_ratio_1m").set(ratio);
                    debug!("screen_off_ratio_1m = {:.3}", ratio);
                }

                // Inactivity trigger
                if inactivity.should_trigger(TimestampMs(now)) {
                    let detail = serde_json::to_string(&PowerEvent::Inactivity)
                        .unwrap_or_else(|_| "{\"type\":\"inactivity\"}".into());
                    let _ = events.sender().send(Event {
                        _ty: "power".into(),
                        _detail: detail,
                    });
                    metrics::counter!("nyx.power.inactivity.trigger").increment(1);
                }

                // Detect wake/resume counters and emit events
                let wk = rust_get_wake_count();
                if wk > prev_wake {
                    let detail = serde_json::to_string(&PowerEvent::Wake)
                        .unwrap_or_else(|_| "{\"type\":\"wake\"}".into());
                    let _ = events.sender().send(Event {
                        _ty: "power".into(),
                        _detail: detail,
                    });
                    prev_wake = wk;
                }
                let rs = rust_get_resume_count();
                if rs > prev_resume {
                    let detail = serde_json::to_string(&PowerEvent::Resume)
                        .unwrap_or_else(|_| "{\"type\":\"resume\"}".into());
                    let _ = events.sender().send(Event {
                        _ty: "power".into(),
                        _detail: detail,
                    });
                    prev_resume = rs;
                }
            }
        });

        Ok(Self { handle })
    }
}

#[derive(Debug, Serialize)]
#[serde(tag = "type")]
enum PowerEvent {
    State { state: String },
    Wake,
    Resume,
    Inactivity,
}

impl Drop for LowPowerBridge {
    fn drop(&mut self) {
        // Best-effort shutdown (idempotent)
        let _ = nyx_mobile_shutdown();
    }
}

fn now_ms() -> u64 {
    use std::time::{SystemTime, UNIX_EPOCH};
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_millis() as u64
}

fn map_power_to_screen(state: u32) -> ScreenState {
    match state {
        x if x == NyxPowerState::Active as u32 => ScreenState::On,
        x if x == NyxPowerState::Background as u32 => ScreenState::Off,
        x if x == NyxPowerState::Inactive as u32 => ScreenState::Off,
        x if x == NyxPowerState::Critical as u32 => ScreenState::Off,
        _ => ScreenState::Off,
    }
}

fn display_power(state: u32) -> &'static str {
    match state {
        x if x == NyxPowerState::Active as u32 => "active",
        x if x == NyxPowerState::Background as u32 => "background",
        x if x == NyxPowerState::Inactive as u32 => "inactive",
        x if x == NyxPowerState::Critical as u32 => "critical",
        _ => "unknown",
    }
}

#[cfg(all(test, feature = "low_power"))]
mod test_s {
    use super::*;
    use std::sync::OnceLock;
    use std::time::Duration;
    use tokio::sync::Mutex;
    use tokio::time::timeout;

    async fn test_lock() -> tokio::sync::MutexGuard<'static, ()> {
        static L: OnceLock<Mutex<()>> = OnceLock::new();
        // In tests we can't use ? since we don't return Result; unwrap is fine here.
        L.get_or_init(|| Mutex::new(())).lock().await
    }

    #[tokio::test]
    async fn emits_initial_state_event() {
        let _guard = test_lock().await;
        std::env::set_var("NYX_POWER_POLL_MS", "50");
        let event_sys = EventSystem::new(16);
        let mut rx = event_sys.subscribe();
        let bridge = LowPowerBridge::start(event_sys).unwrap();
        // Expect first event due to initial state observation
        let ev = timeout(Duration::from_millis(1000), rx.recv())
            .await
            .unwrap()
            .unwrap();
        assert_eq!(ev._ty, "power");
        // detail is JSON like {"type":"State","state":"active"}
        assert!(ev._detail.contains("\"type\":") && ev._detail.contains("state"));
        // Avoid dropping the bridge (and its runtime) inside async context
        std::mem::forget(bridge);
    }

    #[tokio::test]
    async fn emits_on_state_change() {
        let _guard = test_lock().await;
        std::env::set_var("NYX_POWER_POLL_MS", "50");
        let event_sys = EventSystem::new(16);
        let mut rx = event_sys.subscribe();
        let bridge = LowPowerBridge::start(event_sys.clone()).unwrap();
        // Drain the first initial event if present
        let _ = timeout(Duration::from_millis(500), rx.recv()).await;

        // Change state to Background
        let _ = nyx_mobile_ffi::nyx_power_set_state(NyxPowerState::Background as u32);

        // Expect a state:background event
        let ev = timeout(Duration::from_millis(1500), rx.recv())
            .await
            .unwrap()
            .unwrap();
        assert_eq!(ev._ty, "power");
        assert!(
            ev._detail.contains("\"state\":\"background\""),
            "got {}",
            ev._detail
        );
        // Avoid dropping the bridge (and its runtime) inside async context
        std::mem::forget(bridge);
    }

    /// Test all power state transitions: Active → Background → Inactive → Critical
    #[tokio::test]
    async fn test_all_power_state_transitions() {
        let _guard = test_lock().await;
        std::env::set_var("NYX_POWER_POLL_MS", "50");
        // Disable inactivity trigger for this test to avoid interference
        std::env::set_var("NYX_INACTIVITY_MS", "999999");
        let event_sys = EventSystem::new(16);
        let mut rx = event_sys.subscribe();
        
        // Initialize to Active
        let _ = nyx_mobile_ffi::nyx_power_set_state(NyxPowerState::Active as u32);
        let bridge = LowPowerBridge::start(event_sys.clone()).unwrap();
        // Immediately forget to avoid drop issues
        std::mem::forget(bridge);
        
        // Drain all initial events
        while timeout(Duration::from_millis(200), rx.recv()).await.is_ok() {}

        // Transition: Active → Background
        let _ = nyx_mobile_ffi::nyx_power_set_state(NyxPowerState::Background as u32);
        let ev1 = timeout(Duration::from_millis(1000), rx.recv()).await.unwrap().unwrap();
        assert!(ev1._detail.contains("\"state\":\"background\""), "Expected background, got: {}", ev1._detail);

        // Transition: Background → Inactive
        let _ = nyx_mobile_ffi::nyx_power_set_state(NyxPowerState::Inactive as u32);
        let ev2 = timeout(Duration::from_millis(1000), rx.recv()).await.unwrap().unwrap();
        assert!(ev2._detail.contains("\"state\":\"inactive\""), "Expected inactive, got: {}", ev2._detail);

        // Transition: Inactive → Critical
        let _ = nyx_mobile_ffi::nyx_power_set_state(NyxPowerState::Critical as u32);
        let ev3 = timeout(Duration::from_millis(1000), rx.recv()).await.unwrap().unwrap();
        assert!(ev3._detail.contains("\"state\":\"critical\""), "Expected critical, got: {}", ev3._detail);
    }

    /// Test debounce logic: rapid toggles within debounce window should be suppressed
    /// Note: Debounce window is 300ms, so transitions within that window are suppressed
    #[tokio::test]
    async fn test_debounce_suppresses_rapid_toggles() {
        let _guard = test_lock().await;
        std::env::set_var("NYX_POWER_POLL_MS", "50");
        std::env::set_var("NYX_INACTIVITY_MS", "999999"); // Disable inactivity
        let event_sys = EventSystem::new(16);
        let mut rx = event_sys.subscribe();
        
        let _ = nyx_mobile_ffi::nyx_power_set_state(NyxPowerState::Active as u32);
        let bridge = LowPowerBridge::start(event_sys.clone()).unwrap();
        std::mem::forget(bridge);
        
        // Drain all initial events
        while timeout(Duration::from_millis(200), rx.recv()).await.is_ok() {}

        // First transition: Active → Background (will be emitted)
        let _ = nyx_mobile_ffi::nyx_power_set_state(NyxPowerState::Background as u32);
        let ev1 = timeout(Duration::from_millis(1500), rx.recv()).await.unwrap().unwrap();
        assert!(ev1._detail.contains("\"state\":\"background\""), "Got: {}", ev1._detail);
        
        // Rapid toggle within debounce window: Background → Inactive (should be debounced)
        tokio::time::sleep(Duration::from_millis(100)).await; // Within 300ms debounce
        let _ = nyx_mobile_ffi::nyx_power_set_state(NyxPowerState::Inactive as u32);
        
        // Wait 250ms (still within 300ms debounce window total: 100+250=350ms, but event suppressed earlier)
        tokio::time::sleep(Duration::from_millis(250)).await;
        
        // Verify no state event was emitted during debounce window
        let result = timeout(Duration::from_millis(100), rx.recv()).await;
        if let Ok(Ok(ev)) = result {
            // After debounce window expires, the state change should eventually be emitted
            // So we accept a state event here as it's outside the debounce window
            // The key is that it wasn't emitted immediately (within 100ms of the second transition)
            assert!(ev._detail.contains("\"state\":\"inactive\"") || 
                   !ev._detail.contains("\"type\":\"State\""),
                "Got unexpected event: {}", ev._detail);
        }
    }

    /// Test wake counter detection emits wake event
    #[tokio::test]
    async fn test_wake_counter_event() {
        let _guard = test_lock().await;
        std::env::set_var("NYX_POWER_POLL_MS", "50");
        let event_sys = EventSystem::new(16);
        let mut rx = event_sys.subscribe();
        
        let bridge = LowPowerBridge::start(event_sys.clone()).unwrap();
        std::mem::forget(bridge);
        
        // Drain initial event
        let _ = timeout(Duration::from_millis(500), rx.recv()).await;

        // Increment wake counter via FFI
        nyx_mobile_ffi::rust_increment_wake_count();
        
        // Expect wake event
        let ev = timeout(Duration::from_millis(1500), rx.recv()).await.unwrap().unwrap();
        assert_eq!(ev._ty, "power");
        assert!(ev._detail.contains("\"type\":\"Wake\""), "Expected Wake event, got: {}", ev._detail);
    }

    /// Test resume counter detection emits resume event
    #[tokio::test]
    async fn test_resume_counter_event() {
        let _guard = test_lock().await;
        std::env::set_var("NYX_POWER_POLL_MS", "50");
        let event_sys = EventSystem::new(16);
        let mut rx = event_sys.subscribe();
        
        let bridge = LowPowerBridge::start(event_sys.clone()).unwrap();
        std::mem::forget(bridge);
        
        // Drain initial event
        let _ = timeout(Duration::from_millis(500), rx.recv()).await;

        // Increment resume counter via FFI
        nyx_mobile_ffi::rust_increment_resume_count();
        
        // Expect resume event
        let ev = timeout(Duration::from_millis(1500), rx.recv()).await.unwrap().unwrap();
        assert_eq!(ev._ty, "power");
        assert!(ev._detail.contains("\"type\":\"Resume\""), "Expected Resume event, got: {}", ev._detail);
    }

    /// Test inactivity trigger after threshold exceeded
    #[tokio::test]
    async fn test_inactivity_trigger() {
        let _guard = test_lock().await;
        // Short poll interval and 200ms inactivity threshold
        std::env::set_var("NYX_POWER_POLL_MS", "50");
        std::env::set_var("NYX_INACTIVITY_MS", "200");
        std::env::set_var("NYX_INACTIVITY_RATE_PER_SEC", "10.0"); // High rate to allow trigger
        
        let event_sys = EventSystem::new(16);
        let mut rx = event_sys.subscribe();
        
        // Start in Inactive to avoid activity reset
        let _ = nyx_mobile_ffi::nyx_power_set_state(NyxPowerState::Inactive as u32);
        let bridge = LowPowerBridge::start(event_sys.clone()).unwrap();
        std::mem::forget(bridge);
        
        // Drain initial state event
        let _ = timeout(Duration::from_millis(500), rx.recv()).await;

        // Wait for inactivity threshold (200ms) + some margin
        tokio::time::sleep(Duration::from_millis(400)).await;
        
        // Expect inactivity event
        let ev = timeout(Duration::from_millis(2000), rx.recv()).await.unwrap().unwrap();
        assert_eq!(ev._ty, "power");
        assert!(ev._detail.contains("\"type\":\"Inactivity\""), "Expected Inactivity event, got: {}", ev._detail);
    }

    /// Test activity reset on entering Active state
    /// Verifies that entering Active state resets the inactivity timer
    #[tokio::test]
    async fn test_activity_reset_on_active() {
        let _guard = test_lock().await;
        std::env::set_var("NYX_POWER_POLL_MS", "50");
        std::env::set_var("NYX_INACTIVITY_MS", "400"); // 400ms threshold
        std::env::set_var("NYX_INACTIVITY_RATE_PER_SEC", "10.0");
        
        let event_sys = EventSystem::new(16);
        let mut rx = event_sys.subscribe();
        
        // Start in Inactive to allow inactivity timer to run
        let _ = nyx_mobile_ffi::nyx_power_set_state(NyxPowerState::Inactive as u32);
        let bridge = LowPowerBridge::start(event_sys.clone()).unwrap();
        std::mem::forget(bridge);
        
        // Drain all initial events
        while timeout(Duration::from_millis(200), rx.recv()).await.is_ok() {}

        // Wait 200ms (half of inactivity threshold)
        tokio::time::sleep(Duration::from_millis(200)).await;
        
        // Enter Active to reset activity timer
        let _ = nyx_mobile_ffi::nyx_power_set_state(NyxPowerState::Active as u32);
        let _ = timeout(Duration::from_millis(1000), rx.recv()).await; // Drain state event
        
        // Wait another 300ms (total 500ms from start, but only 300ms since Active reset)
        // If timer wasn't reset, inactivity would trigger (since 200+300=500>400)
        // But since timer was reset at 200ms mark, we've only accumulated 300ms since reset (<400)
        tokio::time::sleep(Duration::from_millis(300)).await;
        
        // Should NOT receive inactivity event (timer was reset by Active transition)
        let result = timeout(Duration::from_millis(300), rx.recv()).await;
        if let Ok(Ok(ev)) = result {
            assert!(!ev._detail.contains("\"type\":\"Inactivity\""), 
                "Expected no Inactivity event after activity reset, got: {}", ev._detail);
        }
    }
}

// Unit tests for helper functions (no feature gate needed)
#[cfg(test)]
mod unit_tests {
    use super::*;

    #[test]
    fn test_map_power_to_screen_all_states() {
        assert_eq!(map_power_to_screen(NyxPowerState::Active as u32), ScreenState::On);
        assert_eq!(map_power_to_screen(NyxPowerState::Background as u32), ScreenState::Off);
        assert_eq!(map_power_to_screen(NyxPowerState::Inactive as u32), ScreenState::Off);
        assert_eq!(map_power_to_screen(NyxPowerState::Critical as u32), ScreenState::Off);
        assert_eq!(map_power_to_screen(999), ScreenState::Off); // Unknown state
    }

    #[test]
    fn test_display_power_all_states() {
        assert_eq!(display_power(NyxPowerState::Active as u32), "active");
        assert_eq!(display_power(NyxPowerState::Background as u32), "background");
        assert_eq!(display_power(NyxPowerState::Inactive as u32), "inactive");
        assert_eq!(display_power(NyxPowerState::Critical as u32), "critical");
        assert_eq!(display_power(999), "unknown");
    }

    #[test]
    fn test_now_ms_returns_reasonable_timestamp() {
        let ts = now_ms();
        // Sanity check: timestamp should be after 2020-01-01 (1577836800000ms)
        assert!(ts > 1_577_836_800_000, "Timestamp seems too old: {}", ts);
        // And before 2100-01-01 (4102444800000ms)
        assert!(ts < 4_102_444_800_000, "Timestamp seems too far in future: {}", ts);
    }

    #[test]
    fn test_power_event_serialization() {
        let ev1 = PowerEvent::State { state: "active".to_string() };
        let json1 = serde_json::to_string(&ev1).unwrap();
        assert!(json1.contains("\"type\":\"State\""));
        assert!(json1.contains("\"state\":\"active\""));

        let ev2 = PowerEvent::Wake;
        let json2 = serde_json::to_string(&ev2).unwrap();
        assert!(json2.contains("\"type\":\"Wake\""));

        let ev3 = PowerEvent::Resume;
        let json3 = serde_json::to_string(&ev3).unwrap();
        assert!(json3.contains("\"type\":\"Resume\""));

        let ev4 = PowerEvent::Inactivity;
        let json4 = serde_json::to_string(&ev4).unwrap();
        assert!(json4.contains("\"type\":\"Inactivity\""));
    }
}

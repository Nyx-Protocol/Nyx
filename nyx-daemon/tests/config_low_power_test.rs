#![forbid(unsafe_code)]

use nyx_daemon::config_manager::{ConfigManager, LowPowerConfig, NyxConfig};
use std::path::PathBuf;

#[tokio::test]
async fn test_low_power_config_defaults() {
    let config = LowPowerConfig::default();
    assert!(config.enabled);
    assert_eq!(config.background_cover_traffic_ratio, 0.08);
    assert_eq!(config.active_cover_traffic_ratio, 0.4);
    assert_eq!(config.battery_critical_threshold, 10);
    assert_eq!(config.battery_low_threshold, 20);
    assert_eq!(config.battery_hysteresis, 5);
    assert_eq!(config.screen_off_cooldown_ms, 5000);
    assert_eq!(config.app_background_timeout, 10);
}

#[tokio::test]
async fn test_nyx_config_with_low_power() {
    let config = NyxConfig::default();
    assert!(config.low_power.enabled);
    assert_eq!(config.low_power.background_cover_traffic_ratio, 0.08);
}

#[tokio::test]
async fn test_config_manager_low_power() {
    let config = NyxConfig::default();
    let manager = ConfigManager::new(config, None);

    let cfg = manager.getconfig().await;
    assert!(cfg.low_power.enabled);
    assert_eq!(cfg.low_power.battery_critical_threshold, 10);
    assert_eq!(cfg.low_power.battery_low_threshold, 20);
}

#[tokio::test]
async fn test_low_power_config_validation_valid() {
    let config = NyxConfig {
        low_power: LowPowerConfig {
            enabled: true,
            background_cover_traffic_ratio: 0.08,
            active_cover_traffic_ratio: 0.4,
            battery_critical_threshold: 10,
            battery_low_threshold: 20,
            battery_hysteresis: 5,
            screen_off_cooldown_ms: 5000,
            app_background_timeout: 10,
        },
        ..Default::default()
    };

    let errors = ConfigManager::validate_static(&config);
    assert!(
        errors.is_empty(),
        "Expected no validation errors, got: {:?}",
        errors
    );
}

#[tokio::test]
async fn test_low_power_config_validation_invalid_ratio() {
    let config = NyxConfig {
        low_power: LowPowerConfig {
            background_cover_traffic_ratio: 1.5, // Invalid: > 1.0
            ..Default::default()
        },
        ..Default::default()
    };

    let errors = ConfigManager::validate_static(&config);
    assert!(!errors.is_empty());
    assert!(errors
        .iter()
        .any(|e| e.contains("background_cover_traffic_ratio")));
}

#[tokio::test]
async fn test_low_power_config_validation_invalid_battery_thresholds() {
    let config = NyxConfig {
        low_power: LowPowerConfig {
            battery_critical_threshold: 150, // Invalid: > 100
            ..Default::default()
        },
        ..Default::default()
    };

    let errors = ConfigManager::validate_static(&config);
    assert!(!errors.is_empty());
    assert!(errors
        .iter()
        .any(|e| e.contains("battery_critical_threshold")));
}

#[tokio::test]
async fn test_low_power_config_validation_threshold_order() {
    let config = NyxConfig {
        low_power: LowPowerConfig {
            battery_critical_threshold: 25, // Invalid: >= battery_low_threshold
            battery_low_threshold: 20,
            ..Default::default()
        },
        ..Default::default()
    };

    let errors = ConfigManager::validate_static(&config);
    assert!(!errors.is_empty());
    assert!(errors
        .iter()
        .any(|e| e.contains("battery_critical_threshold must be < battery_low_threshold")));
}

#[tokio::test]
async fn test_low_power_config_validation_excessive_hysteresis() {
    let config = NyxConfig {
        low_power: LowPowerConfig {
            battery_hysteresis: 25, // Invalid: > 20
            ..Default::default()
        },
        ..Default::default()
    };

    let errors = ConfigManager::validate_static(&config);
    assert!(!errors.is_empty());
    assert!(errors.iter().any(|e| e.contains("battery_hysteresis")));
}

#[tokio::test]
async fn test_low_power_config_validation_excessive_cooldown() {
    let config = NyxConfig {
        low_power: LowPowerConfig {
            screen_off_cooldown_ms: 100_000, // Invalid: > 60000
            ..Default::default()
        },
        ..Default::default()
    };

    let errors = ConfigManager::validate_static(&config);
    assert!(!errors.is_empty());
    assert!(errors.iter().any(|e| e.contains("screen_off_cooldown_ms")));
}

#[tokio::test]
async fn test_low_power_config_validation_excessive_timeout() {
    let config = NyxConfig {
        low_power: LowPowerConfig {
            app_background_timeout: 500, // Invalid: > 300
            ..Default::default()
        },
        ..Default::default()
    };

    let errors = ConfigManager::validate_static(&config);
    assert!(!errors.is_empty());
    assert!(errors.iter().any(|e| e.contains("app_background_timeout")));
}

#[tokio::test]
async fn test_load_low_power_config_from_toml() {
    let toml_content = r#"
listen_port = 43300

[low_power]
enabled = false
background_cover_traffic_ratio = 0.05
active_cover_traffic_ratio = 0.35
battery_critical_threshold = 8
battery_low_threshold = 18
battery_hysteresis = 3
screen_off_cooldown_ms = 3000
app_background_timeout = 15
"#;

    let config: NyxConfig = toml::from_str(toml_content).expect("Failed to parse TOML");

    assert!(!config.low_power.enabled);
    assert_eq!(config.low_power.background_cover_traffic_ratio, 0.05);
    assert_eq!(config.low_power.active_cover_traffic_ratio, 0.35);
    assert_eq!(config.low_power.battery_critical_threshold, 8);
    assert_eq!(config.low_power.battery_low_threshold, 18);
    assert_eq!(config.low_power.battery_hysteresis, 3);
    assert_eq!(config.low_power.screen_off_cooldown_ms, 3000);
    assert_eq!(config.low_power.app_background_timeout, 15);
}

#[tokio::test]
async fn test_load_partial_low_power_config_from_toml() {
    // Test that partial config uses defaults for missing fields
    let toml_content = r#"
listen_port = 43300

[low_power]
enabled = false
battery_critical_threshold = 12
"#;

    let config: NyxConfig = toml::from_str(toml_content).expect("Failed to parse TOML");

    assert!(!config.low_power.enabled);
    assert_eq!(config.low_power.battery_critical_threshold, 12);
    // Other fields should use defaults
    assert_eq!(config.low_power.background_cover_traffic_ratio, 0.08);
    assert_eq!(config.low_power.battery_low_threshold, 20);
}

#[tokio::test]
async fn test_load_nyx_toml_with_low_power() {
    // Test loading the actual nyx.toml file
    let workspace_root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .unwrap()
        .to_path_buf();
    let nyx_toml_path = workspace_root.join("nyx.toml");

    if !nyx_toml_path.exists() {
        eprintln!("Skipping test: nyx.toml not found at {:?}", nyx_toml_path);
        return;
    }

    let content = std::fs::read_to_string(&nyx_toml_path).expect("Failed to read nyx.toml");
    let mut config: NyxConfig = toml::from_str(&content).expect("Failed to parse nyx.toml");

    // Verify low_power section was loaded
    assert!(config.low_power.enabled);
    assert_eq!(config.low_power.background_cover_traffic_ratio, 0.08);
    assert_eq!(config.low_power.active_cover_traffic_ratio, 0.4);
    assert_eq!(config.low_power.battery_critical_threshold, 10);
    assert_eq!(config.low_power.battery_low_threshold, 20);

    // Override node_id to valid value for validation (nyx.toml has "auto" which is not 32-byte hex)
    config.node_id =
        Some("0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef".to_string());

    // Validate the loaded config (with corrected node_id)
    let errors = ConfigManager::validate_static(&config);
    assert!(
        errors.is_empty(),
        "nyx.toml validation failed: {:?}",
        errors
    );
}

#[tokio::test]
async fn test_screen_off_detector_from_low_power_config() {
    use nyx_daemon::screen_off_detection::{PowerState, ScreenOffDetector, ScreenState};

    let low_power_config = LowPowerConfig {
        enabled: true,
        background_cover_traffic_ratio: 0.05,
        active_cover_traffic_ratio: 0.35,
        battery_critical_threshold: 8,
        battery_low_threshold: 18,
        battery_hysteresis: 3,
        screen_off_cooldown_ms: 3000,
        app_background_timeout: 15,
    };

    // Create detector from LowPowerConfig
    let detector = ScreenOffDetector::from_low_power_config(low_power_config);

    // Verify config was properly converted (use synchronous API)
    let screen_state = detector.get_screen_state();
    let power_state = detector.get_power_state();
    let battery = detector.get_battery_level();

    assert_eq!(screen_state, ScreenState::On);
    assert_eq!(power_state, PowerState::Active);
    assert!((battery - 1.0).abs() < f32::EPSILON);

    // Verify cover traffic ratio
    let cover_ratio = detector.get_cover_traffic_ratio();
    assert!((cover_ratio - 0.35).abs() < f32::EPSILON);
}

#[tokio::test]
async fn test_screen_off_detector_integration_with_config_manager() {
    use nyx_daemon::screen_off_detection::ScreenOffDetector;

    // Create config with custom low_power settings
    let config = NyxConfig {
        low_power: LowPowerConfig {
            enabled: true,
            background_cover_traffic_ratio: 0.06,
            active_cover_traffic_ratio: 0.42,
            battery_critical_threshold: 12,
            battery_low_threshold: 22,
            battery_hysteresis: 6,
            screen_off_cooldown_ms: 4000,
            app_background_timeout: 12,
        },
        ..Default::default()
    };

    // Create detector from config
    let detector = ScreenOffDetector::from_low_power_config(config.low_power.clone());

    // Verify detector can be created and used (use synchronous API)
    let stats = detector.get_stats();
    assert!((stats.current_cover_ratio - 0.42).abs() < f32::EPSILON);
}

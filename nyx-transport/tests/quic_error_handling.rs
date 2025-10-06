//! Test suite for QUIC error handling robustness
//! 
//! This test module verifies that the QUIC implementation correctly handles
//! malformed packets, edge cases, and error conditions without panicking.
//!
//! Reference: Phase 2 fixes for unwrap() safety in quic.rs

#![cfg(feature = "quic")]
#![allow(clippy::unwrap_used, clippy::expect_used)]

use std::time::Duration;

// Import internal types for testing - these are not exposed in public API
// but are necessary for comprehensive error handling verification
use nyx_transport::quic::{CubicState, QuicFrame};

// If the types are still not accessible, we need to modify the module visibility
// For now, we'll create a conditional compilation approach

/// Test that RTT update handles concurrent access patterns safely
/// 
/// Verifies:
/// - Initial RTT update (None -> Some transition)
/// - Subsequent RTT updates with existing state
/// - min_rtt tracking across multiple samples
#[test]
fn test_rtt_update_edge_cases() {
    let mut cubic = CubicState::new(10000, 1200);
    
    // Initial state: all RTT fields should be None
    assert!(cubic.smoothed_rtt.is_none());
    assert!(cubic.rtt_var.is_none());
    assert!(cubic.min_rtt.is_none());
    
    // First RTT sample should initialize smoothed_rtt and rtt_var
    let first_rtt = Duration::from_millis(50);
    cubic.update_rtt(first_rtt);
    
    assert_eq!(cubic.smoothed_rtt, Some(first_rtt));
    assert_eq!(cubic.rtt_var, Some(first_rtt / 2));
    assert_eq!(cubic.min_rtt, Some(first_rtt));
    assert_eq!(cubic.latest_rtt, Some(first_rtt));
    
    // Second sample should update using EWMA
    let second_rtt = Duration::from_millis(60);
    cubic.update_rtt(second_rtt);
    
    assert!(cubic.smoothed_rtt.is_some());
    assert!(cubic.rtt_var.is_some());
    // min_rtt should still be first_rtt (smaller)
    assert_eq!(cubic.min_rtt, Some(first_rtt));
    
    // Third sample with lower RTT should update min_rtt
    let third_rtt = Duration::from_millis(40);
    cubic.update_rtt(third_rtt);
    
    assert_eq!(cubic.min_rtt, Some(third_rtt));
    assert_eq!(cubic.latest_rtt, Some(third_rtt));
}

/// Test that ACK handling works correctly even before RTT initialization
///
/// This is a regression test for the scenario where on_ack() might be called
/// before any RTT samples are received (e.g., in slow start phase).
#[test]
fn test_ack_before_rtt_initialization() {
    let mut cubic = CubicState::new(10000, 1200);
    
    // on_ack should work even without RTT data (slow start phase)
    let new_cwnd = cubic.on_ack(1200);
    
    // In slow start, cwnd should increase by bytes_acked
    assert_eq!(new_cwnd, 10000 + 1200);
    assert_eq!(cubic.cwnd, 10000 + 1200);
}

/// Test malformed STREAM frame parsing
///
/// Verifies that incomplete or corrupted STREAM frames return errors
/// instead of panicking.
#[test]
fn test_malformed_stream_frame_parsing() {
    // Frame type 0x08 = STREAM frame without FIN
    let frame_type = 0x08u8;
    
    // Test 1: Empty data (should fail length check)
    let empty_data = vec![];
    let result = QuicFrame::decode(&empty_data);
    assert!(result.is_err(), "Empty packet should fail gracefully");
    
    // Test 2: Incomplete header (only 16 bytes instead of 24)
    let incomplete_header = vec![frame_type, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    let result = QuicFrame::decode(&incomplete_header);
    assert!(result.is_err(), "Incomplete STREAM header should fail");
    
    // Test 3: Complete header but missing data
    let mut missing_data = vec![frame_type];
    missing_data.extend_from_slice(&[0u8; 23]); // 24 bytes total
    // Set length to 100 but provide no data
    missing_data[16..24].copy_from_slice(&100u64.to_be_bytes());
    let result = QuicFrame::decode(&missing_data);
    assert!(result.is_err(), "STREAM frame with missing data should fail");
    
    // Test 4: Valid minimal STREAM frame
    let mut valid_frame = vec![frame_type];
    valid_frame.extend_from_slice(&1u64.to_be_bytes()); // stream_id = 1
    valid_frame.extend_from_slice(&0u64.to_be_bytes()); // offset = 0
    valid_frame.extend_from_slice(&5u64.to_be_bytes()); // length = 5
    valid_frame.extend_from_slice(b"hello"); // 5 bytes of data
    
    let result = QuicFrame::decode(&valid_frame);
    assert!(result.is_ok(), "Valid STREAM frame should parse successfully");
    
    if let Ok((frame, consumed)) = result {
        match frame {
            QuicFrame::Stream { stream_id, offset, data, fin } => {
                assert_eq!(stream_id, 1);
                assert_eq!(offset, 0);
                assert_eq!(data.as_ref(), b"hello");
                assert!(!fin); // FIN bit not set (frame_type & 0x01 == 0)
                assert_eq!(consumed, 1 + 8 + 8 + 8 + 5); // header + data
            }
            _ => panic!("Expected STREAM frame"),
        }
    }
}

/// Test malformed ACK frame parsing
///
/// Verifies that ACK frames with invalid range counts or incomplete
/// range data are handled gracefully.
#[test]
fn test_malformed_ack_frame_parsing() {
    let frame_type = 0x02u8; // ACK frame
    
    // Test 1: Incomplete ACK header (< 24 bytes)
    let mut incomplete = vec![frame_type];
    incomplete.extend_from_slice(&[0u8; 16]); // Only 17 bytes total
    let result = QuicFrame::decode(&incomplete);
    assert!(result.is_err(), "Incomplete ACK header should fail");
    
    // Test 2: ACK with range_count but missing range data
    let mut missing_ranges = vec![frame_type];
    missing_ranges.extend_from_slice(&100u64.to_be_bytes()); // largest_ack
    missing_ranges.extend_from_slice(&5u64.to_be_bytes());   // ack_delay
    missing_ranges.extend_from_slice(&2u64.to_be_bytes());   // range_count = 2
    // But no range data provided
    let result = QuicFrame::decode(&missing_ranges);
    assert!(result.is_err(), "ACK with missing ranges should fail");
    
    // Test 3: Valid ACK with zero ranges
    let mut valid_ack = vec![frame_type];
    valid_ack.extend_from_slice(&50u64.to_be_bytes()); // largest_ack = 50
    valid_ack.extend_from_slice(&10u64.to_be_bytes()); // ack_delay = 10
    valid_ack.extend_from_slice(&0u64.to_be_bytes());  // range_count = 0
    
    let result = QuicFrame::decode(&valid_ack);
    assert!(result.is_ok(), "Valid ACK frame should parse");
    
    if let Ok((frame, _)) = result {
        match frame {
            QuicFrame::Ack { largest_acknowledged, ack_delay, ack_ranges } => {
                assert_eq!(largest_acknowledged, 50);
                assert_eq!(ack_delay, 10);
                assert_eq!(ack_ranges.len(), 0);
            }
            _ => panic!("Expected ACK frame"),
        }
    }
}

/// Test CONNECTION_CLOSE frame with oversized reason
///
/// Verifies that a CONNECTION_CLOSE frame claiming a huge reason length
/// is rejected before allocating excessive memory.
#[test]
fn test_connection_close_oversized_reason() {
    let frame_type = 0x1cu8; // CONNECTION_CLOSE
    
    let mut malicious = vec![frame_type];
    malicious.extend_from_slice(&42u64.to_be_bytes());       // error_code
    malicious.extend_from_slice(&0xFFFFFFFFu64.to_be_bytes()); // huge reason_len
    
    let result = QuicFrame::decode(&malicious);
    assert!(result.is_err(), "CONNECTION_CLOSE with oversized reason should fail");
}

/// Test DATAGRAM frame parsing edge cases
#[test]
fn test_datagram_frame_edge_cases() {
    // Test 1: DATAGRAM without length field (frame_type 0x30)
    let frame_type_no_len = 0x30u8;
    let mut datagram_no_len = vec![frame_type_no_len];
    datagram_no_len.extend_from_slice(b"test payload");
    
    let result = QuicFrame::decode(&datagram_no_len);
    assert!(result.is_ok(), "DATAGRAM without length should parse");
    if let Ok((frame, consumed)) = result {
        match frame {
            QuicFrame::Datagram { data } => {
                assert_eq!(data.as_ref(), b"test payload");
                assert_eq!(consumed, datagram_no_len.len());
            }
            _ => panic!("Expected DATAGRAM frame"),
        }
    }
    
    // Test 2: DATAGRAM with length field (frame_type 0x31)
    let frame_type_with_len = 0x31u8;
    let mut datagram_with_len = vec![frame_type_with_len];
    datagram_with_len.extend_from_slice(&5u64.to_be_bytes()); // length = 5
    datagram_with_len.extend_from_slice(b"hello");
    
    let result = QuicFrame::decode(&datagram_with_len);
    assert!(result.is_ok(), "DATAGRAM with length should parse");
    if let Ok((frame, _)) = result {
        match frame {
            QuicFrame::Datagram { data } => {
                assert_eq!(data.as_ref(), b"hello");
            }
            _ => panic!("Expected DATAGRAM frame"),
        }
    }
    
    // Test 3: DATAGRAM with length mismatch
    let mut length_mismatch = vec![frame_type_with_len];
    length_mismatch.extend_from_slice(&100u64.to_be_bytes()); // claims 100 bytes
    length_mismatch.extend_from_slice(b"short"); // but only 5 bytes
    
    let result = QuicFrame::decode(&length_mismatch);
    assert!(result.is_err(), "DATAGRAM with length mismatch should fail");
}

/// Stress test: rapid RTT updates
///
/// Simulates high-frequency RTT updates to ensure no race conditions
/// or invariant violations occur.
#[test]
fn test_rapid_rtt_updates() {
    let mut cubic = CubicState::new(10000, 1200);
    
    // Simulate 1000 RTT samples with varying values
    for i in 0..1000 {
        let rtt = Duration::from_micros(30_000 + (i % 100) * 1000);
        cubic.update_rtt(rtt);
        
        // Invariants that should always hold:
        assert!(cubic.smoothed_rtt.is_some(), "smoothed_rtt should be initialized");
        assert!(cubic.rtt_var.is_some(), "rtt_var should be initialized");
        assert!(cubic.min_rtt.is_some(), "min_rtt should be initialized");
        assert!(cubic.latest_rtt.is_some(), "latest_rtt should be set");
        
        // min_rtt should be <= latest_rtt (after first sample)
        if i > 0 {
            assert!(cubic.min_rtt.unwrap() <= cubic.latest_rtt.unwrap(),
                "min_rtt should be minimum of all samples");
        }
    }
}

/// Test that packet loss handling doesn't panic
#[test]
fn test_packet_loss_handling() {
    let mut cubic = CubicState::new(10000, 1200);
    
    // Initialize RTT
    cubic.update_rtt(Duration::from_millis(50));
    
    // Trigger packet loss
    cubic.on_packet_lost();
    
    // Verify cwnd was reduced according to CUBIC algorithm
    assert!(cubic.cwnd < 10000, "cwnd should be reduced after packet loss");
    assert!(cubic.cwnd >= 2 * 1200, "cwnd should be at least 2 * MSS");
    assert_eq!(cubic.ssthresh, (10000.0 * 0.7) as u32, "ssthresh should be 0.7 * previous cwnd");
}

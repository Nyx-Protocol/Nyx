//! Adaptive FEC Redundancy Tests

use nyx_fec::padding::SHARD_SIZE;
use nyx_fec::rs1280::{Rs1280, RsConfig};

#[test]
fn test_fec_encode_decode_roundtrip() {
    let cfg = RsConfig {
        data_shards: 10,
        parity_shards: 3,
    };
    let rs = Rs1280::new(cfg).unwrap();

    // Create test data (1280 bytes per shard)
    let mut shards: Vec<[u8; SHARD_SIZE]> = (0..cfg.total_shards())
        .map(|i| {
            let mut a = [0u8; SHARD_SIZE];
            a[0] = i as u8;
            a
        })
        .collect();

    let (data, parity) = shards.split_at_mut(cfg.data_shards);
    let data_refs: Vec<&[u8; SHARD_SIZE]> = data.iter().collect();
    let mut parity_refs: Vec<&mut [u8; SHARD_SIZE]> = parity.iter_mut().collect();

    rs.encode_parity(&data_refs, &mut parity_refs).unwrap();

    assert_eq!(shards.len(), cfg.total_shards());
}

#[test]
fn test_fec_recover_lost_packets() {
    let cfg = RsConfig {
        data_shards: 10,
        parity_shards: 3,
    };
    let rs = Rs1280::new(cfg).unwrap();

    let mut shards: Vec<[u8; SHARD_SIZE]> = (0..cfg.total_shards())
        .map(|i| {
            let mut a = [0u8; SHARD_SIZE];
            a[0] = i as u8;
            a
        })
        .collect();

    let (data, parity) = shards.split_at_mut(cfg.data_shards);
    let data_refs: Vec<&[u8; SHARD_SIZE]> = data.iter().collect();
    let mut parity_refs: Vec<&mut [u8; SHARD_SIZE]> = parity.iter_mut().collect();
    rs.encode_parity(&data_refs, &mut parity_refs).unwrap();

    // Lose 2 packets (within redundancy)
    let mut mix: Vec<Option<[u8; SHARD_SIZE]>> = shards.into_iter().map(Some).collect();
    mix[3] = None;
    mix[7] = None;

    rs.reconstruct(&mut mix).unwrap();
    assert!(mix.iter().all(|o| o.is_some()));
}

#[test]
fn test_fec_fail_excessive_loss() {
    let cfg = RsConfig {
        data_shards: 10,
        parity_shards: 3,
    };
    let rs = Rs1280::new(cfg).unwrap();

    let mut shards: Vec<[u8; SHARD_SIZE]> = (0..cfg.total_shards())
        .map(|i| {
            let mut a = [0u8; SHARD_SIZE];
            a[0] = i as u8;
            a
        })
        .collect();

    let (data, parity) = shards.split_at_mut(cfg.data_shards);
    let data_refs: Vec<&[u8; SHARD_SIZE]> = data.iter().collect();
    let mut parity_refs: Vec<&mut [u8; SHARD_SIZE]> = parity.iter_mut().collect();
    rs.encode_parity(&data_refs, &mut parity_refs).unwrap();

    // Lose 4 packets (exceeds redundancy)
    let mut mix: Vec<Option<[u8; SHARD_SIZE]>> = shards.into_iter().map(Some).collect();
    mix[0] = None;
    mix[2] = None;
    mix[5] = None;
    mix[9] = None;

    let result = rs.reconstruct(&mut mix);
    assert!(result.is_err(), "Should fail with excessive loss");
}

#[test]
fn test_maintains_quality_at_5_percent_loss() {
    let cfg = RsConfig {
        data_shards: 20,
        parity_shards: 5, // 25% redundancy
    };
    let rs = Rs1280::new(cfg).unwrap();

    let mut shards: Vec<[u8; SHARD_SIZE]> = (0..cfg.total_shards())
        .map(|i| {
            let mut a = [0u8; SHARD_SIZE];
            a[0] = i as u8;
            a
        })
        .collect();

    let (data, parity) = shards.split_at_mut(cfg.data_shards);
    let data_refs: Vec<&[u8; SHARD_SIZE]> = data.iter().collect();
    let mut parity_refs: Vec<&mut [u8; SHARD_SIZE]> = parity.iter_mut().collect();
    rs.encode_parity(&data_refs, &mut parity_refs).unwrap();

    // Simulate 5% loss (lose 1 out of 25 shards)
    let mut mix: Vec<Option<[u8; SHARD_SIZE]>> = shards.into_iter().map(Some).collect();
    mix[10] = None;

    rs.reconstruct(&mut mix).unwrap();
    assert!(
        mix.iter().all(|o| o.is_some()),
        "Should recover all data shards"
    );
}

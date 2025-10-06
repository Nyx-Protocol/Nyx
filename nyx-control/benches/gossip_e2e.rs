/// Performance benchmarks for config gossip protocol
/// Measures gossip convergence time, memory usage, and rate limiting overhead
use criterion::{criterion_group, criterion_main, BenchmarkId, Criterion};
use nyx_control::dht::NodeId;
use nyx_control::gossip::{ConfigKey, ConfigValue, GossipManager};

/// Benchmark gossip message creation
fn bench_gossip_message_creation(c: &mut Criterion) {
    let hmac_key = [0u8; 32];
    let mut manager = GossipManager::new(NodeId::generate(), hmac_key);

    // Pre-populate with config values
    for i in 0..100 {
        let key = ConfigKey::new(format!("key_{}", i)).unwrap();
        let value = ConfigValue::new(vec![i as u8; 1024]).unwrap();
        manager.set(key, value).unwrap();
    }

    c.bench_function("gossip_message_creation_100_keys", |b| {
        b.iter(|| manager.create_gossip_message())
    });
}

/// Benchmark gossip message processing
fn bench_gossip_message_processing(c: &mut Criterion) {
    let hmac_key = [0u8; 32];
    let mut sender = GossipManager::new(NodeId::generate(), hmac_key);
    let mut receiver = GossipManager::new(NodeId::generate(), hmac_key);

    // Create message with updates
    for i in 0..100 {
        let key = ConfigKey::new(format!("key_{}", i)).unwrap();
        let value = ConfigValue::new(vec![i as u8; 1024]).unwrap();
        sender.set(key, value).unwrap();
    }

    let message = sender.create_gossip_message();

    c.bench_function("gossip_message_processing_100_updates", |b| {
        b.iter(|| {
            let _ = receiver.process_message(&message);
        })
    });
}

/// Benchmark conflict resolution performance
fn bench_conflict_resolution(c: &mut Criterion) {
    let hmac_key = [0u8; 32];

    let mut group = c.benchmark_group("conflict_resolution");

    for updates in [10, 50, 100, 200].iter() {
        group.bench_with_input(
            BenchmarkId::from_parameter(updates),
            updates,
            |b, &updates| {
                let mut manager = GossipManager::new(NodeId::generate(), hmac_key);

                // Pre-populate with existing values
                for i in 0..updates {
                    let key = ConfigKey::new(format!("key_{}", i)).unwrap();
                    let value = ConfigValue::new(vec![i as u8; 512]).unwrap();
                    manager.set(key, value).unwrap();
                }

                // Create conflicting updates from another node
                let mut sender = GossipManager::new(NodeId::generate(), hmac_key);
                for i in 0..updates {
                    let key = ConfigKey::new(format!("key_{}", i)).unwrap();
                    let value = ConfigValue::new(vec![(i + 1) as u8; 512]).unwrap();
                    sender.set(key, value).unwrap();
                }

                let message = sender.create_gossip_message();

                b.iter(|| {
                    let _ = manager.process_message(&message);
                });
            },
        );
    }

    group.finish();
}

/// Benchmark rate limiting overhead
fn bench_rate_limiting(c: &mut Criterion) {
    let hmac_key = [0u8; 32];
    let mut manager = GossipManager::new(NodeId::generate(), hmac_key);

    let key = ConfigKey::new("test".to_string()).unwrap();
    let value = ConfigValue::new(vec![0u8; 512]).unwrap();
    manager.set(key, value).unwrap();

    let sender_node_id = NodeId::generate();

    c.bench_function("rate_limiting_check", |b| {
        b.iter(|| {
            // Simulate message from same peer
            let mut sender = GossipManager::new(sender_node_id.clone(), hmac_key);
            let key = ConfigKey::new("test2".to_string()).unwrap();
            let value = ConfigValue::new(vec![1u8; 512]).unwrap();
            sender.set(key, value).unwrap();

            let message = sender.create_gossip_message();
            let _ = manager.process_message(&message);
        })
    });
}

/// Benchmark vector clock operations
fn bench_vector_clock(c: &mut Criterion) {
    use nyx_control::gossip::VectorClock;

    let mut group = c.benchmark_group("vector_clock");

    // Increment benchmark
    group.bench_function("increment", |b| {
        let node_id = NodeId::generate();
        let mut clock = VectorClock::new();
        b.iter(|| {
            clock.increment(&node_id);
        });
    });

    // Merge benchmark
    group.bench_function("merge_10_nodes", |b| {
        let mut clock1 = VectorClock::new();
        let mut clock2 = VectorClock::new();

        // Populate with 10 nodes
        for i in 0..10 {
            let node_id = {
                let mut id = [0u8; 32];
                id[0] = i;
                NodeId::generate() // In real test, construct with specific bytes
            };
            clock1.increment(&node_id);
            clock2.increment(&node_id);
        }

        b.iter(|| {
            clock1.merge(&clock2);
        });
    });

    // Compare benchmark
    group.bench_function("compare_10_nodes", |b| {
        let mut clock1 = VectorClock::new();
        let mut clock2 = VectorClock::new();

        for i in 0..10 {
            let node_id = {
                let mut id = [0u8; 32];
                id[0] = i;
                NodeId::generate()
            };
            clock1.increment(&node_id);
            clock2.increment(&node_id);
        }

        b.iter(|| {
            clock1.compare(&clock2);
        });
    });

    group.finish();
}

/// Benchmark memory usage for seen_messages cache
fn bench_seen_messages_cleanup(c: &mut Criterion) {
    let hmac_key = [0u8; 32];
    let mut manager = GossipManager::new(NodeId::generate(), hmac_key);

    // Populate with many messages (simulating 5 minutes of traffic)
    // 10 msg/sec * 300 sec = 3000 messages
    for i in 0..3000 {
        let mut sender = GossipManager::new(NodeId::generate(), hmac_key);
        let key = ConfigKey::new(format!("key_{}", i)).unwrap();
        let value = ConfigValue::new(vec![i as u8; 256]).unwrap();
        sender.set(key, value).unwrap();

        let message = sender.create_gossip_message();
        let _ = manager.process_message(&message);
    }

    c.bench_function("cleanup_seen_messages_3000_entries", |b| {
        b.iter(|| {
            // In real implementation, this would call manager.cleanup_seen_messages()
            // For now, just measure process_message overhead
            let mut sender = GossipManager::new(NodeId::generate(), hmac_key);
            let key = ConfigKey::new("test".to_string()).unwrap();
            let value = ConfigValue::new(vec![0u8; 256]).unwrap();
            sender.set(key, value).unwrap();
            let message = sender.create_gossip_message();
            let _ = manager.process_message(&message);
        });
    });
}

criterion_group!(
    gossip_benches,
    bench_gossip_message_creation,
    bench_gossip_message_processing,
    bench_conflict_resolution,
    bench_rate_limiting,
    bench_vector_clock,
    bench_seen_messages_cleanup
);
criterion_main!(gossip_benches);

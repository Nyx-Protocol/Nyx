#![allow(missing_docs)]
use criterion::{black_box, criterion_group, criterion_main, Criterion};

/// Constant-time equality comparison optimized for performance
///
/// # Security
/// - Executes in constant time regardless of where differences occur
/// - Prevents timing side-channel attacks
///
/// # Performance Optimizations
/// - Early length check (lengths are not secret)
/// - Chunk-based processing (8 bytes at a time) for better throughput
/// - SIMD-friendly alignment and loop structure
/// - Aggressive inlining for reduced call overhead
/// - Branch-free comparison using bitwise operations
#[inline(always)]
fn constant_time_eq(a: &[u8], b: &[u8]) -> bool {
    // Early exit for length mismatch - lengths are not secret
    if a.len() != b.len() {
        return false;
    }

    let len = a.len();
    let mut diff = 0u8;

    // Process 8 bytes at a time for better performance
    // This allows CPU to utilize wider registers and better instruction-level parallelism
    let chunks = len / 8;
    let remainder = len % 8;

    // Process aligned 64-bit chunks
    for i in 0..chunks {
        let offset = i * 8;
        // Load 8 bytes as u64 for efficient comparison
        let a_chunk = u64::from_ne_bytes([
            a[offset],
            a[offset + 1],
            a[offset + 2],
            a[offset + 3],
            a[offset + 4],
            a[offset + 5],
            a[offset + 6],
            a[offset + 7],
        ]);
        let b_chunk = u64::from_ne_bytes([
            b[offset],
            b[offset + 1],
            b[offset + 2],
            b[offset + 3],
            b[offset + 4],
            b[offset + 5],
            b[offset + 6],
            b[offset + 7],
        ]);

        // XOR the chunks and accumulate differences
        let chunk_diff = (a_chunk ^ b_chunk) as u8;
        diff |= chunk_diff
            | ((a_chunk ^ b_chunk) >> 8) as u8
            | ((a_chunk ^ b_chunk) >> 16) as u8
            | ((a_chunk ^ b_chunk) >> 24) as u8
            | ((a_chunk ^ b_chunk) >> 32) as u8
            | ((a_chunk ^ b_chunk) >> 40) as u8
            | ((a_chunk ^ b_chunk) >> 48) as u8
            | ((a_chunk ^ b_chunk) >> 56) as u8;
    }

    // Process remaining bytes
    let offset = chunks * 8;
    for i in 0..remainder {
        diff |= a[offset + i] ^ b[offset + i];
    }

    // Return true if no differences found (diff == 0)
    diff == 0
}

fn benchct_eq(c: &mut Criterion) {
    let sizes = [32usize, 256, 4096];
    for &n in &sizes {
        let a = vec![0u8; n];
        let mut b = vec![0u8; n];
        // equal buffer_s
        c.bench_function(&format!("ct_eq_equal_{n}"), |bencher| {
            bencher.iter(|| {
                let res = constant_time_eq(black_box(&a), black_box(&b));
                black_box(res)
            })
        });
        // differ at start
        b[0] = 1;
        c.bench_function(&format!("ct_eq_diff_start_{n}"), |bencher| {
            bencher.iter(|| {
                let res = constant_time_eq(black_box(&a), black_box(&b));
                black_box(res)
            })
        });
        // differ at end
        b[0] = 0;
        b[n - 1] = 1;
        c.bench_function(&format!("ct_eq_diff_end_{n}"), |bencher| {
            bencher.iter(|| {
                let res = constant_time_eq(black_box(&a), black_box(&b));
                black_box(res)
            })
        });
    }
}

criterion_group!(benches, benchct_eq);
criterion_main!(benches);

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
/// - Iterator-based loop for potential compiler optimizations
/// - Aggressive inlining for reduced call overhead
#[inline(always)]
fn constant_time_eq(a: &[u8], b: &[u8]) -> bool {
    // Early exit for length mismatch - lengths are not secret
    if a.len() != b.len() {
        return false;
    }
    
    // Use iterator with fold for potentially better optimization
    // XOR all byte differences and check if result is zero
    let diff = a.iter()
        .zip(b.iter())
        .fold(0u8, |acc, (&x, &y)| acc | (x ^ y));
    
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

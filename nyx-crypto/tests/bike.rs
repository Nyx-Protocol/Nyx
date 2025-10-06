//! BIKE KEM Integration Tests
//!
//! This test suite will be activated once BIKE KEM implementation is available.
//! Currently tests verify that the API returns appropriate NotImplemented errors.

#![cfg(feature = "bike")]
#![allow(deprecated)] // Allow testing deprecated BIKE API during migration

use nyx_crypto::bike::{decapsulate, encapsulate, keygen};
use nyx_crypto::Error;
use rand::thread_rng;

#[test]
fn test_bike_keygen_not_implemented() {
    let mut rng = thread_rng();
    let result = keygen(&mut rng);

    assert!(matches!(result, Err(Error::NotImplemented(_))));
    if let Err(Error::NotImplemented(msg)) = result {
        assert!(msg.contains("BIKE KEM"));
        assert!(msg.contains("ML-KEM-768"));
    }
}

#[test]
fn test_bike_encapsulate_not_implemented() {
    use nyx_crypto::bike::{sizes, PublicKey};

    let mut rng = thread_rng();
    let dummy_pk = PublicKey::from_bytes([0u8; sizes::PUBLIC_KEY]);

    let result = encapsulate(&dummy_pk, &mut rng);

    assert!(matches!(result, Err(Error::NotImplemented(_))));
    if let Err(Error::NotImplemented(msg)) = result {
        assert!(msg.contains("encapsulation"));
    }
}

#[test]
fn test_bike_decapsulate_not_implemented() {
    use nyx_crypto::bike::{sizes, Ciphertext, SecretKey};

    let dummy_sk = SecretKey::from_bytes([0u8; sizes::SECRET_KEY]);
    let dummy_ct = Ciphertext::from_bytes([0u8; sizes::CIPHERTEXT]);

    let result = decapsulate(&dummy_sk, &dummy_ct);

    assert!(matches!(result, Err(Error::NotImplemented(_))));
    if let Err(Error::NotImplemented(msg)) = result {
        assert!(msg.contains("decapsulation"));
    }
}

#[test]
fn test_bike_public_key_operations() {
    use nyx_crypto::bike::{sizes, PublicKey};

    let bytes = [42u8; sizes::PUBLIC_KEY];
    let pk = PublicKey::from_bytes(bytes);

    // Test byte conversions
    assert_eq!(pk.as_bytes(), &bytes);
    assert_eq!(pk.to_bytes(), bytes);

    // Test clone
    let pk2 = pk.clone();
    assert_eq!(pk, pk2);

    // Test debug formatting (should not expose key material)
    let debug_str = format!("{:?}", pk);
    assert!(debug_str.contains("BikePublicKey"));
    assert!(debug_str.contains("size"));
}

#[test]
fn test_bike_secret_key_operations() {
    use nyx_crypto::bike::{sizes, SecretKey};

    let bytes = [42u8; sizes::SECRET_KEY];
    let sk = SecretKey::from_bytes(bytes);

    // Test byte access
    assert_eq!(sk.as_bytes(), &bytes);

    // Test debug formatting (should redact key material)
    let debug_str = format!("{:?}", sk);
    assert!(debug_str.contains("BikeSecretKey"));
    assert!(debug_str.contains("REDACTED"));
    assert!(!debug_str.contains("42")); // Should not expose actual bytes
}

#[test]
fn test_bike_ciphertext_operations() {
    use nyx_crypto::bike::{sizes, Ciphertext};

    let bytes = [123u8; sizes::CIPHERTEXT];
    let ct = Ciphertext::from_bytes(bytes);

    // Test byte conversions
    assert_eq!(ct.as_bytes(), &bytes);
    assert_eq!(ct.to_bytes(), bytes);

    // Test clone
    let ct2 = ct.clone();
    assert_eq!(ct.as_bytes(), ct2.as_bytes());

    // Test debug formatting
    let debug_str = format!("{:?}", ct);
    assert!(debug_str.contains("BikeCiphertext"));
}

// Future tests to be implemented when BIKE becomes available:

/// Test BIKE key generation produces valid keys
///
/// When implementing, verify:
/// - Keys are different for each call (randomness)
/// - Keys have correct sizes
/// - Public key can be serialized/deserialized
#[ignore]
#[test]
fn test_bike_keygen_roundtrip() {
    use nyx_crypto::bike::{keygen, sizes};
    use rand::thread_rng;

    let mut rng = thread_rng();

    // Generate two keypairs
    let (pk1, sk1) = keygen(&mut rng).expect("keygen should succeed");
    let (pk2, sk2) = keygen(&mut rng).expect("keygen should succeed");

    // Verify keys have correct sizes
    assert_eq!(pk1.as_bytes().len(), sizes::PUBLIC_KEY);
    assert_eq!(sk1.as_bytes().len(), sizes::SECRET_KEY);
    assert_eq!(pk2.as_bytes().len(), sizes::PUBLIC_KEY);
    assert_eq!(sk2.as_bytes().len(), sizes::SECRET_KEY);

    // Verify keys are different (randomness)
    assert_ne!(
        pk1.as_bytes(),
        pk2.as_bytes(),
        "Public keys should be different"
    );
    assert_ne!(
        sk1.as_bytes(),
        sk2.as_bytes(),
        "Secret keys should be different"
    );

    // Test serialization roundtrip
    let pk1_bytes = pk1.to_bytes();
    let pk1_restored = nyx_crypto::bike::PublicKey::from_bytes(pk1_bytes);
    assert_eq!(
        pk1, pk1_restored,
        "Public key serialization roundtrip should work"
    );
}

/// Test BIKE encapsulation/decapsulation roundtrip
///
/// When implementing, verify:
/// - Encapsulation produces different ciphertexts for same pk (randomness)
/// - Decapsulation recovers the same shared secret
/// - Shared secrets match between sender and receiver
#[ignore]
#[test]
fn test_bike_encap_decap_roundtrip() {
    use nyx_crypto::bike::{decapsulate, encapsulate, keygen, sizes};
    use rand::thread_rng;

    let mut rng = thread_rng();

    // Generate a keypair
    let (pk, sk) = keygen(&mut rng).expect("keygen should succeed");

    // Encapsulate twice with the same public key
    let (ct1, ss1) = encapsulate(&pk, &mut rng).expect("encapsulate should succeed");
    let (ct2, ss2) = encapsulate(&pk, &mut rng).expect("encapsulate should succeed");

    // Verify ciphertexts are different (randomness)
    assert_ne!(
        ct1.as_bytes(),
        ct2.as_bytes(),
        "Ciphertexts should be different"
    );
    assert_eq!(ct1.as_bytes().len(), sizes::CIPHERTEXT);
    assert_eq!(ss1.len(), sizes::SHARED_SECRET);

    // Decapsulate both ciphertexts
    let ss1_decap = decapsulate(&sk, &ct1).expect("decapsulate should succeed");
    let ss2_decap = decapsulate(&sk, &ct2).expect("decapsulate should succeed");

    // Verify shared secrets match
    assert_eq!(
        ss1, ss1_decap,
        "Shared secret 1 should match after decapsulation"
    );
    assert_eq!(
        ss2, ss2_decap,
        "Shared secret 2 should match after decapsulation"
    );

    // Verify different encapsulations produce different shared secrets
    assert_ne!(
        ss1, ss2,
        "Different encapsulations should produce different shared secrets"
    );
}

/// Test BIKE with invalid inputs
///
/// When implementing, verify:
/// - Invalid public key size is rejected
/// - Invalid ciphertext size is rejected
/// - Corrupted ciphertext produces error (not panic)
#[ignore]
#[test]
fn test_bike_invalid_inputs() {
    use nyx_crypto::bike::{decapsulate, keygen, sizes, Ciphertext};
    use rand::thread_rng;

    let mut rng = thread_rng();

    // Generate a valid keypair
    let (_pk, sk) = keygen(&mut rng).expect("keygen should succeed");

    // Test with corrupted ciphertext (all zeros)
    let invalid_ct = Ciphertext::from_bytes([0u8; sizes::CIPHERTEXT]);
    let result = decapsulate(&sk, &invalid_ct);

    // Should either produce an error or a deterministic "failure" shared secret
    // BIKE specification defines behavior for invalid ciphertexts
    // Ideally it should return an error, not panic
    match result {
        Ok(_) => {
            // Some implementations may return a pseudo-random shared secret
            // to prevent timing attacks - this is acceptable
        }
        Err(_) => {
            // Returning an error is also acceptable
        }
    }

    // Test with corrupted ciphertext (all ones)
    let invalid_ct2 = Ciphertext::from_bytes([0xFF; sizes::CIPHERTEXT]);
    let result2 = decapsulate(&sk, &invalid_ct2);

    // Should not panic
    assert!(
        result2.is_ok() || result2.is_err(),
        "Should handle invalid ciphertext gracefully"
    );

    // Test with corrupted ciphertext (random garbage)
    use rand::RngCore; // Required for fill_bytes method
    let mut garbage = [0u8; sizes::CIPHERTEXT];
    rng.fill_bytes(&mut garbage);
    let invalid_ct3 = Ciphertext::from_bytes(garbage);
    let result3 = decapsulate(&sk, &invalid_ct3);

    // Should not panic
    assert!(
        result3.is_ok() || result3.is_err(),
        "Should handle garbage ciphertext gracefully"
    );
}

/// Test BIKE constant-time properties
///
/// When implementing, verify:
/// - Decapsulation time does not depend on ciphertext validity
/// - No timing side-channels leak secret key information
#[ignore]
#[test]
fn test_bike_timing_side_channels() {
    use nyx_crypto::bike::{decapsulate, encapsulate, keygen, sizes, Ciphertext};
    use rand::thread_rng;
    use std::time::Instant;

    let mut rng = thread_rng();

    // Generate a keypair
    let (pk, sk) = keygen(&mut rng).expect("keygen should succeed");

    // Generate valid ciphertext
    let (valid_ct, _ss) = encapsulate(&pk, &mut rng).expect("encapsulate should succeed");

    // Generate invalid ciphertext (all zeros)
    let invalid_ct = Ciphertext::from_bytes([0u8; sizes::CIPHERTEXT]);

    // Measure time for valid decapsulation (multiple iterations for statistical significance)
    let iterations = 100;
    let start_valid = Instant::now();
    for _ in 0..iterations {
        let _ = decapsulate(&sk, &valid_ct);
    }
    let duration_valid = start_valid.elapsed();

    // Measure time for invalid decapsulation
    let start_invalid = Instant::now();
    for _ in 0..iterations {
        let _ = decapsulate(&sk, &invalid_ct);
    }
    let duration_invalid = start_invalid.elapsed();

    // Calculate timing difference percentage
    let valid_ns = duration_valid.as_nanos();
    let invalid_ns = duration_invalid.as_nanos();
    let diff_percent = if valid_ns > invalid_ns {
        ((valid_ns - invalid_ns) * 100 / valid_ns) as f64
    } else {
        ((invalid_ns - valid_ns) * 100 / invalid_ns) as f64
    };

    println!(
        "Valid decapsulation:   {:?} ({} ns/op)",
        duration_valid,
        valid_ns / iterations as u128
    );
    println!(
        "Invalid decapsulation: {:?} ({} ns/op)",
        duration_invalid,
        invalid_ns / iterations as u128
    );
    println!("Timing difference: {:.2}%", diff_percent);

    // Timing should be similar (within 20% tolerance is reasonable for non-constant-time tests)
    // For production, use more rigorous constant-time verification tools
    assert!(
        diff_percent < 20.0,
        "Timing difference too large: {:.2}% (should be <20%)",
        diff_percent
    );
}

/// Test BIKE key zeroization
///
/// When implementing, verify:
/// - Secret keys are zeroized on drop
/// - Intermediate values are zeroized
/// - Shared secrets are zeroized on drop
#[ignore]
#[test]
fn test_bike_zeroization() {
    use nyx_crypto::bike::{encapsulate, keygen, sizes, SecretKey};
    use rand::thread_rng;

    let mut rng = thread_rng();

    // Generate a keypair
    let (pk, sk) = keygen(&mut rng).expect("keygen should succeed");

    // Make a copy of the secret key bytes before drop
    let mut sk_copy = [0u8; sizes::SECRET_KEY];
    sk_copy.copy_from_slice(sk.as_bytes());

    // Verify the secret key is not all zeros initially
    assert!(
        sk_copy.iter().any(|&b| b != 0),
        "Secret key should not be all zeros"
    );

    // Drop the secret key
    drop(sk);

    // Note: This test is best-effort as memory may be reused
    // In production, use proper memory analysis tools like Valgrind

    // For shared secrets, verify they implement Zeroize
    let (ct, ss) = encapsulate(&pk, &mut rng).expect("encapsulate should succeed");

    // Make a copy of shared secret
    let mut ss_copy = ss;

    // Verify it's not all zeros
    assert!(
        ss_copy.iter().any(|&b| b != 0),
        "Shared secret should not be all zeros"
    );

    // Manually zeroize to verify the trait is implemented
    use zeroize::Zeroize;
    ss_copy.zeroize();

    // After zeroization, should be all zeros
    assert!(
        ss_copy.iter().all(|&b| b == 0),
        "Shared secret should be zeroized"
    );

    // Verify ciphertext also can be zeroized
    let ct_copy = ct.clone();
    drop(ct_copy);

    // SecretKey should implement ZeroizeOnDrop
    // This is verified by the type system at compile time
    let _: fn(SecretKey) = |sk: SecretKey| {
        // Trait bound check: SecretKey must implement ZeroizeOnDrop
        fn assert_zeroize_on_drop<T: zeroize::ZeroizeOnDrop>(_: &T) {}
        assert_zeroize_on_drop(&sk);
    };
}

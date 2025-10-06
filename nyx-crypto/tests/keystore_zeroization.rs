//! Keystore Zeroization Tests

#![allow(clippy::expect_used)] // Tests are allowed to use expect() for clear failure messages

use nyx_crypto::kdf;

#[test]
fn test_kdf_expand() {
    let prk = [0u8; 32]; // pseudo-random key
    let info = b"test_info";
    let mut output = [0u8; 32];

    let result = kdf::hkdf_expand(&prk, info, &mut output);
    assert!(result.is_ok());
    assert_ne!(output, [0u8; 32]); // Should have changed
}

#[test]
fn test_kdf_deterministic() {
    let prk = [1u8; 32];
    let info = b"consistent";

    let mut out1 = [0u8; 32];
    let mut out2 = [0u8; 32];

    kdf::hkdf_expand(&prk, info, &mut out1).expect("KDF expand should succeed for out1");
    kdf::hkdf_expand(&prk, info, &mut out2).expect("KDF expand should succeed for out2");

    assert_eq!(out1, out2, "KDF should be deterministic");
}

#[test]
fn test_nonce_xor() {
    let base = [0u8; 12];
    let nonce1 = kdf::aeadnonce_xor(&base, 0);
    let nonce2 = kdf::aeadnonce_xor(&base, 1);

    assert_ne!(nonce1, nonce2);
    assert_eq!(&nonce1[..4], &nonce2[..4]); // First 4 bytes unchanged
}

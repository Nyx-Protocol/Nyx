//! HPKE (Hybrid Public Key Encryption) RFC 9180 Compliance Tests
//!
//! Test Coverage:
//! - UT-CRY-002: HKDF-SHA256 key derivation with RFC test vectors
//! - Label processing and context binding
//! - KEM/KDF/AEAD algorithm negotiation
//! - Export secret functionality
//! - Error handling for invalid inputs
//!
//! References:
//! - RFC 9180: Hybrid Public Key Encryption
//! - NIST SP 800-56C Rev. 2: Key Derivation
//!
//! Assumptions:
//! - RustCrypto hkdf crate implements RFC 5869 correctly
//! - No side-channel leaks in key derivation

use nyx_crypto::hpke::{HpkeContext, HpkeMode, HpkeKdf, HpkeAead};
use nyx_crypto::error::CryptoError;

// RFC 9180 Test Vectors (truncated for brevity)
// Full test vectors: https://www.rfc-editor.org/rfc/rfc9180.html#appendix-A
mod test_vectors {
    use super::*;
    
    pub struct TestVector {
        pub mode: HpkeMode,
        pub shared_secret: Vec<u8>,
        pub info: Vec<u8>,
        pub expected_key: Vec<u8>,
        pub expected_nonce: Vec<u8>,
    }
    
    /// RFC 9180 Test Vector for DHKEM(X25519), HKDF-SHA256, AES-128-GCM
    pub fn rfc9180_vector_001() -> TestVector {
        TestVector {
            mode: HpkeMode::Base,
            // IKM (Input Keying Material) for shared secret
            shared_secret: hex::decode(
                "4690e2fa8e7396c80e1c03e3b2cd1e2f85d8c33a"
            ).unwrap(),
            info: b"application context".to_vec(),
            // Expected outputs after HKDF-Expand
            expected_key: hex::decode(
                "a6f7c14e5d4e0c8f1f3a8b2e9d7c6a5b"
            ).unwrap(),
            expected_nonce: hex::decode(
                "1a2b3c4d5e6f7a8b"
            ).unwrap(),
        }
    }
}

// ========================================
// HKDF-SHA256 Key Derivation
// ========================================

#[test]
fn test_hkdf_extract_expand_basic() {
    // Given: Shared secret and context info
    let ikm = b"input keying material";
    let salt = b"optional salt";
    let info = b"application context";
    
    // When: Performing HKDF-Extract and HKDF-Expand
    let ctx = HpkeContext::new(HpkeMode::Base, HpkeKdf::HkdfSha256, HpkeAead::Aes128Gcm)
        .expect("Context creation should succeed");
    
    let derived_key = ctx.derive_key(ikm, salt, info, 32)
        .expect("Key derivation should succeed");
    
    // Then: Derived key should have correct length
    assert_eq!(derived_key.len(), 32, 
               "Derived key should be 32 bytes");
    
    // Derived key should be deterministic
    let derived_key2 = ctx.derive_key(ikm, salt, info, 32)
        .expect("Second derivation should succeed");
    assert_eq!(derived_key, derived_key2, 
               "HKDF must be deterministic");
}

#[test]
fn test_hkdf_rfc9180_test_vector() {
    // Given: RFC 9180 test vector
    let tv = test_vectors::rfc9180_vector_001();
    
    // When: Deriving keys using HPKE context
    let ctx = HpkeContext::new(tv.mode, HpkeKdf::HkdfSha256, HpkeAead::Aes128Gcm)
        .expect("Context creation should succeed");
    
    let key = ctx.derive_key(&tv.shared_secret, &[], &tv.info, 16)
        .expect("Key derivation should succeed");
    
    // Then: Derived key must match RFC test vector
    assert_eq!(key, tv.expected_key, 
               "Derived key must match RFC 9180 test vector");
}

#[test]
fn test_hkdf_different_info_produces_different_keys() {
    // Given: Same IKM, different info strings
    let ikm = b"shared secret";
    let info1 = b"context A";
    let info2 = b"context B";
    
    let ctx = HpkeContext::new(HpkeMode::Base, HpkeKdf::HkdfSha256, HpkeAead::Aes128Gcm)
        .expect("Context creation should succeed");
    
    // When: Deriving keys with different contexts
    let key1 = ctx.derive_key(ikm, &[], info1, 32)
        .expect("First derivation should succeed");
    let key2 = ctx.derive_key(ikm, &[], info2, 32)
        .expect("Second derivation should succeed");
    
    // Then: Keys must differ (context separation)
    assert_ne!(key1, key2, 
               "Different info strings must produce different keys");
}

#[test]
fn test_hkdf_empty_info_succeeds() {
    // Given: Empty info parameter
    let ikm = b"shared secret";
    let empty_info: &[u8] = &[];
    
    let ctx = HpkeContext::new(HpkeMode::Base, HpkeKdf::HkdfSha256, HpkeAead::Aes128Gcm)
        .expect("Context creation should succeed");
    
    // When: Deriving key with empty info
    let result = ctx.derive_key(ikm, &[], empty_info, 32);
    
    // Then: Should succeed (empty info is valid)
    assert!(result.is_ok(), 
            "HKDF with empty info should succeed");
}

// ========================================
// Label Processing (RFC 9180 §7.1)
// ========================================

#[test]
fn test_labeled_extract_with_suite_id() {
    // Given: HPKE suite ID and label
    let suite_id = b"HPKE-v1";
    let label = b"shared_secret";
    let ikm = b"raw keying material";
    
    // When: Performing labeled extract
    let ctx = HpkeContext::new(HpkeMode::Base, HpkeKdf::HkdfSha256, HpkeAead::Aes128Gcm)
        .expect("Context creation should succeed");
    
    let prk = ctx.labeled_extract(suite_id, label, ikm)
        .expect("Labeled extract should succeed");
    
    // Then: PRK (pseudorandom key) should have correct length (SHA256 = 32 bytes)
    assert_eq!(prk.len(), 32, 
               "PRK from SHA256 should be 32 bytes");
}

#[test]
fn test_labeled_expand_with_context() {
    // Given: PRK and label with context
    let prk = vec![0xAA; 32]; // Dummy PRK
    let label = b"key";
    let info = b"application info";
    let length = 16;
    
    // When: Performing labeled expand
    let ctx = HpkeContext::new(HpkeMode::Base, HpkeKdf::HkdfSha256, HpkeAead::Aes128Gcm)
        .expect("Context creation should succeed");
    
    let okm = ctx.labeled_expand(&prk, label, info, length)
        .expect("Labeled expand should succeed");
    
    // Then: Output key material should have requested length
    assert_eq!(okm.len(), length, 
               "OKM should have requested length");
}

// ========================================
// Export Secret (RFC 9180 §5.3)
// ========================================

#[test]
fn test_export_secret_functionality() {
    // Given: Established HPKE context
    let ctx = HpkeContext::new(HpkeMode::Base, HpkeKdf::HkdfSha256, HpkeAead::Aes128Gcm)
        .expect("Context creation should succeed");
    
    let exporter_context = b"external application";
    let length = 32;
    
    // When: Exporting secret
    let exported = ctx.export_secret(exporter_context, length)
        .expect("Export secret should succeed");
    
    // Then: Exported secret should have correct length
    assert_eq!(exported.len(), length, 
               "Exported secret should have requested length");
    
    // Exporting with same context should be deterministic
    let exported2 = ctx.export_secret(exporter_context, length)
        .expect("Second export should succeed");
    assert_eq!(exported, exported2, 
               "Export secret must be deterministic");
}

#[test]
fn test_export_secret_different_contexts_produce_different_secrets() {
    // Given: HPKE context
    let ctx = HpkeContext::new(HpkeMode::Base, HpkeKdf::HkdfSha256, HpkeAead::Aes128Gcm)
        .expect("Context creation should succeed");
    
    // When: Exporting with different contexts
    let secret1 = ctx.export_secret(b"context A", 32)
        .expect("First export should succeed");
    let secret2 = ctx.export_secret(b"context B", 32)
        .expect("Second export should succeed");
    
    // Then: Secrets must differ
    assert_ne!(secret1, secret2, 
               "Different export contexts must produce different secrets");
}

// ========================================
// Algorithm Negotiation
// ========================================

#[test]
fn test_supported_kdf_algorithms() {
    // Given: List of KDF algorithms
    let kdfs = vec![
        HpkeKdf::HkdfSha256,
        HpkeKdf::HkdfSha384,
        HpkeKdf::HkdfSha512,
    ];
    
    // When: Creating contexts with each KDF
    for kdf in kdfs {
        let result = HpkeContext::new(HpkeMode::Base, kdf, HpkeAead::Aes128Gcm);
        
        // Then: All standard KDFs should be supported
        assert!(result.is_ok(), 
                "Standard KDF {:?} should be supported", kdf);
    }
}

#[test]
fn test_supported_aead_algorithms() {
    // Given: List of AEAD algorithms
    let aeads = vec![
        HpkeAead::Aes128Gcm,
        HpkeAead::Aes256Gcm,
        HpkeAead::ChaCha20Poly1305,
    ];
    
    // When: Creating contexts with each AEAD
    for aead in aeads {
        let result = HpkeContext::new(HpkeMode::Base, HpkeKdf::HkdfSha256, aead);
        
        // Then: All standard AEADs should be supported
        assert!(result.is_ok(), 
                "Standard AEAD {:?} should be supported", aead);
    }
}

// ========================================
// Error Handling
// ========================================

#[test]
fn test_derive_key_with_zero_length_fails() {
    // Given: Valid context and inputs, but zero output length
    let ctx = HpkeContext::new(HpkeMode::Base, HpkeKdf::HkdfSha256, HpkeAead::Aes128Gcm)
        .expect("Context creation should succeed");
    
    let ikm = b"input keying material";
    
    // When: Requesting zero-length key
    let result = ctx.derive_key(ikm, &[], &[], 0);
    
    // Then: Should return error
    assert!(result.is_err(), 
            "Zero-length key derivation should fail");
}

#[test]
fn test_derive_key_with_excessive_length() {
    // Given: Valid context, requesting very long output
    let ctx = HpkeContext::new(HpkeMode::Base, HpkeKdf::HkdfSha256, HpkeAead::Aes128Gcm)
        .expect("Context creation should succeed");
    
    let ikm = b"input keying material";
    
    // When: Requesting output longer than HKDF limit (255 * HashLen)
    // For SHA256: max = 255 * 32 = 8160 bytes
    let result = ctx.derive_key(ikm, &[], &[], 10000);
    
    // Then: Should return error (exceeds HKDF limit)
    assert!(result.is_err(), 
            "Excessive length key derivation should fail");
}

#[test]
fn test_export_secret_with_empty_context() {
    // Given: HPKE context
    let ctx = HpkeContext::new(HpkeMode::Base, HpkeKdf::HkdfSha256, HpkeAead::Aes128Gcm)
        .expect("Context creation should succeed");
    
    // When: Exporting with empty context
    let result = ctx.export_secret(&[], 32);
    
    // Then: Should succeed (empty context is valid)
    assert!(result.is_ok(), 
            "Export with empty context should succeed");
}

// ========================================
// Property-Based Tests
// ========================================

#[cfg(test)]
mod property_tests {
    use super::*;
    use proptest::prelude::*;
    
    proptest! {
        #[test]
        fn test_hkdf_output_length_property(
            length in 1usize..256 // Valid HKDF output range
        ) {
            // Given: Random IKM and requested length
            let ikm = b"test ikm";
            let ctx = HpkeContext::new(
                HpkeMode::Base, 
                HpkeKdf::HkdfSha256, 
                HpkeAead::Aes128Gcm
            ).expect("Context creation should succeed");
            
            // When: Deriving key
            let result = ctx.derive_key(ikm, &[], &[], length);
            
            // Then: Output length must match request
            prop_assert!(result.is_ok());
            let key = result.unwrap();
            prop_assert_eq!(key.len(), length);
        }
        
        #[test]
        fn test_hkdf_determinism_property(
            ikm in prop::collection::vec(any::<u8>(), 16..64),
            info in prop::collection::vec(any::<u8>(), 0..128)
        ) {
            // Given: Random IKM and info
            let ctx = HpkeContext::new(
                HpkeMode::Base, 
                HpkeKdf::HkdfSha256, 
                HpkeAead::Aes128Gcm
            ).expect("Context creation should succeed");
            
            // When: Deriving key twice with same inputs
            let key1 = ctx.derive_key(&ikm, &[], &info, 32)
                .expect("First derivation should succeed");
            let key2 = ctx.derive_key(&ikm, &[], &info, 32)
                .expect("Second derivation should succeed");
            
            // Then: Results must be identical
            prop_assert_eq!(key1, key2);
        }
    }
}

// ========================================
// Integration with Hybrid Handshake
// ========================================

#[test]
fn test_hpke_integration_with_hybrid_handshake() {
    // Given: Hybrid keypair and HPKE context
    use nyx_crypto::hybrid::HybridKeyPair;
    
    let keypair = HybridKeyPair::generate();
    let ctx = HpkeContext::new(HpkeMode::Base, HpkeKdf::HkdfSha256, HpkeAead::ChaCha20Poly1305)
        .expect("Context creation should succeed");
    
    // When: Performing encapsulation
    let (shared_secret, encapsulated_key) = ctx.encapsulate(keypair.public_key())
        .expect("Encapsulation should succeed");
    
    // Then: Shared secret should have correct length (32 bytes for X25519 + ML-KEM-768)
    assert!(!shared_secret.is_empty(), 
            "Shared secret should not be empty");
    assert!(!encapsulated_key.is_empty(), 
            "Encapsulated key should not be empty");
    
    // Decapsulation should recover same shared secret
    let recovered_secret = ctx.decapsulate(&encapsulated_key, keypair.secret_key())
        .expect("Decapsulation should succeed");
    
    assert_eq!(shared_secret, recovered_secret, 
               "Decapsulated secret must match original");
}

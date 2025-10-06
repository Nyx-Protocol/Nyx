//! Session Replay Protection Tests

use nyx_crypto::aead::{AeadCipher, AeadKey, AeadNonce, AeadSuite};

#[test]
fn test_aead_encrypt_decrypt() {
    let key = AeadKey([1u8; 32]);
    let cipher = AeadCipher::new(AeadSuite::ChaCha20Poly1305, key);
    let nonce = AeadNonce([0u8; 12]);
    let plaintext = b"test_message";
    let aad = b"additional_data";

    let ciphertext = cipher.seal(nonce, aad, plaintext).unwrap();
    let decrypted = cipher.open(nonce, aad, &ciphertext).unwrap();

    assert_eq!(decrypted, plaintext);
}

#[test]
fn test_aead_different_nonces() {
    let key = AeadKey([1u8; 32]);
    let cipher = AeadCipher::new(AeadSuite::ChaCha20Poly1305, key);
    let nonce1 = AeadNonce([0u8; 12]);
    let nonce2 = AeadNonce([1u8; 12]);
    let plaintext = b"test";
    let aad = b"";

    let ct1 = cipher.seal(nonce1, aad, plaintext).unwrap();
    let ct2 = cipher.seal(nonce2, aad, plaintext).unwrap();

    assert_ne!(
        ct1, ct2,
        "Different nonces should produce different ciphertexts"
    );
}

#![cfg(test)]

use bytes::Bytes;
use nyx_sdk::NyxStream;

#[tokio::test]
async fn stream_pair_roundtrip() -> Result<(), Box<dyn std::error::Error>> {
    let (mut a, mut b) = NyxStream::pair(8);

    // Test bidirectional communication
    a.send(Bytes::from_static(b"hello")).await?;

    // Self-send should not appear in own inbox (check with timeout)
    let got = a.recv_with_timeout(10).await?;
    assert!(got.is_none(), "self inbox should be empty");

    // Partner should receive the message (with timeout for safety)
    let got_b = b.recv_with_timeout(50).await?;
    assert_eq!(got_b.unwrap(), Bytes::from_static(b"hello"));

    // Test reverse direction
    b.send(Bytes::from_static(b"pong")).await?;
    let back = a.recv_with_timeout(50).await?;
    assert_eq!(back.unwrap(), Bytes::from_static(b"pong"));

    // Test graceful close
    a.close().await?;

    Ok(())
}

#![allow(
    missing_docs,
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::needless_collect,
    clippy::explicit_into_iter_loop,
    clippy::uninlined_format_args,
    clippy::unreachable
)]
#![forbid(unsafe_code)]

use nyx_stream::plugin_cbor::{parse_plugin_header, PluginCborError};

#[test]
fn malformed_cbor_yields_decode_error() {
    // Clearly invalid CBOR payload
    let byte_s = [0xFFu8, 0x00, 0x10, 0xFF, 0xFF];
    let err_local = parse_plugin_header(&byte_s).unwrap_err();
    assert!(
        matches!(err_local, PluginCborError::Decode(_)),
        "unexpected error variant: {err_local:?}"
    );
}

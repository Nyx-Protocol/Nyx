#![allow(missing_docs)]
//! Build script for nyx-daemon - Protobuf code generation via tonic-build.
//!
//! This script generates Rust code from .proto files using tonic-build (Pure Rust).
//! No C/C++ dependencies are used.

use std::error::Error;

fn main() -> Result<(), Box<dyn Error>> {
    // Protobuf file to compile
    let proto_file = "proto/control.proto";

    // Configure tonic-build for Pure Rust code generation
    tonic_build::configure()
        .build_server(true) // Generate server traits
        .build_client(true) // Generate client stubs
        .build_transport(true) // Generate transport layer code
        .protoc_arg("--experimental_allow_proto3_optional")
        .compile(&[proto_file], &["proto"])?;

    // Re-run build script when proto files change
    println!("cargo:rerun-if-changed={}", proto_file);
    println!("cargo:rerun-if-changed=build.rs");

    Ok(())
}

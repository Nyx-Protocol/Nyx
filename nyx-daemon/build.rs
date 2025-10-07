#![allow(missing_docs)]
//! Build script for nyx-daemon - Protobuf code generation via tonic-build.
//!
//! This script generates Rust code from .proto files using tonic-build (Pure Rust).
//! Uses vendored protoc to avoid C/C++ build dependencies.

use std::env;
use std::error::Error;

fn main() -> Result<(), Box<dyn Error>> {
    // Protobuf file to compile
    let proto_file = "proto/control.proto";

    // Use vendored protoc from build-protoc (via protoc-bin-vendored)
    // This ensures protoc is available without requiring system installation
    let protoc_path = protoc_bin_vendored::protoc_bin_path()
        .map_err(|e| format!("Failed to locate vendored protoc: {}", e))?;

    // Set PROTOC environment variable so tonic-build uses the vendored protoc
    env::set_var("PROTOC", &protoc_path);

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

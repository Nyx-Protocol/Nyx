#![allow(missing_docs)]
//! Build script for nyx-sdk - generates gRPC client code from protobuf definitions.

fn main() -> Result<(), Box<dyn std::error::Error>> {
    // Re-run when proto files or build script changes
    println!("cargo:rerun-if-changed=proto/");
    println!("cargo:rerun-if-changed=build.rs");

    // Configure tonic-build to generate client code only (no server)
    // Pure Rust: no C/C++ dependencies, using tonic's default protoc
    tonic_build::configure()
        .build_client(true)
        .build_server(false)
        .compile(&["proto/control.proto"], &["proto"])?;

    Ok(())
}

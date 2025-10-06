#![forbid(unsafe_code)]

use assert_cmd::prelude::*;
use std::process::Command;
use std::time::{Duration, Instant};

#[test]
fn test_help_performance() -> Result<(), Box<dyn std::error::Error>> {
    let start = Instant::now();
    let mut cmd = Command::cargo_bin("nyx-cli")?;
    cmd.arg("--help");
    cmd.assert().success();
    let elapsed = start.elapsed();

    assert!(
        elapsed < Duration::from_millis(100),
        "Help command took too long: {:?}",
        elapsed
    );
    Ok(())
}

#[test]
fn test_config_show_performance() -> Result<(), Box<dyn std::error::Error>> {
    let start = Instant::now();
    let mut cmd = Command::cargo_bin("nyx-cli")?;
    cmd.args(["config", "show"]);
    cmd.assert().success();
    let elapsed = start.elapsed();

    assert!(
        elapsed < Duration::from_millis(500),
        "Config show took too long: {:?}",
        elapsed
    );
    Ok(())
}

#[test]
fn test_frame_limit_performance() -> Result<(), Box<dyn std::error::Error>> {
    let start = Instant::now();
    let mut cmd = Command::cargo_bin("nyx-cli")?;
    cmd.arg("frame-limit");
    cmd.assert().success();
    let elapsed = start.elapsed();

    assert!(
        elapsed < Duration::from_millis(100),
        "Frame limit command took too long: {:?}",
        elapsed
    );
    Ok(())
}

#[test]
fn test_multiple_commands_sequential() -> Result<(), Box<dyn std::error::Error>> {
    let start = Instant::now();

    for _ in 0..5 {
        let mut cmd = Command::cargo_bin("nyx-cli")?;
        cmd.args(["config", "show"]);
        cmd.assert().success();
    }

    let elapsed = start.elapsed();
    let avg = elapsed / 5;

    assert!(
        avg < Duration::from_millis(500),
        "Average command time too high: {:?}",
        avg
    );
    Ok(())
}

#[test]
fn test_invalid_command_fast_failure() -> Result<(), Box<dyn std::error::Error>> {
    let start = Instant::now();
    let mut cmd = Command::cargo_bin("nyx-cli")?;
    cmd.arg("nonexistent-command");
    cmd.assert().failure();
    let elapsed = start.elapsed();

    assert!(
        elapsed < Duration::from_millis(100),
        "Invalid command took too long to fail: {:?}",
        elapsed
    );
    Ok(())
}

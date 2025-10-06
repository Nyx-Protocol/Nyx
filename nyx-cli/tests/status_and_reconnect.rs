#![forbid(unsafe_code)]

use assert_cmd::prelude::*;
use predicates::prelude::*;
use std::process::Command;
use tempfile::TempDir;

#[test]
fn test_info_with_no_daemon_fails_gracefully() -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = Command::cargo_bin("nyx-cli")?;
    cmd.args([
        "--endpoint",
        "127.0.0.1:65534",
        "--timeout-ms",
        "100",
        "info",
    ]);

    cmd.assert()
        .failure()
        .stderr(predicate::str::contains("error"));
    Ok(())
}

#[test]
fn test_reload_config_with_invalid_endpoint() -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = Command::cargo_bin("nyx-cli")?;
    cmd.args([
        "--endpoint",
        "invalid-endpoint-format",
        "--timeout-ms",
        "100",
        "reload-config",
    ]);

    cmd.assert().failure();
    Ok(())
}

#[test]
fn test_events_command_structure() -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = Command::cargo_bin("nyx-cli")?;
    cmd.args(["events", "--help"]);
    cmd.assert()
        .success()
        .stdout(predicate::str::contains("types"));
    Ok(())
}

#[test]
fn test_update_config_with_invalid_json() -> Result<(), Box<dyn std::error::Error>> {
    let tmp_dir = TempDir::new()?;
    let invalid_json_path = tmp_dir.path().join("invalid.json");
    std::fs::write(&invalid_json_path, "{ this is not valid json }")?;

    let mut cmd = Command::cargo_bin("nyx-cli")?;
    cmd.args([
        "--endpoint",
        "127.0.0.1:65534",
        "--timeout-ms",
        "100",
        "update-config",
        "--file",
        invalid_json_path.to_str().unwrap(),
    ]);

    cmd.assert()
        .failure()
        .stderr(predicate::str::contains("invalid JSON"));
    Ok(())
}

#[test]
fn test_update_config_with_missing_file() -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = Command::cargo_bin("nyx-cli")?;
    cmd.args([
        "--endpoint",
        "127.0.0.1:65534",
        "--timeout-ms",
        "100",
        "update-config",
        "--file",
        "/nonexistent/path/to/config.json",
    ]);

    cmd.assert()
        .failure()
        .stderr(predicate::str::contains("failed to read file"));
    Ok(())
}

#[test]
fn test_prometheus_get_https_rejected() -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = Command::cargo_bin("nyx-cli")?;
    cmd.args(["prometheus-get", "https://example.com/metrics"]);

    cmd.assert()
        .failure()
        .stderr(predicate::str::contains("https is not supported"));
    Ok(())
}

#[test]
fn test_rollback_command_structure() -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = Command::cargo_bin("nyx-cli")?;
    cmd.args(["rollback", "--help"]);
    cmd.assert()
        .success()
        .stdout(predicate::str::contains("version"));
    Ok(())
}

#[test]
fn test_snapshot_command_structure() -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = Command::cargo_bin("nyx-cli")?;
    cmd.args(["snapshot", "--help"]);
    cmd.assert()
        .success()
        .stdout(predicate::str::contains("description"));
    Ok(())
}

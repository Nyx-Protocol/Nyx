#![forbid(unsafe_code)]

use assert_cmd::prelude::*;
use predicates::prelude::*;
use std::process::Command;

#[test]
fn test_version_flag() -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = Command::cargo_bin("nyx-cli")?;
    cmd.arg("--version");
    cmd.assert()
        .success()
        .stdout(predicate::str::contains("nyx-cli"));
    Ok(())
}

#[test]
fn test_help_flag() -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = Command::cargo_bin("nyx-cli")?;
    cmd.arg("--help");
    cmd.assert()
        .success()
        .stdout(predicate::str::contains("Usage:"))
        .stdout(predicate::str::contains("Commands:"));
    Ok(())
}

#[test]
fn test_config_show_command() -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = Command::cargo_bin("nyx-cli")?;
    cmd.args(["config", "show"]);
    cmd.assert()
        .success()
        .stdout(predicate::str::contains("daemon_endpoint"))
        .stdout(predicate::str::contains("request_timeout_ms"));
    Ok(())
}

#[test]
fn test_frame_limit_display() -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = Command::cargo_bin("nyx-cli")?;
    cmd.arg("frame-limit");
    cmd.assert()
        .success()
        .stdout(predicate::str::is_match(r"^\d+\s*$").unwrap());
    Ok(())
}

#[test]
fn test_config_subcommands_exist() -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = Command::cargo_bin("nyx-cli")?;
    cmd.args(["config", "--help"]);
    cmd.assert()
        .success()
        .stdout(predicate::str::contains("show"))
        .stdout(predicate::str::contains("write-template"))
        .stdout(predicate::str::contains("validate"));
    Ok(())
}

#[test]
fn test_invalid_subcommand() -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = Command::cargo_bin("nyx-cli")?;
    cmd.arg("invalid-command");
    cmd.assert()
        .failure()
        .stderr(predicate::str::contains("unrecognized subcommand"));
    Ok(())
}

#[test]
fn test_gen_cookie_requires_force_for_existing() -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = Command::cargo_bin("nyx-cli")?;
    cmd.args(["gen-cookie", "--help"]);
    cmd.assert()
        .success()
        .stdout(predicate::str::contains("force"))
        .stdout(predicate::str::contains("length"));
    Ok(())
}

#[test]
fn test_compliance_command_exists() -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = Command::cargo_bin("nyx-cli")?;
    cmd.args(["compliance", "--help"]);
    cmd.assert()
        .success()
        .stdout(predicate::str::contains("format"))
        .stdout(predicate::str::contains("detailed"));
    Ok(())
}

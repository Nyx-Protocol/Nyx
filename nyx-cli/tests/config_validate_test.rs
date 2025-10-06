use assert_cmd::Command;
use predicates::prelude::*;
use std::fs;
use tempfile::TempDir;

#[test]
fn test_config_validate_valid() {
    let temp = TempDir::new().unwrap();
    let config_path = temp.path().join("valid.toml");
    fs::write(
        &config_path,
        r#"
log_level = "info"

[network]
bind_addr = "127.0.0.1:43300"
max_peers = 100

[crypto]
pq_enabled = true
key_rotation_interval = 3600
"#,
    )
    .unwrap();

    let mut cmd = Command::cargo_bin("nyx-cli").unwrap();
    cmd.args(["config", "validate", config_path.to_str().unwrap()]);
    cmd.assert()
        .success()
        .stdout(predicate::str::contains("✅ Configuration is valid"));
}

#[test]
fn test_config_validate_invalid_log_level() {
    let temp = TempDir::new().unwrap();
    let config_path = temp.path().join("invalid_log.toml");
    fs::write(
        &config_path,
        r#"
log_level = "super_verbose"
"#,
    )
    .unwrap();

    let mut cmd = Command::cargo_bin("nyx-cli").unwrap();
    cmd.args(["config", "validate", config_path.to_str().unwrap()]);
    cmd.assert()
        .failure()
        .stdout(predicate::str::contains("Invalid log_level"))
        .stdout(predicate::str::contains("trace, debug, info, warn, error"));
}

#[test]
fn test_config_validate_invalid_security() {
    let temp = TempDir::new().unwrap();
    let config_path = temp.path().join("invalid_security.toml");
    fs::write(
        &config_path,
        r#"
[security]
max_connections = -5
max_frame_size = 500
"#,
    )
    .unwrap();

    let mut cmd = Command::cargo_bin("nyx-cli").unwrap();
    cmd.args(["config", "validate", config_path.to_str().unwrap()]);
    cmd.assert()
        .failure()
        .stdout(predicate::str::contains(
            "security.max_connections must be greater than 0",
        ))
        .stdout(predicate::str::contains(
            "security.max_frame_size must be between 1024 and 67108864",
        ));
}

#[test]
fn test_config_validate_invalid_network() {
    let temp = TempDir::new().unwrap();
    let config_path = temp.path().join("invalid_network.toml");
    fs::write(
        &config_path,
        r#"
[network]
bind_addr = "not_an_address"
max_peers = 0
"#,
    )
    .unwrap();

    let mut cmd = Command::cargo_bin("nyx-cli").unwrap();
    cmd.args(["config", "validate", config_path.to_str().unwrap()]);
    cmd.assert()
        .failure()
        .stdout(predicate::str::contains("Invalid network.bind_addr"))
        .stdout(predicate::str::contains(
            "network.max_peers must be greater than 0",
        ));
}

#[test]
fn test_config_validate_multipath_out_of_range() {
    let temp = TempDir::new().unwrap();
    let config_path = temp.path().join("invalid_multipath.toml");
    fs::write(
        &config_path,
        r#"
[multipath]
max_paths = 100
min_path_quality = 5.0
"#,
    )
    .unwrap();

    let mut cmd = Command::cargo_bin("nyx-cli").unwrap();
    cmd.args(["config", "validate", config_path.to_str().unwrap()]);
    cmd.assert()
        .failure()
        .stdout(predicate::str::contains(
            "multipath.max_paths must be between 1 and 16",
        ))
        .stdout(predicate::str::contains(
            "multipath.min_path_quality must be between 0.0 and 1.0",
        ));
}

#[test]
fn test_config_validate_telemetry_sampling_rate() {
    let temp = TempDir::new().unwrap();
    let config_path = temp.path().join("invalid_telemetry.toml");
    fs::write(
        &config_path,
        r#"
[telemetry]
otlp_sampling_rate = 2.5
"#,
    )
    .unwrap();

    let mut cmd = Command::cargo_bin("nyx-cli").unwrap();
    cmd.args(["config", "validate", config_path.to_str().unwrap()]);
    cmd.assert().failure().stdout(predicate::str::contains(
        "telemetry.otlp_sampling_rate must be between 0.0 and 1.0",
    ));
}

#[test]
fn test_config_validate_tls_missing_cert() {
    let temp = TempDir::new().unwrap();
    let config_path = temp.path().join("invalid_tls.toml");
    fs::write(
        &config_path,
        r#"
[endpoints]
grpc_addr = "127.0.0.1:50051"
tls_enabled = true
"#,
    )
    .unwrap();

    let mut cmd = Command::cargo_bin("nyx-cli").unwrap();
    cmd.args(["config", "validate", config_path.to_str().unwrap()]);
    cmd.assert()
        .failure()
        .stdout(predicate::str::contains("tls_cert or tls_key is missing"));
}

#[test]
fn test_config_validate_file_not_found() {
    let mut cmd = Command::cargo_bin("nyx-cli").unwrap();
    cmd.args(["config", "validate", "nonexistent.toml"]);
    cmd.assert()
        .failure()
        .stderr(predicate::str::contains("Configuration file not found"));
}

#[test]
fn test_config_validate_toml_parse_error() {
    let temp = TempDir::new().unwrap();
    let config_path = temp.path().join("malformed.toml");
    fs::write(
        &config_path,
        r#"
[incomplete section
log_level = 
"#,
    )
    .unwrap();

    let mut cmd = Command::cargo_bin("nyx-cli").unwrap();
    cmd.args(["config", "validate", config_path.to_str().unwrap()]);
    cmd.assert()
        .failure()
        .stderr(predicate::str::contains("TOML Parse Error"));
}

#[test]
fn test_config_validate_unknown_keys_warning() {
    let temp = TempDir::new().unwrap();
    let config_path = temp.path().join("unknown_keys.toml");
    fs::write(
        &config_path,
        r#"
log_level = "info"
unknown_key = "value"

[unknown_section]
something = "else"
"#,
    )
    .unwrap();

    let mut cmd = Command::cargo_bin("nyx-cli").unwrap();
    cmd.args(["config", "validate", config_path.to_str().unwrap()]);
    cmd.assert()
        .success()
        .stdout(predicate::str::contains("Unknown configuration key"))
        .stdout(predicate::str::contains("warning"));
}

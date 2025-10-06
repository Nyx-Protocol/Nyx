#![forbid(unsafe_code)]

use clap::{Parser, Subcommand};
use nyx_sdk::{daemon::DaemonClient, SdkConfig};
use rand::RngCore;
use serde_json::json;
use std::path::PathBuf;

#[derive(Parser)]
#[command(
    name = "nyx-cli",
    version,
    about = "Nyx command line interface",
    disable_help_subcommand = false
)]
struct Cli {
    /// Daemon endpoint (override). Default: platform-specific (Unix socket / windows named pipe)
    #[arg(long)]
    endpoint: Option<String>,
    /// Request timeout in milliseconds
    #[arg(long)]
    timeout_ms: Option<u64>,
    /// Auth token
    #[arg(long)]
    token: Option<String>,

    #[command(subcommand)]
    command: Commands,
}

#[derive(Debug, Subcommand)]
enum Commands {
    /// Show daemon info
    Info,
    /// Reload configuration
    ReloadConfig,
    /// List config versions
    ListVersions,
    /// Update configuration from inline JSON key=val or a JSON file
    UpdateConfig {
        /// Inline key=value pairs (JSON values). Example: log_level="debug"
        #[arg(long, value_parser = parse_kv, num_args = 0..)]
        set: Vec<(String, serde_json::Value)>,
        /// Path to a JSON file with a flat object of settings
        #[arg(long)]
        file: Option<String>,
    },
    /// Rollback configuration to a specific version
    Rollback { version: u64 },
    /// Create a configuration snapshot with an optional description
    Snapshot {
        #[arg(long)]
        description: Option<String>,
    },
    /// Subscribe to daemon events; press Ctrl-C to stop
    Events {
        #[arg(long)]
        types: Vec<String>,
    },
    /// Fetch Prometheus metrics from a URL (http only)
    PrometheusGet { url: String },
    /// Config helpers
    Config {
        #[command(subcommand)]
        action: ConfigCmd,
    },
    /// Convenience: set or show the codec frame size cap (bytes)
    FrameLimit {
        /// When provided, sets the cap to this value (1024..=67108864). If omitted, shows current default.
        #[arg(long)]
        set: Option<u64>,
    },
    /// Generate a cookie token file compatible with daemon auth
    GenCookie {
        /// Output path (default: platform-specific). Example: %APPDATA%/nyx/control.authcookie
        #[arg(long)]
        path: Option<String>,
        /// Overwrite if file exists
        #[arg(long)]
        force: bool,
        /// Random token length (bytes), hex-encoded
        #[arg(long, default_value_t = 32)]
        length: usize,
    },
    /// Get compliance report from daemon
    Compliance {
        /// Output format: human (default) or json
        #[arg(long, default_value = "human")]
        format: String,
        /// Show detailed feature breakdown by tier
        #[arg(long)]
        detailed: bool,
    },
}

#[derive(Debug, Subcommand)]
enum ConfigCmd {
    /// Show effective CLI config (resolved from env/files)
    Show,
    /// Write a nyx.toml template with CLI section
    WriteTemplate {
        /// Destination path (default: ./nyx.toml)
        #[arg(long)]
        path: Option<String>,
        /// Overwrite if file exists
        #[arg(long)]
        force: bool,
    },
    /// Validate a nyx.toml configuration file
    Validate {
        /// Path to the nyx.toml file to validate (default: ./nyx.toml)
        #[arg(value_name = "FILE")]
        path: Option<String>,
        /// Enable strict mode with additional validations
        #[arg(long)]
        strict: bool,
    },
}

fn parse_kv(s: &str) -> Result<(String, serde_json::Value), String> {
    let (k, v) = s
        .split_once('=')
        .ok_or_else(|| "expected key=value".to_string())?;
    let val = serde_json::from_str::<serde_json::Value>(v)
        .unwrap_or_else(|_| serde_json::Value::String(v.to_string()));
    Ok((k.to_string(), val))
}

#[tokio::main(flavor = "multi_thread")]
async fn main() -> anyhow::Result<()> {
    let cli = Cli::parse();

    // Start with defaults, then apply auto-discovery (env/config), then override by CLI args
    let (mut cfg, mut token) = auto_discover().await;
    if let Some(ep) = cli.endpoint {
        cfg.daemon_endpoint = ep;
    }
    if let Some(t) = cli.timeout_ms {
        cfg.request_timeout_ms = t;
    }
    if let Some(tok) = cli.token {
        token = Some(tok);
    }
    let mut client = DaemonClient::new(cfg);
    if let Some(tok) = token {
        client = client.with_token(tok);
    }

    let res: anyhow::Result<()> = match cli.command {
        Commands::Info => {
            let v = client.get_info().await;
            print_result(v.map(|j| json!({"ok":true, "data": j})));
            Ok(())
        }
        Commands::ReloadConfig => {
            let v = client.reload_config().await;
            print_result(v.map(|j| json!({"ok":true, "data": j})));
            Ok(())
        }
        Commands::ListVersions => {
            let v = client.list_versions().await;
            print_result(v.map(|j| json!({"ok":true, "data": j})));
            Ok(())
        }
        Commands::UpdateConfig { set, file } => {
            let mut map = serde_json::Map::new();
            for (k, v) in set {
                map.insert(k, v);
            }
            if let Some(path) = file {
                match tokio::fs::read_to_string(path).await {
                    Ok(s) => {
                        match serde_json::from_str::<serde_json::Map<String, serde_json::Value>>(&s)
                        {
                            Ok(obj) => {
                                for (k, v) in obj {
                                    map.insert(k, v);
                                }
                            }
                            Err(e) => {
                                eprintln!("invalid JSON file: {e}");
                                std::process::exit(2);
                            }
                        }
                    }
                    Err(e) => {
                        eprintln!("failed to read file: {e}");
                        std::process::exit(2);
                    }
                }
            }
            let v = client.update_config(map).await;
            print_result(v.map(|r| serde_json::to_value(r).unwrap()));
            Ok(())
        }
        Commands::Rollback { version } => {
            let v = client.rollback_config(version).await;
            print_result(v.map(|r| serde_json::to_value(r).unwrap()));
            Ok(())
        }
        Commands::Snapshot { description } => {
            let v = client.create_config_snapshot(description).await;
            print_result(v.map(|j| json!({"ok":true, "data": j})));
            Ok(())
        }
        Commands::Events { types } => {
            match client
                .subscribe_events(if types.is_empty() { None } else { Some(types) })
                .await
            {
                Ok(mut rx) => {
                    let (tx_stop, mut rx_stop) = tokio::sync::mpsc::channel::<()>(1);
                    // Ctrl-C handler (best-effort). Ignore errors if handler already set.
                    let _ = ctrlc::set_handler(move || {
                        let _ = tx_stop.try_send(());
                    });
                    loop {
                        tokio::select! {
                            _ = rx_stop.recv() => { break; }
                            ev = rx.recv() => {
                                match ev {
                                    Ok(ev) => println!("{}", serde_json::to_string(&ev).unwrap()),
                                    Err(_) => break,
                                }
                            }
                        }
                    }
                    Ok(())
                }
                Err(e) => Err(anyhow::anyhow!(format!("subscribe error: {e}"))),
            }
        }
        Commands::PrometheusGet { url } => match prometheus_client::scrape_text(url).await {
            Ok(body) => {
                print!("{body}");
                Ok(())
            }
            Err(e) => Err(anyhow::anyhow!(format!("prometheus fetch failed: {e}"))),
        },
        Commands::Config { action } => match action {
            ConfigCmd::Show => {
                let (cfg, tok) = auto_discover().await;
                let out = json!({
                    "daemon_endpoint": cfg.daemon_endpoint,
                    "request_timeout_ms": cfg.request_timeout_ms,
                    "token_present": tok.is_some(),
                });
                println!("{}", serde_json::to_string_pretty(&out).unwrap());
                Ok(())
            }
            ConfigCmd::WriteTemplate { path, force } => {
                let p = path.unwrap_or_else(|| "nyx.toml".to_string());
                let pathbuf = PathBuf::from(&p);
                if pathbuf.exists() && !force {
                    eprintln!(
                        "refusing to overwrite existing file: {} (use --force)",
                        pathbuf.display()
                    );
                    std::process::exit(2);
                }
                let template = TEMPLATE_NYX_TOML;
                if let Err(e) = tokio::fs::write(&pathbuf, template).await {
                    return Err(anyhow::anyhow!(e));
                }
                eprintln!("wrote {}", pathbuf.display());
                Ok(())
            }
            ConfigCmd::Validate { path, strict } => validate_config(path, strict).await,
        },
        Commands::FrameLimit { set } => {
            if let Some(n) = set {
                // Validate conservative bounds to protect memory usage.
                const MIN: u64 = 1024; // 1 KiB
                const MAX: u64 = 64 * 1024 * 1024; // 64 MiB
                if !(MIN..=MAX).contains(&n) {
                    anyhow::bail!("invalid frame limit: {} (allowed {}..={})", n, MIN, MAX);
                }
                let mut map = serde_json::Map::new();
                map.insert("max_frame_len_bytes".into(), serde_json::Value::from(n));
                let v = client.update_config(map).await;
                print_result(v.map(|r| serde_json::to_value(r).unwrap()));
            } else {
                let current = nyx_stream::FrameCodec::default_limit() as u64;
                println!("{current}");
            }
            Ok(())
        }
        Commands::GenCookie {
            path,
            force,
            length,
        } => {
            let pathbuf = if let Some(p) = path {
                PathBuf::from(p)
            } else {
                default_cookie_path()
            };
            if pathbuf.exists() && !force {
                eprintln!(
                    "refusing to overwrite existing file: {} (use --force)",
                    pathbuf.display()
                );
                std::process::exit(2);
            }
            if length == 0 || length > 1024 {
                anyhow::bail!("invalid length: {length}");
            }
            let mut bytes = vec![0u8; length];
            rand::thread_rng().fill_bytes(&mut bytes);
            let token = hex::encode(bytes);
            if let Some(parent) = pathbuf.parent() {
                tokio::fs::create_dir_all(parent).await.ok();
            }
            tokio::fs::write(&pathbuf, &token).await?;
            #[cfg(unix)]
            {
                use std::fs::{metadata, set_permissions};
                use std::os::unix::fs::PermissionsExt;
                if let Ok(meta) = metadata(&pathbuf) {
                    let mut perm = meta.permissions();
                    perm.set_mode(0o600);
                    let _ = set_permissions(&pathbuf, perm);
                }
            }
            eprintln!("wrote {}", pathbuf.display());
            Ok(())
        }
        Commands::Compliance { format, detailed } => {
            handle_compliance(&client, &format, detailed).await
        }
    };

    res
}

fn print_result(res: Result<serde_json::Value, nyx_sdk::Error>) {
    match res {
        Ok(v) => println!("{}", serde_json::to_string_pretty(&v).unwrap()),
        Err(e) => {
            eprintln!("error: {e}");
            std::process::exit(1);
        }
    }
}

mod prometheus_client;

// ---------------- helper: auto-discovery -----------------

#[derive(Debug, Default)]
struct CliFileConfig {
    endpoint: Option<String>,
    token: Option<String>,
    timeout_ms: Option<u64>,
}

async fn auto_discover() -> (SdkConfig, Option<String>) {
    let mut cfg = SdkConfig::default();
    let mut token: Option<String> = None;
    // Track whether user explicitly set token via env var (even if empty)
    // This prevents falling back to cookie/config when user wants no token
    let mut token_env_explicitly_set = false;

    // 1) Env vars
    if let Ok(ep) = std::env::var("NYX_DAEMON_ENDPOINT") {
        let e = ep.trim();
        if !e.is_empty() {
            cfg.daemon_endpoint = e.to_string();
        }
    }
    if let Ok(t) = std::env::var("NYX_REQUEST_TIMEOUT_MS") {
        if let Ok(v) = t.parse::<u64>() {
            cfg.request_timeout_ms = v;
        }
    }
    // Prefer NYX_CONTROL_TOKEN (charts/values.yaml hint) then NYX_TOKEN
    // Note: Presence of env var (even if whitespace-only) signals explicit intent
    // to override cookie/config token. Empty/whitespace means "no token".
    if let Ok(tok) = std::env::var("NYX_CONTROL_TOKEN") {
        token_env_explicitly_set = true;
        if !tok.trim().is_empty() {
            token = Some(tok.trim().to_string());
        }
    }
    if !token_env_explicitly_set {
        if let Ok(tok) = std::env::var("NYX_TOKEN") {
            token_env_explicitly_set = true;
            if !tok.trim().is_empty() {
                token = Some(tok.trim().to_string());
            }
        }
    }

    // 2) Cookie file (Tor-style). Only use if env var was NOT explicitly set
    if token.is_none() && !token_env_explicitly_set {
        if let Some(tok) = read_cookie_token().await {
            token = Some(tok);
        }
    }

    // 3) Config file (only fills missing)
    if let Some(file_cfg) = load_cli_file_config().await {
        if cfg.daemon_endpoint == SdkConfig::default_endpoint() {
            if let Some(ep) = file_cfg.endpoint {
                cfg.daemon_endpoint = ep;
            }
        }
        if let Some(ms) = file_cfg.timeout_ms {
            cfg.request_timeout_ms = ms;
        }
        // Only use config file token if env var was NOT explicitly set
        if token.is_none() && !token_env_explicitly_set {
            token = file_cfg.token.filter(|s| !s.trim().is_empty());
        }
    }

    (cfg, token)
}

async fn load_cli_file_config() -> Option<CliFileConfig> {
    // Search order: $NYX_CONFIG -> ./nyx.toml -> platform config dir
    let mut candidates: Vec<PathBuf> = Vec::new();
    if let Ok(p) = std::env::var("NYX_CONFIG") {
        candidates.push(PathBuf::from(p));
    }
    candidates.push(PathBuf::from("nyx.toml"));
    // Platform specific default
    if cfg!(windows) {
        if let Ok(app_data) = std::env::var("APPDATA") {
            candidates.push(PathBuf::from(app_data).join("nyx").join("nyx.toml"));
        }
    } else {
        if let Ok(xdg) = std::env::var("XDG_CONFIG_HOME") {
            candidates.push(PathBuf::from(xdg).join("nyx").join("nyx.toml"));
        }
        if let Ok(home) = std::env::var("HOME") {
            candidates.push(
                PathBuf::from(home)
                    .join(".config")
                    .join("nyx")
                    .join("nyx.toml"),
            );
        }
    }

    for path in candidates {
        if !path.exists() {
            continue;
        }
        if let Ok(s) = tokio::fs::read_to_string(&path).await {
            if let Some(parsed) = parse_cli_toml(&s) {
                return Some(parsed);
            }
        }
    }
    None
}

fn parse_cli_toml(s: &str) -> Option<CliFileConfig> {
    let v: toml::Value = toml::from_str(s).ok()?;
    let mut out = CliFileConfig::default();
    if let Some(cli) = v.get("cli") {
        if let Some(ep) = cli.get("daemon_endpoint").and_then(|x| x.as_str()) {
            let ep = ep.trim();
            if !ep.is_empty() {
                out.endpoint = Some(ep.to_string());
            }
        }
        if let Some(tok) = cli.get("token").and_then(|x| x.as_str()) {
            let tok = tok.trim();
            if !tok.is_empty() {
                out.token = Some(tok.to_string());
            }
        }
        if let Some(ms) = cli.get("request_timeout_ms").and_then(|x| x.as_integer()) {
            if ms >= 0 {
                out.timeout_ms = Some(ms as u64);
            }
        }
    }
    Some(out)
}

const TEMPLATE_NYX_TOML: &str = r#"# Nyx Configuration (template)

# Service endpoints
[endpoints]
grpc_addr = "127.0.0.1:50051"
prometheus_addr = "127.0.0.1:9090"

# CLI specific configuration
[cli]
# windows named pipe example: \\.\pipe\nyx-daemon
# Unix domain socket example: /tmp/nyx.sock
daemon_endpoint = "\\\\.\\pipe\\nyx-daemon"
request_timeout_ms = 5000
# Set a control token if daemon requires auth
token = ""

# Static safety limits
# If set, this applies at daemon startup or reload.
max_frame_len_bytes = 8388608
"#;

fn default_cookie_path() -> PathBuf {
    if cfg!(windows) {
        if let Ok(app_data) = std::env::var("APPDATA") {
            return PathBuf::from(app_data)
                .join("nyx")
                .join("control.authcookie");
        }
    } else if let Ok(home) = std::env::var("HOME") {
        return PathBuf::from(home).join(".nyx").join("control.authcookie");
    }
    PathBuf::from("control.authcookie")
}

async fn read_cookie_token() -> Option<String> {
    if let Ok(p) = std::env::var("NYX_DAEMON_COOKIE") {
        if !p.trim().is_empty() {
            if let Ok(s) = tokio::fs::read_to_string(&p).await {
                let v = s.trim().to_string();
                if !v.is_empty() {
                    return Some(v);
                }
            }
        }
    }
    let p = default_cookie_path();
    if let Ok(s) = tokio::fs::read_to_string(&p).await {
        let v = s.trim().to_string();
        if !v.is_empty() {
            return Some(v);
        }
    }
    None
}

/// Validate a nyx.toml configuration file
/// Returns Ok(()) if valid, Err with descriptive error message if invalid
async fn validate_config(path: Option<String>, strict: bool) -> anyhow::Result<()> {
    use std::collections::HashSet;

    let config_path = path.unwrap_or_else(|| "nyx.toml".to_string());
    let pathbuf = PathBuf::from(&config_path);

    // Check if file exists
    if !pathbuf.exists() {
        eprintln!(
            "❌ Error: Configuration file not found: {}",
            pathbuf.display()
        );
        std::process::exit(1);
    }

    // Read and parse TOML
    let contents = match tokio::fs::read_to_string(&pathbuf).await {
        Ok(s) => s,
        Err(e) => {
            eprintln!("❌ Error reading file {}: {}", pathbuf.display(), e);
            std::process::exit(1);
        }
    };

    // Parse as generic TOML first to provide better error messages
    let config: toml::Value = match toml::from_str(&contents) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("❌ TOML Parse Error in {}:", pathbuf.display());
            eprintln!("   {}", e);
            if let Some(span) = e.span() {
                eprintln!("   At line {}, column {}", span.start, span.end);
            }
            std::process::exit(1);
        }
    };

    let mut warnings = Vec::new();
    let mut errors = Vec::new();

    // Validate basic structure and required fields
    if let Some(table) = config.as_table() {
        // Validate log_level if present
        if let Some(log_level) = table.get("log_level").and_then(|v| v.as_str()) {
            let valid_levels = ["trace", "debug", "info", "warn", "error"];
            if !valid_levels.contains(&log_level) {
                errors.push(format!(
                    "Invalid log_level '{}'. Must be one of: {}",
                    log_level,
                    valid_levels.join(", ")
                ));
            }
        }

        // Validate [security] section
        if let Some(security) = table.get("security").and_then(|v| v.as_table()) {
            if let Some(max_conn) = security.get("max_connections").and_then(|v| v.as_integer()) {
                if max_conn <= 0 {
                    errors.push("security.max_connections must be greater than 0".to_string());
                }
            }
            if let Some(timeout) = security
                .get("connection_timeout")
                .and_then(|v| v.as_integer())
            {
                if timeout <= 0 {
                    errors.push("security.connection_timeout must be greater than 0".to_string());
                }
            }
            // Validate maximum frame size: must be between 1KB and 64MB to prevent DoS attacks
            // and ensure reasonable memory usage
            if let Some(frame_size) = security.get("max_frame_size").and_then(|v| v.as_integer()) {
                if !(1024..=67108864).contains(&frame_size) {
                    errors.push(
                        "security.max_frame_size must be between 1024 and 67108864 (64MB)"
                            .to_string(),
                    );
                }
            }
        }

        // Validate [network] section
        if let Some(network) = table.get("network").and_then(|v| v.as_table()) {
            if let Some(bind_addr) = network.get("bind_addr").and_then(|v| v.as_str()) {
                if let Err(e) = bind_addr.parse::<std::net::SocketAddr>() {
                    errors.push(format!("Invalid network.bind_addr '{}': {}", bind_addr, e));
                }
            }
            if let Some(max_peers) = network.get("max_peers").and_then(|v| v.as_integer()) {
                if max_peers <= 0 {
                    errors.push("network.max_peers must be greater than 0".to_string());
                }
            }
        }

        // Validate [crypto] section
        if let Some(crypto) = table.get("crypto").and_then(|v| v.as_table()) {
            if let Some(interval) = crypto
                .get("key_rotation_interval")
                .and_then(|v| v.as_integer())
            {
                if interval <= 0 {
                    warnings.push(
                        "crypto.key_rotation_interval is 0 or negative; key rotation disabled"
                            .to_string(),
                    );
                } else if interval < 300 {
                    warnings.push(
                        "crypto.key_rotation_interval < 5 minutes may impact performance"
                            .to_string(),
                    );
                }
            }
            if let Some(timeout) = crypto.get("session_timeout").and_then(|v| v.as_integer()) {
                if timeout <= 0 {
                    errors.push("crypto.session_timeout must be greater than 0".to_string());
                }
            }
        }

        // Validate [dht] section
        if let Some(dht) = table.get("dht").and_then(|v| v.as_table()) {
            // Validate DHT port: recommend unprivileged ports (1024-65535) to avoid requiring root
            // and stay within valid port range
            if let Some(port) = dht.get("port").and_then(|v| v.as_integer()) {
                if !(1024..=65535).contains(&port) {
                    warnings.push(format!(
                        "dht.port {} is outside recommended range 1024-65535",
                        port
                    ));
                }
            }
            if let Some(cache_size) = dht.get("peer_cache_size").and_then(|v| v.as_integer()) {
                if cache_size <= 0 {
                    errors.push("dht.peer_cache_size must be greater than 0".to_string());
                }
            }
        }

        // Validate [endpoints] section
        if let Some(endpoints) = table.get("endpoints").and_then(|v| v.as_table()) {
            if let Some(grpc_addr) = endpoints.get("grpc_addr").and_then(|v| v.as_str()) {
                if let Err(e) = grpc_addr.parse::<std::net::SocketAddr>() {
                    errors.push(format!(
                        "Invalid endpoints.grpc_addr '{}': {}",
                        grpc_addr, e
                    ));
                }
            }
            if let Some(prom_addr) = endpoints.get("prometheus_addr").and_then(|v| v.as_str()) {
                if let Err(e) = prom_addr.parse::<std::net::SocketAddr>() {
                    errors.push(format!(
                        "Invalid endpoints.prometheus_addr '{}': {}",
                        prom_addr, e
                    ));
                }
            }
            // Validate TLS configuration: if enabled, both certificate and key must be provided
            // for secure gRPC communication
            if let Some(tls_enabled) = endpoints.get("tls_enabled").and_then(|v| v.as_bool()) {
                if tls_enabled
                    && (!endpoints.contains_key("tls_cert") || !endpoints.contains_key("tls_key"))
                {
                    errors.push(
                        "endpoints.tls_enabled is true but tls_cert or tls_key is missing"
                            .to_string(),
                    );
                }
            }
        }

        // Validate [multipath] section (new schema)
        if let Some(multipath) = table.get("multipath").and_then(|v| v.as_table()) {
            if let Some(max_paths) = multipath.get("max_paths").and_then(|v| v.as_integer()) {
                if max_paths <= 0 || max_paths > 16 {
                    errors.push("multipath.max_paths must be between 1 and 16".to_string());
                }
            }
            // Validate path quality threshold: normalized value between 0.0 (worst) and 1.0 (best)
            // used for multipath routing decisions
            if let Some(quality) = multipath.get("min_path_quality").and_then(|v| v.as_float()) {
                if !(0.0..=1.0).contains(&quality) {
                    errors
                        .push("multipath.min_path_quality must be between 0.0 and 1.0".to_string());
                }
            }
        }

        // Validate [telemetry] section (new schema)
        if let Some(telemetry) = table.get("telemetry").and_then(|v| v.as_table()) {
            if let Some(endpoint) = telemetry.get("otlp_endpoint").and_then(|v| v.as_str()) {
                // Basic URL validation
                if !endpoint.starts_with("http://") && !endpoint.starts_with("https://") {
                    warnings.push(format!(
                        "telemetry.otlp_endpoint '{}' should start with http:// or https://",
                        endpoint
                    ));
                }

                // Strict mode: check if endpoint is reachable (using ureq for Pure Rust)
                if strict {
                    print!("🔍 Checking OTLP endpoint connectivity... ");
                    match ureq::get(endpoint)
                        .timeout(std::time::Duration::from_secs(5))
                        .call()
                    {
                        Ok(_) => println!("✅ reachable"),
                        Err(e) => {
                            println!("⚠️  unreachable");
                            warnings.push(format!(
                                "telemetry.otlp_endpoint '{}' is unreachable: {}",
                                endpoint, e
                            ));
                        }
                    }
                }
            }
            // Validate OTLP sampling rate: percentage of traces to export (0.0=none, 1.0=all)
            // to control telemetry overhead and costs
            if let Some(rate) = telemetry
                .get("otlp_sampling_rate")
                .and_then(|v| v.as_float())
            {
                if !(0.0..=1.0).contains(&rate) {
                    errors.push(
                        "telemetry.otlp_sampling_rate must be between 0.0 and 1.0".to_string(),
                    );
                }
            }
        }

        // Validate [mix] section (new schema)
        if let Some(mix) = table.get("mix").and_then(|v| v.as_table()) {
            if let Some(batch_size) = mix.get("batch_size").and_then(|v| v.as_integer()) {
                if batch_size <= 0 || batch_size > 10000 {
                    errors.push("mix.batch_size must be between 1 and 10000".to_string());
                }
            }
            // Validate cover traffic ratio: fraction of bandwidth allocated to dummy traffic
            // (0.0=no cover, 1.0=only cover) for traffic analysis resistance
            if let Some(ratio) = mix.get("cover_traffic_ratio").and_then(|v| v.as_float()) {
                if !(0.0..=1.0).contains(&ratio) {
                    errors.push("mix.cover_traffic_ratio must be between 0.0 and 1.0".to_string());
                }
            }
        }

        // Check for unknown/deprecated top-level keys
        let known_keys: HashSet<&str> = [
            "listen_port",
            "node_id",
            "log_level",
            "log_format",
            "security",
            "bootstrap_peers",
            "network",
            "crypto",
            "dht",
            "endpoints",
            "cli",
            "performance",
            "plugins",
            "multipath",
            "telemetry",
            "mix",
            "low_power",
            "development",
            "limits",
            "monitoring",
        ]
        .iter()
        .copied()
        .collect();

        for key in table.keys() {
            if !known_keys.contains(key.as_str()) {
                warnings.push(format!("Unknown configuration key: '{}'", key));
            }
        }
    }

    // Print validation results
    println!("✅ TOML Syntax: Valid");

    if !warnings.is_empty() {
        println!("\n⚠️  Warnings ({}):", warnings.len());
        for (i, warning) in warnings.iter().enumerate() {
            println!("   {}. {}", i + 1, warning);
        }
    }

    if !errors.is_empty() {
        println!("\n❌ Errors ({}):", errors.len());
        for (i, error) in errors.iter().enumerate() {
            println!("   {}. {}", i + 1, error);
        }
        eprintln!(
            "\n❌ Configuration validation failed with {} error(s)",
            errors.len()
        );
        std::process::exit(1);
    }

    if warnings.is_empty() {
        println!("\n✅ Configuration is valid!");
    } else {
        println!(
            "\n✅ Configuration is valid (with {} warning(s))",
            warnings.len()
        );
    }

    Ok(())
}

/// Handle compliance report command
async fn handle_compliance(
    client: &DaemonClient,
    format: &str,
    detailed: bool,
) -> anyhow::Result<()> {
    let report = client.get_compliance_report().await?;

    match format {
        "json" => {
            // JSON output for machine consumption
            println!("{}", serde_json::to_string_pretty(&report)?);
        }
        _ => {
            // Human-readable table format
            println!("╔════════════════════════════════════════════════════════════╗");
            println!("║           Nyx Protocol Compliance Report                  ║");
            println!("╚════════════════════════════════════════════════════════════╝");
            println!();

            // Summary section
            println!(
                "📊 Compliance Level: {}",
                report
                    .get("compliance_level")
                    .and_then(|v| v.as_str())
                    .unwrap_or("unknown")
                    .to_uppercase()
            );

            let detected_count = report
                .get("detected_features")
                .and_then(|v| v.as_array())
                .map(|a| a.len())
                .unwrap_or(0);
            let available_count = report
                .get("available_features")
                .and_then(|v| v.as_array())
                .map(|a| a.len())
                .unwrap_or(0);
            let missing_count = report
                .get("missing_features")
                .and_then(|v| v.as_array())
                .map(|a| a.len())
                .unwrap_or(0);

            println!("✅ Detected Features: {}", detected_count);
            println!("📦 Available Features: {}", available_count);
            if missing_count > 0 {
                println!("⚠️  Missing Features: {}", missing_count);
            }
            println!();

            // Detailed breakdown if requested
            if detailed {
                println!("─────────────────────────────────────────────────────────────");
                println!("Tier Breakdown:");
                println!();

                if let Some(core) = report.get("core_features") {
                    print_tier_features("CORE", core);
                }
                if let Some(plus) = report.get("plus_features") {
                    print_tier_features("PLUS", plus);
                }
                if let Some(full) = report.get("full_features") {
                    print_tier_features("FULL", full);
                }
            }

            // Summary text
            if let Some(summary) = report.get("summary").and_then(|v| v.as_str()) {
                println!("─────────────────────────────────────────────────────────────");
                println!("Summary:");
                println!("{}", summary);
            }

            // Timestamp
            if let Some(timestamp) = report.get("report_generated_at") {
                println!();
                println!(
                    "Generated at: {}",
                    timestamp
                        .get("seconds")
                        .and_then(|v| v.as_i64())
                        .map(|s| format!("{}", s))
                        .unwrap_or_else(|| "unknown".to_string())
                );
            }
        }
    }

    Ok(())
}

/// Print features for a compliance tier
fn print_tier_features(tier_name: &str, tier_data: &serde_json::Value) {
    println!("  {} Tier:", tier_name);

    if let Some(required) = tier_data.get("required").and_then(|v| v.as_array()) {
        println!("    Required: {}", required.len());
        if !required.is_empty() {
            for feature in required.iter().take(3) {
                if let Some(f) = feature.as_str() {
                    println!("      • {}", f);
                }
            }
            if required.len() > 3 {
                println!("      ... and {} more", required.len() - 3);
            }
        }
    }

    if let Some(detected) = tier_data.get("detected").and_then(|v| v.as_array()) {
        let missing_in_tier = tier_data
            .get("missing")
            .and_then(|v| v.as_array())
            .map(|a| a.len())
            .unwrap_or(0);
        println!("    Detected: {} ✅", detected.len());
        if missing_in_tier > 0 {
            println!("    Missing: {} ⚠️", missing_in_tier);
        }
    }

    println!();
}

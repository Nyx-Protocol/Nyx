//! Test execution script for comprehensive test suite
#!/usr/bin/env pwsh

# Colors
$Green = "`e[32m"
$Red = "`e[31m"
$Yellow = "`e[33m"
$Reset = "`e[0m"

Write-Host "${Green}=== NyxNet Comprehensive Test Suite ===${Reset}`n"

# Configuration
$ErrorActionPreference = "Continue"
$TestResults = @{
    Passed = 0
    Failed = 0
    Skipped = 0
}

function Run-TestPhase {
    param(
        [string]$Name,
        [string]$Command
    )
    
    Write-Host "${Yellow}► Running: $Name${Reset}"
    Invoke-Expression $Command
    
    if ($LASTEXITCODE -eq 0) {
        $TestResults.Passed++
        Write-Host "${Green}✓ $Name passed${Reset}`n"
        return $true
    } else {
        $TestResults.Failed++
        Write-Host "${Red}✗ $Name failed${Reset}`n"
        return $false
    }
}

# Phase 1: nyx-crypto
Run-TestPhase "nyx-crypto tests" "cargo test -p nyx-crypto --test hybrid_pq_comprehensive"
Run-TestPhase "HPKE compliance" "cargo test -p nyx-crypto --test hpke_rfc9180_compliance"
Run-TestPhase "Replay protection" "cargo test -p nyx-crypto --test session_replay_protection"
Run-TestPhase "Keystore zeroization" "cargo test -p nyx-crypto --test keystore_zeroization"

# Phase 2: nyx-transport
Run-TestPhase "QUIC datagram" "cargo test -p nyx-transport --test quic_datagram_rfc9221"
Run-TestPhase "Multipath BBR" "cargo test -p nyx-transport --test multipath_bbr_scheduler"
Run-TestPhase "ICE/Teredo" "cargo test -p nyx-transport --test ice_teredo_integration"

# Phase 3: nyx-stream
Run-TestPhase "Handshake state" "cargo test -p nyx-stream --test handshake_state_machine"
Run-TestPhase "Frame ordering" "cargo test -p nyx-stream --test frame_ordering_reorder"
Run-TestPhase "Capability negotiation" "cargo test -p nyx-stream --test capability_negotiation_compat"
Run-TestPhase "Security tests" "cargo test -p nyx-stream --test integrated_security_tests"
Run-TestPhase "Property frame" "cargo test -p nyx-stream --test property_frame_codec"

# Phase 4: Integration
Run-TestPhase "0-RTT handshake" "cargo test -p tests --test e2e_zero_rtt_handshake"
Run-TestPhase "Multipath failover" "cargo test -p tests --test e2e_multipath_failover"
Run-TestPhase "Stress test" "cargo test -p tests --test stress_concurrent_connections"
Run-TestPhase "Network partition" "cargo test -p tests --test network_partition_recovery"

# Phase 5: Other components
Run-TestPhase "Mix cover traffic" "cargo test -p nyx-mix --test cover_traffic_poisson"
Run-TestPhase "FEC adaptive" "cargo test -p nyx-fec --test adaptive_redundancy"
Run-TestPhase "gRPC API" "cargo test -p nyx-control --test grpc_api_all_methods"
Run-TestPhase "OTLP export" "cargo test -p nyx-telemetry --test otlp_span_export_e2e"
Run-TestPhase "Network simulator" "cargo test -p nyx-conformance --test deterministic_network_sim"
Run-TestPhase "SDK API" "cargo test -p nyx-sdk --test public_api_coverage"
Run-TestPhase "CLI validation" "cargo test -p nyx-cli --test config_validation_cli"

# Summary
Write-Host "`n${Green}=== Test Summary ===${Reset}"
Write-Host "Passed:  ${Green}$($TestResults.Passed)${Reset}"
Write-Host "Failed:  ${Red}$($TestResults.Failed)${Reset}"
Write-Host "Skipped: ${Yellow}$($TestResults.Skipped)${Reset}"

$Total = $TestResults.Passed + $TestResults.Failed + $TestResults.Skipped
$SuccessRate = if ($Total -gt 0) { ($TestResults.Passed / $Total * 100) } else { 0 }

Write-Host "`nSuccess Rate: ${Green}$($SuccessRate.ToString('0.00'))%${Reset}`n"

if ($TestResults.Failed -eq 0) {
    Write-Host "${Green}✓ All tests passed!${Reset}`n"
    exit 0
} else {
    Write-Host "${Red}✗ Some tests failed${Reset}`n"
    exit 1
}

package main

import (
	"encoding/json"
	"testing"
)

// Test JSON-RPC request marshaling
func TestJsonRpcRequestMarshal(t *testing.T) {
	params := ConnectParams{
		Target:   "example.com:443",
		Protocol: "socks5",
	}

	request := JsonRpcRequest{
		Jsonrpc: "2.0",
		Method:  "proxy.connect",
		Params:  params,
		ID:      1,
	}

	data, err := json.Marshal(request)
	if err != nil {
		t.Fatalf("failed to marshal request: %v", err)
	}

	// Verify JSON structure
	var decoded map[string]interface{}
	if err := json.Unmarshal(data, &decoded); err != nil {
		t.Fatalf("failed to unmarshal JSON: %v", err)
	}

	if decoded["jsonrpc"] != "2.0" {
		t.Errorf("expected jsonrpc '2.0', got '%v'", decoded["jsonrpc"])
	}

	if decoded["method"] != "proxy.connect" {
		t.Errorf("expected method 'proxy.connect', got '%v'", decoded["method"])
	}
}

// Test JSON-RPC response unmarshaling (success)
func TestJsonRpcResponseUnmarshalSuccess(t *testing.T) {
	responseJSON := `{
		"jsonrpc": "2.0",
		"result": {
			"stream_id": "stream_1",
			"status": "connected"
		},
		"id": 1
	}`

	var response JsonRpcResponse
	if err := json.Unmarshal([]byte(responseJSON), &response); err != nil {
		t.Fatalf("failed to unmarshal response: %v", err)
	}

	if response.Jsonrpc != "2.0" {
		t.Errorf("expected jsonrpc '2.0', got '%s'", response.Jsonrpc)
	}

	if response.Error != nil {
		t.Errorf("expected no error, got %v", response.Error)
	}

	// Parse result
	var result ConnectResult
	if err := json.Unmarshal(response.Result, &result); err != nil {
		t.Fatalf("failed to parse result: %v", err)
	}

	if result.StreamID != "stream_1" {
		t.Errorf("expected stream_id 'stream_1', got '%s'", result.StreamID)
	}

	if result.Status != "connected" {
		t.Errorf("expected status 'connected', got '%s'", result.Status)
	}
}

// Test JSON-RPC response unmarshaling (error)
func TestJsonRpcResponseUnmarshalError(t *testing.T) {
	responseJSON := `{
		"jsonrpc": "2.0",
		"error": {
			"code": -32001,
			"message": "Connection failed",
			"data": {"target": "example.com:443"}
		},
		"id": 1
	}`

	var response JsonRpcResponse
	if err := json.Unmarshal([]byte(responseJSON), &response); err != nil {
		t.Fatalf("failed to unmarshal response: %v", err)
	}

	if response.Error == nil {
		t.Fatal("expected error, got nil")
	}

	if response.Error.Code != -32001 {
		t.Errorf("expected error code -32001, got %d", response.Error.Code)
	}

	if response.Error.Message != "Connection failed" {
		t.Errorf("expected message 'Connection failed', got '%s'", response.Error.Message)
	}
}

// Test ConnectParams validation
func TestConnectParamsValidation(t *testing.T) {
	testCases := []struct {
		protocol string
		valid    bool
	}{
		{"socks5", true},
		{"http-connect", true},
		{"invalid", false},
		{"", false},
	}

	for _, tc := range testCases {
		params := ConnectParams{
			Target:   "example.com:443",
			Protocol: tc.protocol,
		}

		// Validate protocol
		valid := params.Protocol == "socks5" || params.Protocol == "http-connect"
		if valid != tc.valid {
			t.Errorf("protocol '%s': expected valid=%v, got %v", tc.protocol, tc.valid, valid)
		}
	}
}

// Test MixBridgeClient creation
func TestNewMixBridgeClient(t *testing.T) {
	socketPath := "/tmp/test.sock"
	client := NewMixBridgeClient(socketPath)

	if client == nil {
		t.Fatal("expected non-nil client")
	}

	if client.socketPath != socketPath {
		t.Errorf("expected socket path '%s', got '%s'", socketPath, client.socketPath)
	}

	if client.IsConnected() {
		t.Error("expected client to be disconnected initially")
	}
}

// Test request ID generation
func TestRequestIDGeneration(t *testing.T) {
	client := NewMixBridgeClient("/tmp/test.sock")

	id1 := client.nextRequestID()
	id2 := client.nextRequestID()
	id3 := client.nextRequestID()

	if id1 >= id2 || id2 >= id3 {
		t.Errorf("request IDs should be monotonically increasing: %d, %d, %d", id1, id2, id3)
	}
}

// Test ProxyConnect validation
func TestProxyConnectValidation(t *testing.T) {
	client := NewMixBridgeClient("/tmp/test.sock")

	// Test invalid protocol
	_, err := client.ProxyConnect("example.com:443", "invalid-protocol")
	if err == nil {
		t.Error("expected error for invalid protocol")
	}
}

// Test Close on unconnected client
func TestCloseUnconnectedClient(t *testing.T) {
	client := NewMixBridgeClient("/tmp/test.sock")

	err := client.Close()
	if err != nil {
		t.Errorf("expected no error closing unconnected client, got %v", err)
	}
}

// Benchmark JSON-RPC request marshaling
func BenchmarkJsonRpcRequestMarshal(b *testing.B) {
	params := ConnectParams{
		Target:   "example.com:443",
		Protocol: "socks5",
	}

	request := JsonRpcRequest{
		Jsonrpc: "2.0",
		Method:  "proxy.connect",
		Params:  params,
		ID:      1,
	}

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		json.Marshal(request)
	}
}

// Benchmark JSON-RPC response unmarshaling
func BenchmarkJsonRpcResponseUnmarshal(b *testing.B) {
	responseJSON := []byte(`{
		"jsonrpc": "2.0",
		"result": {
			"stream_id": "stream_1",
			"status": "connected"
		},
		"id": 1
	}`)

	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		var response JsonRpcResponse
		json.Unmarshal(responseJSON, &response)
	}
}

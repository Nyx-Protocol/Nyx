package main

import (
	"bufio"
	"encoding/base64"
	"encoding/json"
	"errors"
	"fmt"
	"net"
	"sync"
	"sync/atomic"
)

// JSON-RPC 2.0 structures

// JsonRpcRequest represents a JSON-RPC 2.0 request
type JsonRpcRequest struct {
	Jsonrpc string      `json:"jsonrpc"`
	Method  string      `json:"method"`
	Params  interface{} `json:"params"`
	ID      interface{} `json:"id"`
}

// JsonRpcResponse represents a JSON-RPC 2.0 response
type JsonRpcResponse struct {
	Jsonrpc string          `json:"jsonrpc"`
	Result  json.RawMessage `json:"result,omitempty"`
	Error   *JsonRpcError   `json:"error,omitempty"`
	ID      interface{}     `json:"id"`
}

// JsonRpcError represents a JSON-RPC 2.0 error object
type JsonRpcError struct {
	Code    int             `json:"code"`
	Message string          `json:"message"`
	Data    json.RawMessage `json:"data,omitempty"`
}

// ConnectParams represents parameters for proxy.connect method
type ConnectParams struct {
	Target   string `json:"target"`
	Protocol string `json:"protocol"` // "socks5" or "http-connect"
}

// ConnectResult represents result from proxy.connect method
type ConnectResult struct {
	StreamID string `json:"stream_id"`
	Status   string `json:"status"`
}

// CloseParams represents parameters for proxy.close method
type CloseParams struct {
	StreamID string `json:"stream_id"`
}

// SendParams represents parameters for proxy.send method (Phase 3)
type SendParams struct {
	StreamID string `json:"stream_id"`
	Data     string `json:"data"` // Base64-encoded payload
}

// SendResult represents result from proxy.send method
type SendResult struct {
	BytesSent int    `json:"bytes_sent"`
	Status    string `json:"status"`
}

// ReceiveParams represents parameters for proxy.receive method (Phase 3)
type ReceiveParams struct {
	StreamID string `json:"stream_id"`
	MaxBytes int    `json:"max_bytes,omitempty"` // Optional, default 8192
}

// ReceiveResult represents result from proxy.receive method
type ReceiveResult struct {
	Data          string `json:"data"` // Base64-encoded received data
	BytesReceived int    `json:"bytes_received"`
	EOF           bool   `json:"eof"`
}

// MixBridgeClient handles IPC communication with Rust Mix Layer
type MixBridgeClient struct {
	socketPath string
	conn       net.Conn
	reader     *bufio.Reader
	writer     *bufio.Writer
	mu         sync.Mutex
	requestID  atomic.Int64
}

// NewMixBridgeClient creates a new Mix Layer IPC bridge client
func NewMixBridgeClient(socketPath string) *MixBridgeClient {
	return &MixBridgeClient{
		socketPath: socketPath,
	}
}

// Connect establishes IPC connection to Mix Layer
func (mbc *MixBridgeClient) Connect() error {
	mbc.mu.Lock()
	defer mbc.mu.Unlock()

	// Platform-specific connection
	// Unix socket for Linux/macOS, Named Pipe for Windows
	conn, err := net.Dial("unix", mbc.socketPath)
	if err != nil {
		return fmt.Errorf("failed to connect to Mix Layer at %s: %w", mbc.socketPath, err)
	}

	mbc.conn = conn
	mbc.reader = bufio.NewReader(conn)
	mbc.writer = bufio.NewWriter(conn)
	return nil
}

// ProxyConnect requests a new connection through Mix Network
func (mbc *MixBridgeClient) ProxyConnect(target string, protocol string) (*ConnectResult, error) {
	// Validate protocol
	if protocol != "socks5" && protocol != "http-connect" {
		return nil, fmt.Errorf("invalid protocol: %s", protocol)
	}

	// Create request
	params := ConnectParams{
		Target:   target,
		Protocol: protocol,
	}

	request := JsonRpcRequest{
		Jsonrpc: "2.0",
		Method:  "proxy.connect",
		Params:  params,
		ID:      mbc.nextRequestID(),
	}

	// Send request and receive response
	response, err := mbc.sendRequest(request)
	if err != nil {
		return nil, err
	}

	// Check for error
	if response.Error != nil {
		return nil, fmt.Errorf("JSON-RPC error %d: %s", response.Error.Code, response.Error.Message)
	}

	// Parse result
	var result ConnectResult
	if err := json.Unmarshal(response.Result, &result); err != nil {
		return nil, fmt.Errorf("failed to parse connect result: %w", err)
	}

	return &result, nil
}

// ProxySend sends data through Mix Network stream (Phase 3: Bidirectional relay)
//
// This method sends data through the established Mix Network circuit.
// Data is automatically encrypted using Sphinx-like onion routing across 3 hops.
//
// Parameters:
// - streamID: ID returned from ProxyConnect
// - data: Raw bytes to send (will be Base64-encoded internally)
//
// Returns error if send fails
func (mbc *MixBridgeClient) ProxySend(streamID string, data []byte) (*SendResult, error) {
	// Base64 encode data for JSON transport
	dataB64 := base64.StdEncoding.EncodeToString(data)

	params := SendParams{
		StreamID: streamID,
		Data:     dataB64,
	}

	request := JsonRpcRequest{
		Jsonrpc: "2.0",
		Method:  "proxy.send",
		Params:  params,
		ID:      mbc.nextRequestID(),
	}

	response, err := mbc.sendRequest(request)
	if err != nil {
		return nil, err
	}

	// Check for error
	if response.Error != nil {
		return nil, fmt.Errorf("JSON-RPC error %d: %s", response.Error.Code, response.Error.Message)
	}

	// Parse result
	var result SendResult
	if err := json.Unmarshal(response.Result, &result); err != nil {
		return nil, fmt.Errorf("failed to parse send result: %w", err)
	}

	return &result, nil
}

// ProxyReceive receives data from Mix Network stream (Phase 3: Bidirectional relay)
//
// This method receives data from the Mix Network endpoint (e.g., HTTP response).
// Data is automatically decrypted after passing through the 3-hop circuit.
//
// Parameters:
// - streamID: ID returned from ProxyConnect
// - maxBytes: Maximum bytes to receive (default: 8192)
//
// Returns:
// - Received data (decoded from Base64)
// - EOF flag (true if stream closed)
// - Error if receive fails
func (mbc *MixBridgeClient) ProxyReceive(streamID string, maxBytes int) ([]byte, bool, error) {
	if maxBytes <= 0 {
		maxBytes = 8192 // Default buffer size
	}

	params := ReceiveParams{
		StreamID: streamID,
		MaxBytes: maxBytes,
	}

	request := JsonRpcRequest{
		Jsonrpc: "2.0",
		Method:  "proxy.receive",
		Params:  params,
		ID:      mbc.nextRequestID(),
	}

	response, err := mbc.sendRequest(request)
	if err != nil {
		return nil, false, err
	}

	// Check for error
	if response.Error != nil {
		return nil, false, fmt.Errorf("JSON-RPC error %d: %s", response.Error.Code, response.Error.Message)
	}

	// Parse result
	var result ReceiveResult
	if err := json.Unmarshal(response.Result, &result); err != nil {
		return nil, false, fmt.Errorf("failed to parse receive result: %w", err)
	}

	// Decode Base64 data
	data, err := base64.StdEncoding.DecodeString(result.Data)
	if err != nil {
		return nil, false, fmt.Errorf("failed to decode base64 data: %w", err)
	}

	return data, result.EOF, nil
}

// ProxyClose closes a Mix Network stream
func (mbc *MixBridgeClient) ProxyClose(streamID string) error {
	params := CloseParams{
		StreamID: streamID,
	}

	request := JsonRpcRequest{
		Jsonrpc: "2.0",
		Method:  "proxy.close",
		Params:  params,
		ID:      mbc.nextRequestID(),
	}

	response, err := mbc.sendRequest(request)
	if err != nil {
		return err
	}

	// Check for error
	if response.Error != nil {
		return fmt.Errorf("JSON-RPC error %d: %s", response.Error.Code, response.Error.Message)
	}

	return nil
}

// sendRequest sends a JSON-RPC request and receives response
func (mbc *MixBridgeClient) sendRequest(request JsonRpcRequest) (*JsonRpcResponse, error) {
	mbc.mu.Lock()
	defer mbc.mu.Unlock()

	if mbc.conn == nil {
		return nil, errors.New("not connected to Mix Layer")
	}

	// Serialize request
	requestJSON, err := json.Marshal(request)
	if err != nil {
		return nil, fmt.Errorf("failed to marshal request: %w", err)
	}

	// Send request (newline-delimited)
	if _, err := mbc.writer.Write(requestJSON); err != nil {
		return nil, fmt.Errorf("failed to write request: %w", err)
	}
	if err := mbc.writer.WriteByte('\n'); err != nil {
		return nil, fmt.Errorf("failed to write newline: %w", err)
	}
	if err := mbc.writer.Flush(); err != nil {
		return nil, fmt.Errorf("failed to flush writer: %w", err)
	}

	// Read response (newline-delimited)
	responseJSON, err := mbc.reader.ReadBytes('\n')
	if err != nil {
		return nil, fmt.Errorf("failed to read response: %w", err)
	}

	// Parse response
	var response JsonRpcResponse
	if err := json.Unmarshal(responseJSON, &response); err != nil {
		return nil, fmt.Errorf("failed to parse response: %w", err)
	}

	return &response, nil
}

// Close closes the IPC connection
func (mbc *MixBridgeClient) Close() error {
	mbc.mu.Lock()
	defer mbc.mu.Unlock()

	if mbc.conn != nil {
		err := mbc.conn.Close()
		mbc.conn = nil
		mbc.reader = nil
		mbc.writer = nil
		return err
	}
	return nil
}

// nextRequestID generates a unique request ID
func (mbc *MixBridgeClient) nextRequestID() int64 {
	return mbc.requestID.Add(1)
}

// IsConnected checks if the bridge is connected
func (mbc *MixBridgeClient) IsConnected() bool {
	mbc.mu.Lock()
	defer mbc.mu.Unlock()
	return mbc.conn != nil
}

package main

import (
	"bufio"
	"crypto/subtle"
	"encoding/base64"
	"errors"
	"fmt"
	"io"
	"log"
	"net"
	"strconv"
	"strings"
	"time"
)

// HTTP CONNECT proxy constants
const (
	// HTTP status codes
	httpStatusOK                = 200 // Connection established
	httpStatusBadRequest        = 400 // Malformed request
	httpStatusProxyAuthRequired = 407 // Authentication required
	httpStatusBadGateway        = 502 // Target unreachable
	httpStatusGatewayTimeout    = 504 // Connection timeout

	// Protocol constraints
	maxHTTPHeaderSize = 8192 // 8KB max header size (DoS protection)
	maxHostLength     = 255  // Max hostname length (RFC 1035)
	connectTimeout    = 30 * time.Second
	tunnelIdleTimeout = 60 * time.Second
)

var (
	// Errors
	errHTTPInvalidRequest     = errors.New("http: invalid CONNECT request")
	errHTTPHeaderTooLarge     = errors.New("http: request header too large")
	errHTTPInvalidHost        = errors.New("http: invalid host format")
	errHTTPAuthRequired       = errors.New("http: proxy authentication required")
	errHTTPAuthFailed         = errors.New("http: authentication failed")
	errHTTPUnsupportedVersion = errors.New("http: unsupported HTTP version")
)

// HTTPConnectServer handles HTTP CONNECT proxy connections
type HTTPConnectServer struct {
	listener  net.Listener
	stats     *Stats
	mixBridge *MixBridgeClient
	shutdown  chan struct{}
	// Optional authentication credentials (Basic auth)
	authUser     string
	authPassword string
}

// NewHTTPConnectServer creates a new HTTP CONNECT proxy server
func NewHTTPConnectServer(addr string, stats *Stats, mixBridge *MixBridgeClient) (*HTTPConnectServer, error) {
	listener, err := net.Listen("tcp", addr)
	if err != nil {
		return nil, fmt.Errorf("failed to listen on %s: %w", addr, err)
	}

	return &HTTPConnectServer{
		listener:  listener,
		stats:     stats,
		mixBridge: mixBridge,
		shutdown:  make(chan struct{}),
	}, nil
}

// SetAuth configures Basic authentication (optional)
func (s *HTTPConnectServer) SetAuth(username, password string) {
	s.authUser = username
	s.authPassword = password
}

// Serve starts the HTTP CONNECT server
func (s *HTTPConnectServer) Serve() error {
	log.Printf("HTTP CONNECT server listening on %s", s.listener.Addr())

	for {
		select {
		case <-s.shutdown:
			return nil
		default:
		}

		conn, err := s.listener.Accept()
		if err != nil {
			select {
			case <-s.shutdown:
				return nil
			default:
				log.Printf("HTTP CONNECT accept error: %v", err)
				continue
			}
		}

		// Handle connection in goroutine
		go s.handleConnection(conn)
	}
}

// Close gracefully shuts down the server
func (s *HTTPConnectServer) Close() error {
	close(s.shutdown)
	return s.listener.Close()
}

// handleConnection processes a single HTTP CONNECT request
func (s *HTTPConnectServer) handleConnection(clientConn net.Conn) {
	defer clientConn.Close()

	s.stats.TotalConnections.Add(1)
	s.stats.HTTPConnections.Add(1)
	s.stats.ActiveConnections.Add(1)
	defer s.stats.ActiveConnections.Add(-1)

	// Set read timeout for header parsing
	if err := clientConn.SetReadDeadline(time.Now().Add(connectTimeout)); err != nil {
		log.Printf("HTTP CONNECT set read deadline error: %v", err)
	}

	// Parse CONNECT request
	targetAddr, authHeader, err := s.parseConnectRequest(clientConn)
	if err != nil {
		log.Printf("HTTP CONNECT parse error: %v", err)
		if err := s.sendErrorResponse(clientConn, httpStatusBadRequest, err.Error()); err != nil {
			log.Printf("HTTP CONNECT send error response failed: %v", err)
		}
		s.stats.Errors.Add(1)
		return
	}

	// Authenticate if credentials are configured
	if s.authUser != "" {
		if err := s.authenticate(authHeader); err != nil {
			log.Printf("HTTP CONNECT auth failed: %v", err)
			if err := s.sendErrorResponse(clientConn, httpStatusProxyAuthRequired, "Proxy authentication required"); err != nil {
				log.Printf("HTTP CONNECT send error response failed: %v", err)
			}
			s.stats.Errors.Add(1)
			return
		}
	}

	// Validate target host
	if err := validateHost(targetAddr); err != nil {
		log.Printf("HTTP CONNECT invalid host %s: %v", targetAddr, err)
		if err := s.sendErrorResponse(clientConn, httpStatusBadRequest, "Invalid host"); err != nil {
			log.Printf("HTTP CONNECT send error response failed: %v", err)
		}
		s.stats.Errors.Add(1)
		return
	}

	// Connect to target via Mix Network through IPC bridge
	// ProxyConnect returns a ProxyConnectResult with StreamID and Address
	result, err := s.mixBridge.ProxyConnect(targetAddr, "http-connect")
	if err != nil {
		log.Printf("HTTP CONNECT Mix connect to %s failed: %v", targetAddr, err)
		s.sendErrorResponse(clientConn, httpStatusBadGateway, "Target unreachable via Mix Network")
		s.stats.Errors.Add(1)
		return
	}

	// Send 200 Connection Established
	if err := s.sendSuccessResponse(clientConn); err != nil {
		log.Printf("HTTP CONNECT send response failed: %v", err)
		s.stats.Errors.Add(1)
		// Close the Mix stream on reply failure
		s.mixBridge.ProxyClose(result.StreamID)
		return
	}

	log.Printf("HTTP CONNECT Mix tunnel established to %s (StreamID: %s)", targetAddr, result.StreamID)

	// Remove read deadline for tunneling phase
	if err := clientConn.SetReadDeadline(time.Time{}); err != nil {
		log.Printf("HTTP CONNECT clear read deadline error: %v", err)
	}

	// Phase 3: Full bidirectional relay implementation
	// Relay data between client and Mix Network using ProxySend/ProxyReceive
	log.Printf("HTTP CONNECT tunnel active for %s (StreamID: %s). Starting bidirectional relay.", targetAddr, result.StreamID)

	// Ensure Mix stream is closed on exit
	defer func() {
		log.Printf("HTTP CONNECT client disconnected from %s, closing Mix stream %s", targetAddr, result.StreamID)
		s.mixBridge.ProxyClose(result.StreamID)
	}()

	// Start bidirectional relay
	// This pumps data in both directions:
	// - Client -> Mix Network (clientConn read -> ProxySend)
	// - Mix Network -> Client (ProxyReceive -> clientConn write)
	err = s.relayBidirectional(clientConn, result.StreamID, targetAddr)
	if err != nil {
		log.Printf("HTTP CONNECT relay error for %s (StreamID: %s): %v", targetAddr, result.StreamID, err)
		s.stats.Errors.Add(1)
	} else {
		log.Printf("HTTP CONNECT relay completed for %s (StreamID: %s)", targetAddr, result.StreamID)
	}
}

// parseConnectRequest parses HTTP CONNECT request line and headers
func (s *HTTPConnectServer) parseConnectRequest(conn net.Conn) (targetAddr string, authHeader string, err error) {
	reader := bufio.NewReader(conn)

	// Read request line: CONNECT host:port HTTP/1.1
	requestLine, err := reader.ReadString('\n')
	if err != nil {
		return "", "", fmt.Errorf("read request line: %w", err)
	}

	// Check header size limit
	if len(requestLine) > maxHTTPHeaderSize {
		return "", "", errHTTPHeaderTooLarge
	}

	// Parse request line
	parts := strings.Fields(strings.TrimSpace(requestLine))
	if len(parts) != 3 {
		return "", "", errHTTPInvalidRequest
	}

	method, target, version := parts[0], parts[1], parts[2]

	// Verify CONNECT method
	if strings.ToUpper(method) != "CONNECT" {
		return "", "", fmt.Errorf("unsupported method: %s", method)
	}

	// Verify HTTP version (HTTP/1.1 or HTTP/1.0)
	if !strings.HasPrefix(version, "HTTP/1.") {
		return "", "", errHTTPUnsupportedVersion
	}

	targetAddr = target

	// Parse headers until blank line
	headerSize := len(requestLine)
	for {
		line, err := reader.ReadString('\n')
		if err != nil {
			return "", "", fmt.Errorf("read headers: %w", err)
		}

		headerSize += len(line)
		if headerSize > maxHTTPHeaderSize {
			return "", "", errHTTPHeaderTooLarge
		}

		// Blank line indicates end of headers
		line = strings.TrimSpace(line)
		if line == "" {
			break
		}

		// Extract Proxy-Authorization header
		if strings.HasPrefix(strings.ToLower(line), "proxy-authorization:") {
			authHeader = strings.TrimSpace(line[len("proxy-authorization:"):])
		}
	}

	return targetAddr, authHeader, nil
}

// authenticate verifies Basic authentication credentials
func (s *HTTPConnectServer) authenticate(authHeader string) error {
	if authHeader == "" {
		return errHTTPAuthRequired
	}

	// Parse "Basic <base64-credentials>"
	if !strings.HasPrefix(authHeader, "Basic ") {
		return fmt.Errorf("unsupported auth scheme: %s", authHeader)
	}

	encodedCreds := strings.TrimPrefix(authHeader, "Basic ")
	decodedCreds, err := base64.StdEncoding.DecodeString(encodedCreds)
	if err != nil {
		return fmt.Errorf("invalid base64 encoding: %w", err)
	}

	// Parse "username:password"
	creds := string(decodedCreds)
	colonIdx := strings.Index(creds, ":")
	if colonIdx == -1 {
		return fmt.Errorf("invalid credentials format")
	}

	username := creds[:colonIdx]
	password := creds[colonIdx+1:]

	// Constant-time comparison to prevent timing attacks
	usernameMatch := subtle.ConstantTimeCompare([]byte(username), []byte(s.authUser))
	passwordMatch := subtle.ConstantTimeCompare([]byte(password), []byte(s.authPassword))

	if usernameMatch != 1 || passwordMatch != 1 {
		return errHTTPAuthFailed
	}

	return nil
}

// relayBidirectional performs full-duplex relay between client and Mix Network
//
// This function spawns two goroutines:
// 1. Client -> Mix: Read from client, send via ProxySend (Base64 encoded)
// 2. Mix -> Client: Receive via ProxyReceive (Base64 decoded), write to client
//
// Both goroutines run until EOF or error, then signal completion.
// The function returns when both directions have completed.
func (s *HTTPConnectServer) relayBidirectional(clientConn net.Conn, streamID string, targetAddr string) error {
	// Error channel for both directions
	// Buffer size 2 to avoid blocking on send
	errChan := make(chan error, 2)

	// Goroutine 1: Client -> Mix Network
	// Read from client, send through Mix via ProxySend
	go func() {
		buf := make([]byte, 32768) // 32KB buffer for client reads
		for {
			// Check for shutdown signal
			select {
			case <-s.shutdown:
				errChan <- nil
				return
			default:
			}

			// Read from client with timeout
			if err := clientConn.SetReadDeadline(time.Now().Add(30 * time.Second)); err != nil {
				log.Printf("HTTP CONNECT set read deadline error: %v", err)
			}
			n, err := clientConn.Read(buf)
			if err != nil {
				if err == io.EOF {
					log.Printf("HTTP CONNECT client->Mix EOF for %s (StreamID: %s)", targetAddr, streamID)
					errChan <- nil // Graceful close
				} else if netErr, ok := err.(net.Error); ok && netErr.Timeout() {
					// Read timeout - check for shutdown and continue
					select {
					case <-s.shutdown:
						errChan <- nil
					default:
						continue // Keep reading
					}
				} else {
					log.Printf("HTTP CONNECT client read error for %s (StreamID: %s): %v", targetAddr, streamID, err)
					errChan <- err
				}
				return
			}

			if n > 0 {
				// Send to Mix Network via ProxySend (data will be Base64 encoded internally)
				_, err := s.mixBridge.ProxySend(streamID, buf[:n])
				if err != nil {
					log.Printf("HTTP CONNECT ProxySend error for %s (StreamID: %s): %v", targetAddr, streamID, err)
					errChan <- err
					return
				}
				log.Printf("HTTP CONNECT client->Mix sent %d bytes for %s (StreamID: %s)", n, targetAddr, streamID)
			}
		}
	}()

	// Goroutine 2: Mix Network -> Client
	// Receive from Mix via ProxyReceive, write to client
	go func() {
		for {
			// Check for shutdown signal
			select {
			case <-s.shutdown:
				errChan <- nil
				return
			default:
			}

			// Receive from Mix Network (max 32KB per call)
			// ProxyReceive will decode Base64 data internally
			data, eof, err := s.mixBridge.ProxyReceive(streamID, 32768)
			if err != nil {
				log.Printf("HTTP CONNECT ProxyReceive error for %s (StreamID: %s): %v", targetAddr, streamID, err)
				errChan <- err
				return
			}

			if len(data) > 0 {
				// Write to client
				if err := clientConn.SetWriteDeadline(time.Now().Add(30 * time.Second)); err != nil {
					log.Printf("HTTP CONNECT set write deadline error: %v", err)
				}
				if _, err := clientConn.Write(data); err != nil {
					log.Printf("HTTP CONNECT client write error for %s (StreamID: %s): %v", targetAddr, streamID, err)
					errChan <- err
					return
				}
				log.Printf("HTTP CONNECT Mix->client sent %d bytes for %s (StreamID: %s)", len(data), targetAddr, streamID)
			}

			if eof {
				log.Printf("HTTP CONNECT Mix->client EOF for %s (StreamID: %s)", targetAddr, streamID)
				errChan <- nil // Graceful close
				return
			}

			// If no data received and not EOF, add small delay to avoid busy loop
			if len(data) == 0 {
				time.Sleep(10 * time.Millisecond)
			}
		}
	}()

	// Wait for both directions to complete
	// First error (or nil) indicates completion of one direction
	err1 := <-errChan
	// Second error (or nil) indicates completion of other direction
	err2 := <-errChan

	// Return first non-nil error, or nil if both succeeded
	if err1 != nil {
		return err1
	}
	return err2
}

// validateHost checks if the target host:port is valid
func validateHost(hostPort string) error {
	host, portStr, err := net.SplitHostPort(hostPort)
	if err != nil {
		return fmt.Errorf("invalid host:port format: %w", err)
	}

	// Validate hostname length
	if len(host) > maxHostLength || len(host) == 0 {
		return errHTTPInvalidHost
	}

	// Validate port range
	port, err := strconv.Atoi(portStr)
	if err != nil || port < 1 || port > 65535 {
		return fmt.Errorf("invalid port: %s", portStr)
	}

	return nil
}

// sendSuccessResponse sends "HTTP/1.1 200 Connection established"
func (s *HTTPConnectServer) sendSuccessResponse(conn net.Conn) error {
	response := "HTTP/1.1 200 Connection established\r\n\r\n"
	_, err := conn.Write([]byte(response))
	return err
}

// sendErrorResponse sends HTTP error response
func (s *HTTPConnectServer) sendErrorResponse(conn net.Conn, statusCode int, message string) error {
	statusText := getHTTPStatusText(statusCode)
	response := fmt.Sprintf("HTTP/1.1 %d %s\r\nContent-Length: %d\r\n\r\n%s",
		statusCode, statusText, len(message), message)
	_, err := conn.Write([]byte(response))
	return err
}

// getHTTPStatusText returns status text for HTTP status code
func getHTTPStatusText(code int) string {
	switch code {
	case httpStatusOK:
		return "Connection established"
	case httpStatusBadRequest:
		return "Bad Request"
	case httpStatusProxyAuthRequired:
		return "Proxy Authentication Required"
	case httpStatusBadGateway:
		return "Bad Gateway"
	case httpStatusGatewayTimeout:
		return "Gateway Timeout"
	default:
		return "Unknown"
	}
}

// relay copies data bidirectionally between client and target
// Unused: replaced by relayBidirectional for Mix Network integration
// nolint:unused
func (s *HTTPConnectServer) relay(client, target net.Conn) {
	// Use buffered channels to signal completion
	done := make(chan error, 2)

	// Client → Target
	go func() {
		n, err := io.Copy(target, client)
		s.stats.BytesTransferred.Add(n)
		done <- err
	}()

	// Target → Client
	go func() {
		n, err := io.Copy(client, target)
		s.stats.BytesTransferred.Add(n)
		done <- err
	}()

	// Wait for either direction to complete
	<-done
	<-done
}

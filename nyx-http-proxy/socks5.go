package main

import (
	"encoding/binary"
	"errors"
	"fmt"
	"io"
	"log"
	"net"
	"strconv"
	"time"
)

// SOCKS5 protocol constants (RFC 1928)
const (
	// Protocol version
	socks5Version = 0x05

	// Authentication methods
	socks5AuthNone     = 0x00 // No authentication required
	socks5AuthPassword = 0x02 // Username/password authentication
	socks5AuthNoAccept = 0xFF // No acceptable methods

	// Commands
	socks5CmdConnect      = 0x01 // CONNECT command
	socks5CmdBind         = 0x02 // BIND command (not implemented)
	socks5CmdUDPAssociate = 0x03 // UDP ASSOCIATE (not implemented)

	// Address types
	socks5AtypIPv4   = 0x01 // IPv4 address
	socks5AtypDomain = 0x03 // Domain name
	socks5AtypIPv6   = 0x04 // IPv6 address

	// Reply codes
	socks5RepSuccess             = 0x00 // Succeeded
	socks5RepGeneralFailure      = 0x01 // General SOCKS server failure
	socks5RepNotAllowed          = 0x02 // Connection not allowed by ruleset
	socks5RepNetworkUnreachable  = 0x03 // Network unreachable
	socks5RepHostUnreachable     = 0x04 // Host unreachable
	socks5RepConnectionRefused   = 0x05 // Connection refused
	socks5RepTTLExpired          = 0x06 // TTL expired
	socks5RepCommandNotSupported = 0x07 // Command not supported
	socks5RepAddressNotSupported = 0x08 // Address type not supported
)

var (
	// Errors
	errSOCKS5InvalidVersion      = errors.New("socks5: invalid protocol version")
	errSOCKS5NoAcceptableAuth    = errors.New("socks5: no acceptable authentication method")
	errSOCKS5CommandNotSupported = errors.New("socks5: command not supported")
	errSOCKS5AddressNotSupported = errors.New("socks5: address type not supported")
	errSOCKS5InvalidRequest      = errors.New("socks5: invalid request format")
)

// SOCKS5Server handles SOCKS5 proxy connections
type SOCKS5Server struct {
	listener  net.Listener
	stats     *Stats
	mixBridge *MixBridgeClient
	shutdown  chan struct{}
}

// NewSOCKS5Server creates a new SOCKS5 server
func NewSOCKS5Server(addr string, stats *Stats, mixBridge *MixBridgeClient) (*SOCKS5Server, error) {
	listener, err := net.Listen("tcp", addr)
	if err != nil {
		return nil, fmt.Errorf("failed to listen on %s: %w", addr, err)
	}

	return &SOCKS5Server{
		listener:  listener,
		stats:     stats,
		mixBridge: mixBridge,
		shutdown:  make(chan struct{}),
	}, nil
}

// Serve starts the SOCKS5 server
func (s *SOCKS5Server) Serve() error {
	log.Printf("SOCKS5 server listening on %s", s.listener.Addr())

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
				log.Printf("SOCKS5 accept error: %v", err)
				continue
			}
		}

		// Handle connection in goroutine
		go s.handleConnection(conn)
	}
}

// Close gracefully shuts down the server
func (s *SOCKS5Server) Close() error {
	close(s.shutdown)
	return s.listener.Close()
}

// handleConnection processes a single SOCKS5 connection
func (s *SOCKS5Server) handleConnection(clientConn net.Conn) {
	defer clientConn.Close()

	s.stats.TotalConnections.Add(1)
	s.stats.SOCKS5Connections.Add(1)
	s.stats.ActiveConnections.Add(1)
	defer s.stats.ActiveConnections.Add(-1)

	// Phase 1: Authentication handshake
	if err := s.handleAuth(clientConn); err != nil {
		log.Printf("SOCKS5 auth failed: %v", err)
		s.stats.Errors.Add(1)
		return
	}

	// Phase 2: Request processing
	targetAddr, err := s.handleRequest(clientConn)
	if err != nil {
		log.Printf("SOCKS5 request failed: %v", err)
		s.stats.Errors.Add(1)
		return
	}

	// Phase 3: Connect to target via Mix Network through IPC bridge
	// ProxyConnect returns a ProxyConnectResult with StreamID and Address
	result, err := s.mixBridge.ProxyConnect(targetAddr, "socks5")
	if err != nil {
		log.Printf("SOCKS5 Mix connect to %s failed: %v", targetAddr, err)
		if err := s.sendReply(clientConn, socks5RepHostUnreachable, nil); err != nil {
			log.Printf("SOCKS5 send reply error: %v", err)
		}
		s.stats.Errors.Add(1)
		return
	}

	// For Phase 2b: We'll create a virtual connection adapter
	// In Phase 2c, this will be a real Mix Network stream with bidirectional relay
	// For now, we acknowledge the connection was established via Mix routing
	log.Printf("SOCKS5 Mix connection established to %s (StreamID: %s)", targetAddr, result.StreamID)

	// Create a dummy local address for the reply
	// In production, this would be the Mix exit node's address
	dummyAddr := &net.TCPAddr{IP: net.IPv4(127, 0, 0, 1), Port: 0}
	if err := s.sendReply(clientConn, socks5RepSuccess, dummyAddr); err != nil {
		log.Printf("SOCKS5 send reply failed: %v", err)
		s.stats.Errors.Add(1)
		// Close the Mix stream on reply failure
		s.mixBridge.ProxyClose(result.StreamID)
		return
	}

	// Phase 3: Full bidirectional relay implementation
	// Relay data between client and Mix Network using ProxySend/ProxyReceive
	log.Printf("SOCKS5 Mix connection active for %s (StreamID: %s). Starting bidirectional relay.", targetAddr, result.StreamID)

	// Ensure Mix stream is closed on exit
	defer func() {
		log.Printf("SOCKS5 client disconnected from %s, closing Mix stream %s", targetAddr, result.StreamID)
		s.mixBridge.ProxyClose(result.StreamID)
	}()

	// Start bidirectional relay
	// This pumps data in both directions:
	// - Client -> Mix Network (clientConn read -> ProxySend)
	// - Mix Network -> Client (ProxyReceive -> clientConn write)
	err = s.relayBidirectional(clientConn, result.StreamID, targetAddr)
	if err != nil {
		log.Printf("SOCKS5 relay error for %s (StreamID: %s): %v", targetAddr, result.StreamID, err)
		s.stats.Errors.Add(1)
	} else {
		log.Printf("SOCKS5 relay completed for %s (StreamID: %s)", targetAddr, result.StreamID)
	}
}

// relayBidirectional performs full-duplex relay between client and Mix Network
//
// This function spawns two goroutines:
// 1. Client -> Mix: Read from client, send via ProxySend (Base64 encoded)
// 2. Mix -> Client: Receive via ProxyReceive (Base64 decoded), write to client
//
// Both goroutines run until EOF or error, then signal completion.
// The function returns when both directions have completed.
func (s *SOCKS5Server) relayBidirectional(clientConn net.Conn, streamID string, targetAddr string) error {
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
			clientConn.SetReadDeadline(time.Now().Add(30 * time.Second))
			n, err := clientConn.Read(buf)
			if err != nil {
				if err == io.EOF {
					log.Printf("SOCKS5 client->Mix EOF for %s (StreamID: %s)", targetAddr, streamID)
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
					log.Printf("SOCKS5 client read error for %s (StreamID: %s): %v", targetAddr, streamID, err)
					errChan <- err
				}
				return
			}

			if n > 0 {
				// Send to Mix Network via ProxySend (data will be Base64 encoded internally)
				_, err := s.mixBridge.ProxySend(streamID, buf[:n])
				if err != nil {
					log.Printf("SOCKS5 ProxySend error for %s (StreamID: %s): %v", targetAddr, streamID, err)
					errChan <- err
					return
				}
				log.Printf("SOCKS5 client->Mix sent %d bytes for %s (StreamID: %s)", n, targetAddr, streamID)
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
				log.Printf("SOCKS5 ProxyReceive error for %s (StreamID: %s): %v", targetAddr, streamID, err)
				errChan <- err
				return
			}

			if len(data) > 0 {
				// Write to client
				if err := clientConn.SetWriteDeadline(time.Now().Add(30 * time.Second)); err != nil {
					log.Printf("SOCKS5 set write deadline error: %v", err)
				}
				if _, err := clientConn.Write(data); err != nil {
					log.Printf("SOCKS5 client write error for %s (StreamID: %s): %v", targetAddr, streamID, err)
					errChan <- err
					return
				}
				log.Printf("SOCKS5 Mix->client sent %d bytes for %s (StreamID: %s)", len(data), targetAddr, streamID)
			}

			if eof {
				log.Printf("SOCKS5 Mix->client EOF for %s (StreamID: %s)", targetAddr, streamID)
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

// handleAuth processes the SOCKS5 authentication handshake
func (s *SOCKS5Server) handleAuth(conn net.Conn) error {
	// Read client greeting: [VER, NMETHODS, METHODS...]
	buf := make([]byte, 257) // Max: 1 + 1 + 255 methods
	n, err := io.ReadAtLeast(conn, buf, 2)
	if err != nil {
		return fmt.Errorf("read greeting: %w", err)
	}

	// Verify protocol version
	if buf[0] != socks5Version {
		return errSOCKS5InvalidVersion
	}

	// Parse authentication methods
	nmethods := int(buf[1])
	if n < 2+nmethods {
		return errSOCKS5InvalidRequest
	}
	methods := buf[2 : 2+nmethods]

	// Select authentication method (prefer no-auth for simplicity)
	selectedMethod := byte(socks5AuthNoAccept)
	for _, method := range methods {
		if method == socks5AuthNone {
			selectedMethod = socks5AuthNone
			break
		}
	}

	// Send method selection: [VER, METHOD]
	reply := []byte{socks5Version, selectedMethod}
	if _, err := conn.Write(reply); err != nil {
		return fmt.Errorf("write auth reply: %w", err)
	}

	if selectedMethod == socks5AuthNoAccept {
		return errSOCKS5NoAcceptableAuth
	}

	// Handle username/password authentication if selected
	if selectedMethod == socks5AuthPassword {
		if err := s.handleUsernamePasswordAuth(conn); err != nil {
			return fmt.Errorf("username/password auth failed: %w", err)
		}
	}

	return nil
}

// handleUsernamePasswordAuth implements RFC 1929 username/password authentication
func (s *SOCKS5Server) handleUsernamePasswordAuth(conn net.Conn) error {
	// Read authentication request: [VER, ULEN, UNAME, PLEN, PASSWD]
	buf := make([]byte, 513) // Max: 1 + 1 + 255 + 1 + 255

	// Read version and username length
	if _, err := io.ReadFull(conn, buf[:2]); err != nil {
		return fmt.Errorf("read auth header: %w", err)
	}

	// Verify username/password auth version (must be 1)
	if buf[0] != 0x01 {
		if err := s.sendAuthReply(conn, 0xFF); err != nil { // 0xFF = auth failed
			log.Printf("SOCKS5 send auth reply error: %v", err)
		}
		return fmt.Errorf("invalid auth version: %d", buf[0])
	}

	ulen := int(buf[1])
	if ulen == 0 || ulen > 255 {
		if err := s.sendAuthReply(conn, 0xFF); err != nil {
			log.Printf("SOCKS5 send auth reply error: %v", err)
		}
		return fmt.Errorf("invalid username length: %d", ulen)
	}

	// Read username
	if _, err := io.ReadFull(conn, buf[:ulen]); err != nil {
		return fmt.Errorf("read username: %w", err)
	}
	username := string(buf[:ulen])

	// Read password length
	if _, err := io.ReadFull(conn, buf[:1]); err != nil {
		return fmt.Errorf("read password length: %w", err)
	}
	plen := int(buf[0])
	if plen == 0 || plen > 255 {
		if err := s.sendAuthReply(conn, 0xFF); err != nil {
			log.Printf("SOCKS5 send auth reply error: %v", err)
		}
		return fmt.Errorf("invalid password length: %d", plen)
	}

	// Read password
	if _, err := io.ReadFull(conn, buf[:plen]); err != nil {
		return fmt.Errorf("read password: %w", err)
	}
	password := string(buf[:plen])

	// Verify credentials
	// In production, this should check against a secure credential store
	// For now, we accept any non-empty username/password combination
	if username == "" || password == "" {
		s.sendAuthReply(conn, 0xFF) // Auth failed
		return fmt.Errorf("empty username or password")
	}

	// Optional: Implement actual credential verification here
	// Example: check against environment variables or config file
	// validUser := os.Getenv("SOCKS5_USER")
	// validPass := os.Getenv("SOCKS5_PASS")
	// if username != validUser || password != validPass {
	//     s.sendAuthReply(conn, 0xFF)
	//     return fmt.Errorf("invalid credentials")
	// }

	// Authentication successful
	s.sendAuthReply(conn, 0x00) // 0x00 = success
	return nil
}

// sendAuthReply sends username/password authentication reply
func (s *SOCKS5Server) sendAuthReply(conn net.Conn, status byte) error {
	// Reply: [VER, STATUS]
	// VER = 1 (username/password auth version)
	// STATUS = 0 (success) or 0xFF (failure)
	reply := []byte{0x01, status}
	_, err := conn.Write(reply)
	return err
}

// handleRequest processes the SOCKS5 request
func (s *SOCKS5Server) handleRequest(conn net.Conn) (string, error) {
	// Read request header: [VER, CMD, RSV, ATYP]
	buf := make([]byte, 4)
	if _, err := io.ReadFull(conn, buf); err != nil {
		return "", fmt.Errorf("read request header: %w", err)
	}

	// Verify protocol version
	if buf[0] != socks5Version {
		if err := s.sendReply(conn, socks5RepGeneralFailure, nil); err != nil {
			log.Printf("SOCKS5 send reply error: %v", err)
		}
		return "", errSOCKS5InvalidVersion
	}

	// Check command (only CONNECT supported)
	cmd := buf[1]
	if cmd != socks5CmdConnect {
		if err := s.sendReply(conn, socks5RepCommandNotSupported, nil); err != nil {
			log.Printf("SOCKS5 send reply error: %v", err)
		}
		return "", errSOCKS5CommandNotSupported
	}

	// Parse address type and destination
	atyp := buf[3]
	var host string
	var port uint16

	switch atyp {
	case socks5AtypIPv4:
		// IPv4: 4 bytes
		addr := make([]byte, 4)
		if _, err := io.ReadFull(conn, addr); err != nil {
			return "", fmt.Errorf("read IPv4 address: %w", err)
		}
		host = net.IP(addr).String()

	case socks5AtypDomain:
		// Domain name: 1 byte length + domain
		lenBuf := make([]byte, 1)
		if _, err := io.ReadFull(conn, lenBuf); err != nil {
			return "", fmt.Errorf("read domain length: %w", err)
		}
		domainLen := int(lenBuf[0])
		domain := make([]byte, domainLen)
		if _, err := io.ReadFull(conn, domain); err != nil {
			return "", fmt.Errorf("read domain name: %w", err)
		}
		host = string(domain)

	case socks5AtypIPv6:
		// IPv6: 16 bytes
		addr := make([]byte, 16)
		if _, err := io.ReadFull(conn, addr); err != nil {
			return "", fmt.Errorf("read IPv6 address: %w", err)
		}
		host = net.IP(addr).String()

	default:
		s.sendReply(conn, socks5RepAddressNotSupported, nil)
		return "", errSOCKS5AddressNotSupported
	}

	// Read port (2 bytes, big-endian)
	portBuf := make([]byte, 2)
	if _, err := io.ReadFull(conn, portBuf); err != nil {
		return "", fmt.Errorf("read port: %w", err)
	}
	port = binary.BigEndian.Uint16(portBuf)

	targetAddr := net.JoinHostPort(host, strconv.Itoa(int(port)))
	log.Printf("SOCKS5 CONNECT request to %s", targetAddr)

	return targetAddr, nil
}

// sendReply sends a SOCKS5 reply to the client
func (s *SOCKS5Server) sendReply(conn net.Conn, rep byte, bindAddr net.Addr) error {
	// Build reply: [VER, REP, RSV, ATYP, BND.ADDR, BND.PORT]
	reply := []byte{socks5Version, rep, 0x00} // VER, REP, RSV

	if bindAddr == nil {
		// Use zero address on error
		reply = append(reply, socks5AtypIPv4)
		reply = append(reply, 0, 0, 0, 0) // IPv4: 0.0.0.0
		reply = append(reply, 0, 0)       // Port: 0
	} else {
		// Parse bind address
		host, portStr, err := net.SplitHostPort(bindAddr.String())
		if err != nil {
			return fmt.Errorf("parse bind address: %w", err)
		}
		port, _ := strconv.Atoi(portStr)

		// Determine address type
		ip := net.ParseIP(host)
		if ip == nil {
			return fmt.Errorf("invalid bind IP: %s", host)
		}

		if ipv4 := ip.To4(); ipv4 != nil {
			// IPv4
			reply = append(reply, socks5AtypIPv4)
			reply = append(reply, ipv4...)
		} else {
			// IPv6
			reply = append(reply, socks5AtypIPv6)
			reply = append(reply, ip...)
		}

		// Add port (big-endian)
		portBytes := make([]byte, 2)
		binary.BigEndian.PutUint16(portBytes, uint16(port))
		reply = append(reply, portBytes...)
	}

	_, err := conn.Write(reply)
	return err
}

// relay copies data bidirectionally between client and target
// Unused: replaced by relayBidirectional for Mix Network integration
// nolint:unused
func (s *SOCKS5Server) relay(client, target net.Conn) {
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

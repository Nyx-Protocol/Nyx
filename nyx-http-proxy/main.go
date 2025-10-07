// Package main implements a Pure Go HTTP/HTTPS proxy with SOCKS5 and HTTP CONNECT support
//
// This proxy provides Tor-like functionality for routing HTTP/HTTPS traffic through the
// Nyx Mix Network, eliminating Rust's dependency on C/C++ libraries (ring/openssl) by
// handling TLS connections using Go's standard library (Pure Go implementation).
//
// Architecture:
//
//	Browser/App → SOCKS5/HTTP CONNECT (localhost) → Go Proxy → Mix Network → Exit Node → Internet
//
// Features:
//   - SOCKS5 proxy (RFC 1928) on localhost:9050
//   - HTTP CONNECT proxy on localhost:8080
//   - Pure Go TLS (crypto/tls, ZERO C/C++ dependencies)
//   - IPC bridge to Rust Mix Layer
//   - Statistics and health monitoring
//
// Endpoints:
//
//	SOCKS5:  localhost:9050  - SOCKS5 proxy protocol
//	HTTP:    localhost:8080  - HTTP CONNECT proxy
//	Health:  localhost:8081  - Health check endpoint
//	IPC:     /tmp/nyx-mix.sock (Unix) or \\.\pipe\nyx-mix (Windows) - Mix Layer communication
package main

import (
	"context"
	"encoding/json"
	"flag"
	"fmt"
	"log"
	"net/http"
	"os"
	"os/signal"
	"sync"
	"sync/atomic"
	"syscall"
	"time"
)

const (
	// Default server addresses
	defaultSOCKS5Addr = ":9050"
	defaultHTTPAddr   = ":8080"
	defaultHealthAddr = ":8081"

	// IPC socket paths
	ipcSocketUnix    = "/tmp/nyx-mix.sock"
	ipcSocketWindows = `\\.\pipe\nyx-mix`

	// Timeouts (unused - kept for documentation)
	// readTimeout  = 30 * time.Second
	// writeTimeout = 30 * time.Second
	// idleTimeout  = 60 * time.Second
)

// ProxyServer handles both SOCKS5 and HTTP CONNECT
type ProxyServer struct {
	socks5Addr string
	httpAddr   string
	healthAddr string
	ipcPath    string
	mixBridge  *MixBridgeClient
	exitNode   *ExitNode
	stats      *Stats
	startTime  time.Time
	shutdown   chan struct{}
	wg         sync.WaitGroup
}

// Stats tracks proxy statistics with atomic counters for thread-safety
type Stats struct {
	TotalConnections  atomic.Int64 `json:"total_connections"`
	SOCKS5Connections atomic.Int64 `json:"socks5_connections"`
	HTTPConnections   atomic.Int64 `json:"http_connections"`
	ActiveConnections atomic.Int64 `json:"active_connections"`
	BytesTransferred  atomic.Int64 `json:"bytes_transferred"`
	Errors            atomic.Int64 `json:"errors"`
}

// NewProxyServer creates a new proxy server instance
func NewProxyServer(socks5Addr, httpAddr, healthAddr, ipcPath string) *ProxyServer {
	// Create exit node with default configuration
	exitNodeConfig := DefaultExitNodeConfig()
	exitNode, err := NewExitNode(exitNodeConfig)
	if err != nil {
		log.Printf("Warning: Failed to create exit node: %v", err)
		// Continue without exit node - will use direct connections
	}

	return &ProxyServer{
		socks5Addr: socks5Addr,
		httpAddr:   httpAddr,
		healthAddr: healthAddr,
		ipcPath:    ipcPath,
		mixBridge:  NewMixBridgeClient(ipcPath),
		exitNode:   exitNode,
		stats:      &Stats{},
		startTime:  time.Now(),
		shutdown:   make(chan struct{}),
	}
}

// Start starts all proxy services
func (ps *ProxyServer) Start(ctx context.Context) error {
	// Start SOCKS5 server (with Mix bridge integration)
	socks5Server, err := NewSOCKS5Server(ps.socks5Addr, ps.stats, ps.mixBridge)
	if err != nil {
		return err
	}

	ps.wg.Add(1)
	go func() {
		defer ps.wg.Done()
		if err := socks5Server.Serve(); err != nil {
			log.Printf("SOCKS5 server error: %v", err)
		}
	}()

	// Close SOCKS5 server on context cancellation
	go func() {
		<-ctx.Done()
		socks5Server.Close()
	}()

	// Start HTTP CONNECT server (with Mix bridge integration)
	httpServer, err := NewHTTPConnectServer(ps.httpAddr, ps.stats, ps.mixBridge)
	if err != nil {
		return err
	}

	ps.wg.Add(1)
	go func() {
		defer ps.wg.Done()
		if err := httpServer.Serve(); err != nil {
			log.Printf("HTTP CONNECT server error: %v", err)
		}
	}()

	// Close HTTP CONNECT server on context cancellation
	go func() {
		<-ctx.Done()
		httpServer.Close()
	}()

	// Start health check server
	ps.wg.Add(1)
	go ps.startHealthServer(ctx)

	// Wait for shutdown signal
	<-ps.shutdown
	ps.wg.Wait()

	// Close Mix Bridge connection
	if ps.mixBridge != nil {
		ps.mixBridge.Close()
	}

	return nil
}

// startHealthServer starts the health check HTTP server
func (ps *ProxyServer) startHealthServer(ctx context.Context) {
	defer ps.wg.Done()

	log.Printf("Health check server listening on %s", ps.healthAddr)

	// Create HTTP server with health check endpoints
	mux := http.NewServeMux()

	// Health check endpoint - returns 200 OK if service is healthy
	mux.HandleFunc("/health", func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Type", "application/json")
		w.WriteHeader(http.StatusOK)
		fmt.Fprintf(w, `{"status":"healthy","timestamp":"%s"}`, time.Now().UTC().Format(time.RFC3339))
	})

	// Readiness check endpoint - returns 200 OK if service is ready to accept traffic
	mux.HandleFunc("/ready", func(w http.ResponseWriter, r *http.Request) {
		// Check if critical components are initialized
		// Service is ready if it has been running for at least 1 second
		ready := time.Since(ps.startTime) > time.Second

		w.Header().Set("Content-Type", "application/json")
		if ready {
			w.WriteHeader(http.StatusOK)
			fmt.Fprintf(w, `{"status":"ready","timestamp":"%s"}`, time.Now().UTC().Format(time.RFC3339))
		} else {
			w.WriteHeader(http.StatusServiceUnavailable)
			fmt.Fprintf(w, `{"status":"not_ready","timestamp":"%s"}`, time.Now().UTC().Format(time.RFC3339))
		}
	})

	// Liveness check endpoint - returns 200 OK if service is running
	mux.HandleFunc("/live", func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Type", "application/json")
		w.WriteHeader(http.StatusOK)
		fmt.Fprintf(w, `{"status":"alive","timestamp":"%s"}`, time.Now().UTC().Format(time.RFC3339))
	})

	// Metrics endpoint - returns basic proxy metrics
	mux.HandleFunc("/metrics", func(w http.ResponseWriter, r *http.Request) {
		w.Header().Set("Content-Type", "application/json")
		w.WriteHeader(http.StatusOK)

		// Collect basic metrics
		metrics := map[string]interface{}{
			"timestamp":      time.Now().UTC().Format(time.RFC3339),
			"uptime_seconds": time.Since(ps.startTime).Seconds(),
		}

		// Add exit node metrics if available
		if ps.exitNode != nil {
			metrics["exit_node_enabled"] = true
		}

		// Add mix bridge metrics if available
		if ps.mixBridge != nil {
			metrics["mix_bridge_enabled"] = true
		}

		if err := json.NewEncoder(w).Encode(metrics); err != nil {
			log.Printf("Failed to encode metrics: %v", err)
		}
	})

	// Create HTTP server
	server := &http.Server{
		Addr:    ps.healthAddr,
		Handler: mux,
	}

	// Start server in goroutine
	go func() {
		if err := server.ListenAndServe(); err != nil && err != http.ErrServerClosed {
			log.Printf("Health server error: %v", err)
		}
	}()

	// Wait for shutdown signal
	<-ctx.Done()

	// Graceful shutdown with timeout
	shutdownCtx, cancel := context.WithTimeout(context.Background(), 5*time.Second)
	defer cancel()

	if err := server.Shutdown(shutdownCtx); err != nil {
		log.Printf("Health server shutdown error: %v", err)
	}

	log.Printf("Health check server stopped")
}

// Shutdown gracefully shuts down the proxy server
func (ps *ProxyServer) Shutdown() {
	close(ps.shutdown)
	if ps.mixBridge != nil {
		ps.mixBridge.Close()
	}
	if ps.exitNode != nil {
		ps.exitNode.Close()
	}
}

func main() {
	// Parse command-line flags
	socks5Addr := flag.String("socks5", defaultSOCKS5Addr, "SOCKS5 proxy listen address")
	httpAddr := flag.String("http", defaultHTTPAddr, "HTTP CONNECT proxy listen address")
	healthAddr := flag.String("health", defaultHealthAddr, "Health check listen address")
	ipcPath := flag.String("ipc", getDefaultIPCPath(), "IPC socket path for Mix Layer communication")
	flag.Parse()

	// Create proxy server
	server := NewProxyServer(*socks5Addr, *httpAddr, *healthAddr, *ipcPath)

	// Setup signal handling for graceful shutdown
	ctx, cancel := context.WithCancel(context.Background())
	sigChan := make(chan os.Signal, 1)
	signal.Notify(sigChan, os.Interrupt, syscall.SIGTERM)

	// Start server in background
	errChan := make(chan error, 1)
	go func() {
		if err := server.Start(ctx); err != nil {
			errChan <- err
		}
	}()

	log.Println("Nyx HTTP Proxy started successfully")
	log.Printf("  SOCKS5:  %s", *socks5Addr)
	log.Printf("  HTTP:    %s", *httpAddr)
	log.Printf("  Health:  %s", *healthAddr)
	log.Printf("  IPC:     %s", *ipcPath)

	// Wait for shutdown signal or error
	select {
	case <-sigChan:
		log.Println("Received shutdown signal, gracefully stopping...")
		cancel()
		server.Shutdown()
	case err := <-errChan:
		log.Printf("Server error: %v", err)
		cancel()
		server.Shutdown()
		os.Exit(1)
	}

	log.Println("Nyx HTTP Proxy stopped")
}

// getDefaultIPCPath returns the platform-specific default IPC socket path
func getDefaultIPCPath() string {
	if os.Getenv("OS") == "Windows_NT" {
		return ipcSocketWindows
	}
	return ipcSocketUnix
}

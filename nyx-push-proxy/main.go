// Package main implements a Pure Go HTTPS proxy for push notification services
//
// This proxy eliminates Rust's dependency on ring/openssl C/C++ libraries by handling
// TLS connections using Go's standard library (Pure Go implementation).
//
// Architecture:
//
//	Rust nyx-daemon → HTTP (localhost:8765) → Go Proxy → HTTPS → FCM/APNS/WebPush
//
// Endpoints:
//
//	POST /fcm       - Firebase Cloud Messaging
//	POST /apns      - Apple Push Notification Service
//	POST /webpush   - Web Push
//	GET  /health    - Health check
package main

import (
	"bytes"
	"context"
	"crypto/tls"
	"encoding/json"
	"fmt"
	"io"
	"log"
	"net/http"
	"os"
	"os/signal"
	"syscall"
	"time"

	"github.com/golang-jwt/jwt/v5"
	"golang.org/x/oauth2/google"
)

const (
	// Server configuration
	serverAddr    = ":8765"
	readTimeout   = 30 * time.Second
	writeTimeout  = 30 * time.Second
	idleTimeout   = 60 * time.Second
	maxHeaderSize = 1 << 20 // 1 MB
)

// ProxyServer handles push notification proxying with TLS termination
type ProxyServer struct {
	httpClient *http.Client
	stats      *Stats
}

// Stats tracks proxy statistics
type Stats struct {
	TotalRequests   int64 `json:"total_requests"`
	FCMRequests     int64 `json:"fcm_requests"`
	APNSRequests    int64 `json:"apns_requests"`
	WebPushRequests int64 `json:"webpush_requests"`
	Errors          int64 `json:"errors"`
}

// FCMRequest represents an FCM proxy request from Rust
type FCMRequest struct {
	ServiceAccountJSON string                 `json:"service_account_json"`
	ProjectID          string                 `json:"project_id"`
	Token              string                 `json:"token"`
	Notification       map[string]interface{} `json:"notification"`
}

// APNSRequest represents an APNS proxy request from Rust
type APNSRequest struct {
	KeyPEM  string                 `json:"key_pem"`
	KeyID   string                 `json:"key_id"`
	TeamID  string                 `json:"team_id"`
	Topic   string                 `json:"topic"`
	Sandbox bool                   `json:"sandbox"`
	Token   string                 `json:"token"`
	Payload map[string]interface{} `json:"payload"`
}

// WebPushRequest represents a WebPush proxy request from Rust
type WebPushRequest struct {
	Endpoint        string                 `json:"endpoint"`
	VAPIDPublicKey  string                 `json:"vapid_public_key"`
	VAPIDPrivateKey string                 `json:"vapid_private_key"`
	ContactEmail    string                 `json:"contact_email"`
	Payload         map[string]interface{} `json:"payload"`
}

// NewProxyServer creates a new proxy server instance
func NewProxyServer() *ProxyServer {
	// Configure TLS with Go's standard library (Pure Go)
	tlsConfig := &tls.Config{
		MinVersion: tls.VersionTLS12,
	}

	transport := &http.Transport{
		TLSClientConfig:     tlsConfig,
		MaxIdleConns:        100,
		MaxIdleConnsPerHost: 10,
		IdleConnTimeout:     90 * time.Second,
	}

	return &ProxyServer{
		httpClient: &http.Client{
			Transport: transport,
			Timeout:   30 * time.Second,
		},
		stats: &Stats{},
	}
}

// handleFCM proxies FCM requests with OAuth2 token acquisition
func (s *ProxyServer) handleFCM(w http.ResponseWriter, r *http.Request) {
	s.stats.TotalRequests++
	s.stats.FCMRequests++

	var req FCMRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		s.stats.Errors++
		http.Error(w, fmt.Sprintf("Invalid request: %v", err), http.StatusBadRequest)
		return
	}

	// Parse service account credentials
	creds, err := google.CredentialsFromJSON(
		context.Background(),
		[]byte(req.ServiceAccountJSON),
		"https://www.googleapis.com/auth/firebase.messaging",
	)
	if err != nil {
		s.stats.Errors++
		http.Error(w, fmt.Sprintf("Invalid service account: %v", err), http.StatusBadRequest)
		return
	}

	// Get OAuth2 token
	token, err := creds.TokenSource.Token()
	if err != nil {
		s.stats.Errors++
		http.Error(w, fmt.Sprintf("Failed to get OAuth2 token: %v", err), http.StatusInternalServerError)
		return
	}

	// Construct FCM message
	fcmMessage := map[string]interface{}{
		"message": map[string]interface{}{
			"token":        req.Token,
			"notification": req.Notification,
		},
	}

	fcmPayload, err := json.Marshal(fcmMessage)
	if err != nil {
		s.stats.Errors++
		http.Error(w, fmt.Sprintf("Failed to marshal payload: %v", err), http.StatusInternalServerError)
		return
	}

	// Send to FCM API
	fcmURL := fmt.Sprintf("https://fcm.googleapis.com/v1/projects/%s/messages:send", req.ProjectID)
	fcmReq, err := http.NewRequest("POST", fcmURL, bytes.NewReader(fcmPayload))
	if err != nil {
		s.stats.Errors++
		http.Error(w, fmt.Sprintf("Failed to create request: %v", err), http.StatusInternalServerError)
		return
	}

	fcmReq.Header.Set("Authorization", "Bearer "+token.AccessToken)
	fcmReq.Header.Set("Content-Type", "application/json")

	resp, err := s.httpClient.Do(fcmReq)
	if err != nil {
		s.stats.Errors++
		http.Error(w, fmt.Sprintf("FCM request failed: %v", err), http.StatusBadGateway)
		return
	}
	defer resp.Body.Close()

	// Copy FCM response back to Rust
	w.WriteHeader(resp.StatusCode)
	io.Copy(w, resp.Body)
}

// handleAPNS proxies APNS requests with JWT token generation
func (s *ProxyServer) handleAPNS(w http.ResponseWriter, r *http.Request) {
	s.stats.TotalRequests++
	s.stats.APNSRequests++

	var req APNSRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		s.stats.Errors++
		http.Error(w, fmt.Sprintf("Invalid request: %v", err), http.StatusBadRequest)
		return
	}

	// Parse EC private key
	key, err := jwt.ParseECPrivateKeyFromPEM([]byte(req.KeyPEM))
	if err != nil {
		s.stats.Errors++
		http.Error(w, fmt.Sprintf("Invalid APNS key: %v", err), http.StatusBadRequest)
		return
	}

	// Generate JWT token
	now := time.Now()
	token := jwt.NewWithClaims(jwt.SigningMethodES256, jwt.MapClaims{
		"iss": req.TeamID,
		"iat": now.Unix(),
	})
	token.Header["kid"] = req.KeyID

	tokenString, err := token.SignedString(key)
	if err != nil {
		s.stats.Errors++
		http.Error(w, fmt.Sprintf("Failed to sign JWT: %v", err), http.StatusInternalServerError)
		return
	}

	// Construct APNS payload
	apnsPayload, err := json.Marshal(req.Payload)
	if err != nil {
		s.stats.Errors++
		http.Error(w, fmt.Sprintf("Failed to marshal payload: %v", err), http.StatusInternalServerError)
		return
	}

	// Choose APNS host
	host := "api.push.apple.com"
	if req.Sandbox {
		host = "api.sandbox.push.apple.com"
	}

	// Send to APNS
	apnsURL := fmt.Sprintf("https://%s/3/device/%s", host, req.Token)
	apnsReq, err := http.NewRequest("POST", apnsURL, bytes.NewReader(apnsPayload))
	if err != nil {
		s.stats.Errors++
		http.Error(w, fmt.Sprintf("Failed to create request: %v", err), http.StatusInternalServerError)
		return
	}

	apnsReq.Header.Set("authorization", "bearer "+tokenString)
	apnsReq.Header.Set("apns-topic", req.Topic)
	apnsReq.Header.Set("apns-push-type", "alert")
	apnsReq.Header.Set("apns-priority", "10")

	resp, err := s.httpClient.Do(apnsReq)
	if err != nil {
		s.stats.Errors++
		http.Error(w, fmt.Sprintf("APNS request failed: %v", err), http.StatusBadGateway)
		return
	}
	defer resp.Body.Close()

	// Copy APNS response back to Rust
	w.WriteHeader(resp.StatusCode)
	io.Copy(w, resp.Body)
}

// handleWebPush proxies WebPush requests with VAPID signature
func (s *ProxyServer) handleWebPush(w http.ResponseWriter, r *http.Request) {
	s.stats.TotalRequests++
	s.stats.WebPushRequests++

	var req WebPushRequest
	if err := json.NewDecoder(r.Body).Decode(&req); err != nil {
		s.stats.Errors++
		http.Error(w, fmt.Sprintf("Invalid request: %v", err), http.StatusBadRequest)
		return
	}

	// Parse VAPID private key
	key, err := jwt.ParseECPrivateKeyFromPEM([]byte(req.VAPIDPrivateKey))
	if err != nil {
		s.stats.Errors++
		http.Error(w, fmt.Sprintf("Invalid VAPID key: %v", err), http.StatusBadRequest)
		return
	}

	// Generate VAPID JWT
	now := time.Now()
	token := jwt.NewWithClaims(jwt.SigningMethodES256, jwt.MapClaims{
		"aud": req.Endpoint,
		"exp": now.Add(12 * time.Hour).Unix(),
		"sub": "mailto:" + req.ContactEmail,
	})

	tokenString, err := token.SignedString(key)
	if err != nil {
		s.stats.Errors++
		http.Error(w, fmt.Sprintf("Failed to sign VAPID JWT: %v", err), http.StatusInternalServerError)
		return
	}

	// Construct WebPush payload
	webpushPayload, err := json.Marshal(req.Payload)
	if err != nil {
		s.stats.Errors++
		http.Error(w, fmt.Sprintf("Failed to marshal payload: %v", err), http.StatusInternalServerError)
		return
	}

	// Send to WebPush endpoint
	webpushReq, err := http.NewRequest("POST", req.Endpoint, bytes.NewReader(webpushPayload))
	if err != nil {
		s.stats.Errors++
		http.Error(w, fmt.Sprintf("Failed to create request: %v", err), http.StatusInternalServerError)
		return
	}

	webpushReq.Header.Set("Content-Type", "application/octet-stream")
	webpushReq.Header.Set("Authorization", fmt.Sprintf("vapid t=%s, k=%s", tokenString, req.VAPIDPublicKey))
	webpushReq.Header.Set("TTL", "86400")

	resp, err := s.httpClient.Do(webpushReq)
	if err != nil {
		s.stats.Errors++
		http.Error(w, fmt.Sprintf("WebPush request failed: %v", err), http.StatusBadGateway)
		return
	}
	defer resp.Body.Close()

	// Copy WebPush response back to Rust
	w.WriteHeader(resp.StatusCode)
	io.Copy(w, resp.Body)
}

// handleHealth returns server health and statistics
func (s *ProxyServer) handleHealth(w http.ResponseWriter, r *http.Request) {
	w.Header().Set("Content-Type", "application/json")
	json.NewEncoder(w).Encode(map[string]interface{}{
		"status": "healthy",
		"stats":  s.stats,
	})
}

// Run starts the proxy server
func (s *ProxyServer) Run() error {
	mux := http.NewServeMux()
	mux.HandleFunc("/fcm", s.handleFCM)
	mux.HandleFunc("/apns", s.handleAPNS)
	mux.HandleFunc("/webpush", s.handleWebPush)
	mux.HandleFunc("/health", s.handleHealth)

	server := &http.Server{
		Addr:           serverAddr,
		Handler:        mux,
		ReadTimeout:    readTimeout,
		WriteTimeout:   writeTimeout,
		IdleTimeout:    idleTimeout,
		MaxHeaderBytes: maxHeaderSize,
	}

	// Graceful shutdown
	done := make(chan struct{})
	go func() {
		sigint := make(chan os.Signal, 1)
		signal.Notify(sigint, os.Interrupt, syscall.SIGTERM)
		<-sigint

		log.Println("Shutting down proxy server...")
		ctx, cancel := context.WithTimeout(context.Background(), 10*time.Second)
		defer cancel()

		if err := server.Shutdown(ctx); err != nil {
			log.Printf("Server shutdown error: %v\n", err)
		}
		close(done)
	}()

	log.Printf("Nyx Push Proxy listening on %s (Pure Go TLS)\n", serverAddr)
	if err := server.ListenAndServe(); err != http.ErrServerClosed {
		return fmt.Errorf("server error: %w", err)
	}

	<-done
	log.Println("Server stopped gracefully")
	return nil
}

func main() {
	proxy := NewProxyServer()
	if err := proxy.Run(); err != nil {
		log.Fatal(err)
	}
}

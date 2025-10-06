# Nyx Push Proxy

**Pure Go HTTPS proxy for push notification services**

Eliminates Rust's dependency on `ring`/OpenSSL C/C++ libraries by handling TLS connections with Go's standard library (100% Pure Go implementation).

## Architecture

```
Rust nyx-daemon
    ↓ HTTP (localhost:8765)
Go Push Proxy (Pure Go TLS)
    ↓ HTTPS (TLS via Go stdlib)
FCM / APNS / WebPush APIs
```

## Features

- ✅ **Zero C/C++ Dependencies**: Pure Go implementation
- ✅ **TLS Termination**: Go's `crypto/tls` (Pure Go)
- ✅ **FCM Support**: OAuth2 token management + HTTP v1 API
- ✅ **APNS Support**: JWT token generation + HTTP/2
- ✅ **WebPush Support**: VAPID signature generation
- ✅ **Health Checks**: `/health` endpoint with statistics
- ✅ **Graceful Shutdown**: Signal handling with context cancellation

## API Endpoints

### POST /fcm
Firebase Cloud Messaging proxy

**Request:**
```json
{
  "service_account_json": "{ ... service account JSON ... }",
  "project_id": "my-firebase-project",
  "token": "fcm-device-token",
  "notification": {
    "title": "Hello",
    "body": "World"
  }
}
```

**Response:** FCM API response (200 OK or error)

### POST /apns
Apple Push Notification Service proxy

**Request:**
```json
{
  "key_pem": "-----BEGIN PRIVATE KEY-----\n...",
  "key_id": "ABCDE12345",
  "team_id": "TEAM123456",
  "topic": "com.example.app",
  "sandbox": false,
  "token": "apns-device-token-64-hex",
  "payload": {
    "aps": {
      "alert": {
        "title": "Hello",
        "body": "World"
      }
    }
  }
}
```

**Response:** APNS API response (200 OK or error)

### POST /webpush
Web Push proxy

**Request:**
```json
{
  "endpoint": "https://fcm.googleapis.com/fcm/send/...",
  "vapid_public_key": "BPublicKey...",
  "vapid_private_key": "-----BEGIN PRIVATE KEY-----\n...",
  "contact_email": "admin@example.com",
  "payload": {
    "title": "Hello",
    "body": "World"
  }
}
```

**Response:** WebPush endpoint response (201 Created or error)

### GET /health
Health check and statistics

**Response:**
```json
{
  "status": "healthy",
  "stats": {
    "total_requests": 1234,
    "fcm_requests": 500,
    "apns_requests": 400,
    "webpush_requests": 334,
    "errors": 0
  }
}
```

## Usage

### Build
```bash
go build -o nyx-push-proxy main.go
```

### Run
```bash
./nyx-push-proxy
```

Server listens on `localhost:8765` by default.

### Docker
```bash
docker build -t nyx-push-proxy .
docker run -p 8765:8765 nyx-push-proxy
```

### Kubernetes Sidecar
```yaml
apiVersion: v1
kind: Pod
metadata:
  name: nyx-daemon
spec:
  containers:
  - name: nyx-daemon
    image: nyx-daemon:latest
    env:
    - name: PUSH_PROXY_URL
      value: "http://localhost:8765"
  - name: push-proxy
    image: nyx-push-proxy:latest
    ports:
    - containerPort: 8765
```

## Configuration

Environment variables (optional):
- `PORT`: Server port (default: 8765)
- `READ_TIMEOUT`: HTTP read timeout (default: 30s)
- `WRITE_TIMEOUT`: HTTP write timeout (default: 30s)

## Development

### Run tests
```bash
go test -v ./...
```

### Format code
```bash
go fmt ./...
```

### Lint
```bash
golangci-lint run
```

## Security Considerations

1. **Localhost Only**: Bind to `127.0.0.1:8765` to prevent external access
2. **Credential Handling**: Service accounts and keys are passed per-request (not stored)
3. **TLS Verification**: Go's `crypto/tls` verifies all upstream certificates
4. **Timeout Protection**: All requests have 30s timeout

## Performance

- **Connection Pooling**: Reuses HTTP/2 connections to FCM/APNS/WebPush
- **Idle Connections**: Max 100 idle connections, 10 per host
- **Concurrency**: Handles concurrent requests with Go's goroutines

## License

MIT OR Apache-2.0 (same as Nyx project)

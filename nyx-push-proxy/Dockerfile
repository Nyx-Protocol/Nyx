# Build stage
FROM golang:1.21-alpine AS builder

WORKDIR /build

# Copy go mod files
COPY go.mod go.sum ./
RUN go mod download

# Copy source code
COPY main.go ./

# Build binary (static linking)
RUN CGO_ENABLED=0 GOOS=linux GOARCH=amd64 go build \
    -ldflags="-w -s" \
    -o nyx-push-proxy \
    main.go

# Runtime stage
FROM alpine:3.19

# Add ca-certificates for TLS
RUN apk --no-cache add ca-certificates

WORKDIR /app

# Copy binary from builder
COPY --from=builder /build/nyx-push-proxy /app/nyx-push-proxy

# Non-root user
RUN adduser -D -u 1000 proxy && \
    chown -R proxy:proxy /app
USER proxy

# Expose proxy port
EXPOSE 8765

# Health check
HEALTHCHECK --interval=30s --timeout=3s --start-period=5s --retries=3 \
    CMD wget --no-verbose --tries=1 --spider http://localhost:8765/health || exit 1

# Run proxy
ENTRYPOINT ["/app/nyx-push-proxy"]

# Build stage
FROM golang:1.23-alpine AS builder

WORKDIR /build

# Copy go mod files
COPY go.mod go.sum ./
RUN go mod download

# Copy source code
COPY *.go ./

# Build with optimizations
RUN CGO_ENABLED=0 GOOS=linux go build -ldflags="-w -s" -o nyx-http-proxy .

# Runtime stage
FROM alpine:latest

RUN apk --no-cache add ca-certificates

WORKDIR /app

# Copy binary from builder
COPY --from=builder /build/nyx-http-proxy .

# Expose ports
EXPOSE 9050 8080 8081

# Run as non-root user
RUN addgroup -S nyx && adduser -S nyx -G nyx
USER nyx

ENTRYPOINT ["./nyx-http-proxy"]
CMD ["-socks5", ":9050", "-http", ":8080", "-health", ":8081"]

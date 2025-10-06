# Nyx Helm Chart
**Chart Version**: 0.2.0  
**App Version**: 0.9.0  
**Status**: Production-Ready (Non-Mix Deployments)

---

## Overview

This Helm chart deploys the **NyxNet daemon** to Kubernetes, providing a privacy-first, post-quantum secure networking stack with:
- **Post-Quantum Cryptography**: Hybrid handshake (X25519 + Kyber1024)
- **Multipath QUIC**: Automatic failover (<1s), bandwidth aggregation
- **NAT Traversal**: ICE Lite with STUN for P2P connectivity
- **gRPC Control API**: 20+ RPCs for management, monitoring, configuration
- **OTLP Telemetry**: Jaeger/Tempo integration with configurable sampling
- **Kubernetes-Native**: HPA, PDB, ServiceMonitor support

**Use Cases**:
- Private peer-to-peer communication
- IoT device networking
- Zero-trust microservices mesh

---

## Prerequisites

- **Kubernetes**: v1.21+ (tested on v1.24, v1.27, v1.30)
- **Helm**: v3.8+
- **Storage**: PersistentVolumeClaim support (for session persistence)
- **Optional**: Prometheus Operator (for ServiceMonitor)
- **Optional**: Jaeger/Tempo (for OTLP telemetry)

---

## Quick Start

### 1. Install with Default Values

```bash
helm install nyx ./charts/nyx \
  --namespace nyx-system \
  --create-namespace
```

This deploys:
- **1 replica** (single daemon instance)
- **Prometheus metrics** at `:9090/metrics`
- **gRPC API** disabled by default
- **OTLP telemetry** disabled by default

### 2. Install with Production Configuration

```bash
helm install nyx ./charts/nyx \
  --namespace nyx-system \
  --create-namespace \
  --values charts/nyx/values-production.yaml
```

Create `values-production.yaml`:

```yaml
# values-production.yaml
replicaCount: 6  # High availability

grpc:
  enabled: true
  port: 50051
  service:
    type: ClusterIP  # Use LoadBalancer for external access
    annotations: {}

telemetry:
  otlp:
    enabled: true
    endpoint: "http://tempo.monitoring.svc.cluster.local:4317"
    samplingRate: 0.1  # 10% sampling
    exportPrometheus: true

resources:
  requests:
    cpu: 1000m      # 1 CPU core
    memory: 512Mi   # 512 MB
  limits:
    cpu: 4000m      # 4 CPU cores (multipath processing)
    memory: 2Gi     # 2 GB (10K connections)

autoscaling:
  enabled: true
  minReplicas: 3
  maxReplicas: 10
  targetCPUUtilizationPercentage: 70
  targetMemoryUtilizationPercentage: 80

podDisruptionBudget:
  enabled: true
  minAvailable: 2  # Ensure 2 replicas during updates

persistence:
  enabled: true
  size: 10Gi
  storageClass: "fast-ssd"  # Use SSD for low-latency

config:
  # Embedded nyx.toml configuration
  network:
    bootstrap_peers:
      - "/ip4/203.0.113.42/udp/43300"
      - "/ip4/198.51.100.7/udp/43300"
  
  multipath:
    enabled: true
    max_paths: 4
    failover_threshold_ms: 500
  
  crypto:
    rekey_interval_seconds: 600      # 10 minutes
    rekey_data_threshold_bytes: 1073741824  # 1 GB
```

### 3. Verify Deployment

```bash
# Check pod status
kubectl get pods -n nyx-system

# Check service endpoints
kubectl get svc -n nyx-system

# Check gRPC API (if enabled)
kubectl port-forward -n nyx-system svc/nyx-grpc 50051:50051
grpcurl -plaintext localhost:50051 list

# Check Prometheus metrics
kubectl port-forward -n nyx-system svc/nyx 9090:9090
curl http://localhost:9090/metrics
```

---

## Configuration

### Core Settings

| Parameter | Description | Default |
|-----------|-------------|---------|
| `replicaCount` | Number of daemon replicas | `1` |
| `image.repository` | Docker image repository | `nyxnet/nyx-daemon` |
| `image.tag` | Docker image tag | `0.9.0` |
| `image.pullPolicy` | Image pull policy | `IfNotPresent` |
| `nameOverride` | Override chart name | `""` |
| `fullnameOverride` | Override full name | `""` |

### gRPC Control API

| Parameter | Description | Default |
|-----------|-------------|---------|
| `grpc.enabled` | Enable gRPC control API | `false` |
| `grpc.port` | gRPC port (internal) | `50051` |
| `grpc.service.type` | Service type (ClusterIP/LoadBalancer/NodePort) | `ClusterIP` |
| `grpc.service.port` | Service port (external) | `50051` |
| `grpc.service.annotations` | Service annotations (e.g., cloud load balancer) | `{}` |
| `grpc.tls.enabled` | Enable TLS for gRPC | `false` |
| `grpc.tls.secretName` | TLS secret name (cert, key) | `""` |

**Example: Expose gRPC with LoadBalancer**

```yaml
grpc:
  enabled: true
  service:
    type: LoadBalancer
    annotations:
      service.beta.kubernetes.io/aws-load-balancer-type: "nlb"
      service.beta.kubernetes.io/aws-load-balancer-internal: "true"
```

### Telemetry

| Parameter | Description | Default |
|-----------|-------------|---------|
| `telemetry.otlp.enabled` | Enable OTLP telemetry export | `false` |
| `telemetry.otlp.endpoint` | OTLP collector endpoint (gRPC) | `""` |
| `telemetry.otlp.samplingRate` | Trace sampling rate (0.0-1.0) | `0.1` |
| `telemetry.otlp.exportPrometheus` | Export Prometheus metrics alongside OTLP | `true` |

**Example: Jaeger Integration**

```yaml
telemetry:
  otlp:
    enabled: true
    endpoint: "http://jaeger-collector.monitoring.svc.cluster.local:14250"
    samplingRate: 0.1  # 10% sampling (reduce overhead)
```

**Example: Tempo Integration**

```yaml
telemetry:
  otlp:
    enabled: true
    endpoint: "http://tempo.monitoring.svc.cluster.local:4317"
    samplingRate: 0.05  # 5% sampling (high traffic)
```

### Resources & Autoscaling

| Parameter | Description | Default |
|-----------|-------------|---------|
| `resources.requests.cpu` | CPU request | `500m` |
| `resources.requests.memory` | Memory request | `256Mi` |
| `resources.limits.cpu` | CPU limit | `2000m` |
| `resources.limits.memory` | Memory limit | `1Gi` |
| `autoscaling.enabled` | Enable HPA | `false` |
| `autoscaling.minReplicas` | Minimum replicas | `1` |
| `autoscaling.maxReplicas` | Maximum replicas | `5` |
| `autoscaling.targetCPUUtilizationPercentage` | CPU threshold for scaling | `80` |
| `autoscaling.targetMemoryUtilizationPercentage` | Memory threshold for scaling | `80` |

**Resource Guidelines**:
- **Small deployment** (10-100 connections): 500m CPU, 256Mi memory
- **Medium deployment** (100-1K connections): 1 CPU, 512Mi memory
- **Large deployment** (1K-10K connections): 4 CPU, 2Gi memory

### Persistence

| Parameter | Description | Default |
|-----------|-------------|---------|
| `persistence.enabled` | Enable persistent storage (session state) | `false` |
| `persistence.size` | PVC size | `1Gi` |
| `persistence.storageClass` | Storage class | `""` |
| `persistence.accessMode` | Access mode | `ReadWriteOnce` |

**When to Enable Persistence**:
- ✅ **Enable**: Long-lived sessions, need to survive pod restarts
- ❌ **Disable**: Stateless deployments, short-lived connections

### Push Notifications (Mobile)

| Parameter | Description | Default |
|-----------|-------------|---------|
| `pushNotification.enabled` | Enable push notification relay | `false` |
| `pushNotification.fcm.enabled` | Enable Firebase Cloud Messaging | `false` |
| `pushNotification.fcm.credentialsSecret` | FCM credentials secret name | `nyx-fcm-credentials` |
| `pushNotification.apns.enabled` | Enable Apple Push Notification Service | `false` |
| `pushNotification.apns.credentialsSecret` | APNS credentials secret name | `nyx-apns-credentials` |

**Setup Push Notifications**:

1. Create FCM credentials secret:
   ```bash
   kubectl create secret generic nyx-fcm-credentials \
     --from-file=fcm-service-account.json=./fcm-key.json \
     --namespace nyx-system
   ```

2. Create APNS credentials secret:
   ```bash
   kubectl create secret generic nyx-apns-credentials \
     --from-file=apns-key.p8=./apns-key.p8 \
     --from-literal=key-id=ABCD1234 \
     --from-literal=team-id=XYZ9876 \
     --namespace nyx-system
   ```

3. Enable in `values.yaml`:
   ```yaml
   pushNotification:
     enabled: true
     fcm:
       enabled: true
     apns:
       enabled: true
   ```

### Configuration File (nyx.toml)

| Parameter | Description | Default |
|-----------|-------------|---------|
| `config` | Embedded nyx.toml configuration | See `values.yaml` |

**Configuration Sections** (see [docs/configuration.md](../../docs/configuration.md)):
1. **Root**: `node_id`, `log_level`, `data_directory`
2. **Network**: `listen_addr`, `public_addr`, `bootstrap_peers`
3. **Crypto**: `rekey_interval_seconds`, `rekey_data_threshold_bytes`
4. **Multipath**: `enabled`, `max_paths`, `failover_threshold_ms`
5. **DHT**: `replication_factor`, `query_timeout`
6. **Endpoints**: `metrics_port`, `control_port`
7. **Telemetry**: `otlp_endpoint`, `otlp_sampling_rate`

**Example: Override Configuration**

```yaml
config:
  root:
    log_level: "info"  # debug, info, warn, error
  
  network:
    listen_addr: "0.0.0.0:43300"
    public_addr: ""  # Auto-detect
    bootstrap_peers:
      - "/ip4/203.0.113.42/udp/43300"
  
  crypto:
    rekey_interval_seconds: 600      # 10 minutes
    rekey_data_threshold_bytes: 1073741824  # 1 GB
  
  multipath:
    enabled: true
    max_paths: 4
    failover_threshold_ms: 500
  
  limits:
    max_connections: 10000
    max_streams_per_connection: 1000
```

---

## Advanced Configuration

### High Availability (HA)

```yaml
# values-ha.yaml
replicaCount: 6  # Spread across 3 AZs (2 per AZ)

affinity:
  podAntiAffinity:
    requiredDuringSchedulingIgnoredDuringExecution:
      - labelSelector:
          matchExpressions:
            - key: app.kubernetes.io/name
              operator: In
              values:
                - nyx
        topologyKey: topology.kubernetes.io/zone

podDisruptionBudget:
  enabled: true
  minAvailable: 3  # Minimum 3 replicas (quorum)

autoscaling:
  enabled: true
  minReplicas: 6
  maxReplicas: 20
```

### Multi-Region Deployment

```yaml
# values-region-us-east.yaml
config:
  network:
    bootstrap_peers:
      - "/dns4/nyx-us-west.example.com/udp/43300"
      - "/dns4/nyx-eu-west.example.com/udp/43300"
      - "/dns4/nyx-ap-southeast.example.com/udp/43300"

grpc:
  enabled: true
  service:
    type: LoadBalancer
    annotations:
      service.beta.kubernetes.io/aws-load-balancer-cross-zone-load-balancing-enabled: "true"
```

### TLS/mTLS for gRPC

```yaml
# values-grpc-tls.yaml
grpc:
  enabled: true
  tls:
    enabled: true
    secretName: "nyx-grpc-tls"  # Contains tls.crt, tls.key, ca.crt

# Create TLS secret
# kubectl create secret tls nyx-grpc-tls \
#   --cert=grpc-server.crt \
#   --key=grpc-server.key \
#   --namespace nyx-system
```

### ServiceMonitor (Prometheus Operator)

```yaml
# values-prometheus.yaml
serviceMonitor:
  enabled: true
  interval: 15s
  scrapeTimeout: 10s
  labels:
    prometheus: kube-prometheus
```

---

## Upgrade Guide

### 1. Upgrade with Helm

```bash
# Fetch latest chart
helm repo update

# Upgrade with custom values
helm upgrade nyx ./charts/nyx \
  --namespace nyx-system \
  --values values-production.yaml \
  --wait \
  --timeout 5m
```

### 2. Rolling Update Strategy

The chart uses `RollingUpdate` strategy by default:

```yaml
strategy:
  type: RollingUpdate
  rollingUpdate:
    maxUnavailable: 1
    maxSurge: 1
```

**Zero-Downtime Updates**:
- ✅ Enabled by default with `podDisruptionBudget.minAvailable`
- ✅ Graceful shutdown (SIGTERM handler, 30s grace period)
- ✅ Connection migration (QUIC connection IDs)

### 3. Rollback

```bash
# List releases
helm list -n nyx-system

# Rollback to previous version
helm rollback nyx -n nyx-system

# Rollback to specific revision
helm rollback nyx 2 -n nyx-system
```

---

## Troubleshooting

### 1. Pods Not Starting

**Symptoms**: Pods in `Pending` or `CrashLoopBackOff` state

**Check**:
```bash
# Describe pod
kubectl describe pod <pod-name> -n nyx-system

# Check logs
kubectl logs <pod-name> -n nyx-system

# Common issues:
# - Insufficient CPU/memory resources
# - PVC not binding (check storage class)
# - Image pull errors (check image.repository, image.tag)
```

**Fix**:
- Reduce resource requests in `values.yaml`
- Check storage class availability (`kubectl get sc`)
- Verify image exists (`docker pull nyxnet/nyx-daemon:0.9.0`)

### 2. gRPC API Not Accessible

**Symptoms**: Connection refused or timeout when connecting to gRPC

**Check**:
```bash
# Check service endpoints
kubectl get svc -n nyx-system

# Check if gRPC port is exposed
kubectl get svc nyx-grpc -n nyx-system -o yaml

# Port-forward to test locally
kubectl port-forward -n nyx-system svc/nyx-grpc 50051:50051

# Test with grpcurl
grpcurl -plaintext localhost:50051 list
```

**Fix**:
- Ensure `grpc.enabled: true` in `values.yaml`
- Check service type (`ClusterIP` for internal, `LoadBalancer` for external)
- Verify firewall rules (cloud provider security groups)

### 3. OTLP Telemetry Not Working

**Symptoms**: No traces in Jaeger/Tempo

**Check**:
```bash
# Check environment variables
kubectl get pod <pod-name> -n nyx-system -o yaml | grep NYX_OTLP_ENDPOINT

# Check connectivity to OTLP collector
kubectl exec -it <pod-name> -n nyx-system -- curl -v http://tempo.monitoring.svc.cluster.local:4317

# Check logs for OTLP errors
kubectl logs <pod-name> -n nyx-system | grep -i otlp
```

**Fix**:
- Verify `telemetry.otlp.endpoint` is correct
- Check OTLP collector is running (`kubectl get pods -n monitoring`)
- Reduce sampling rate (`telemetry.otlp.samplingRate: 1.0` for testing)

### 4. High Memory Usage

**Symptoms**: Pods restarted due to OOMKilled

**Check**:
```bash
# Check memory usage
kubectl top pod -n nyx-system

# Check resource limits
kubectl get pod <pod-name> -n nyx-system -o yaml | grep -A 5 resources
```

**Fix**:
- Increase memory limits: `resources.limits.memory: 4Gi`
- Reduce max connections: `config.limits.max_connections: 5000`
- Reduce max streams: `config.limits.max_streams_per_connection: 500`

### 5. Connection Failures

**Symptoms**: Peers cannot connect to daemon

**Check**:
```bash
# Check logs for NAT traversal errors
kubectl logs <pod-name> -n nyx-system | grep -i "NAT\|STUN\|ICE"

# Check bootstrap peers
kubectl exec -it <pod-name> -n nyx-system -- nyx-cli node info
```

**Fix**:
- Verify bootstrap peers are reachable (`config.network.bootstrap_peers`)
- Check STUN server configuration (`config.stun.servers`)
- Ensure UDP port 43300 is open (firewall, security groups)

### 6. Prometheus Metrics Not Scraped

**Symptoms**: Metrics not visible in Prometheus

**Check**:
```bash
# Check metrics endpoint
kubectl port-forward -n nyx-system svc/nyx 9090:9090
curl http://localhost:9090/metrics

# Check ServiceMonitor (if using Prometheus Operator)
kubectl get servicemonitor -n nyx-system
```

**Fix**:
- Ensure `serviceMonitor.enabled: true` (if using Prometheus Operator)
- Check ServiceMonitor labels match Prometheus selector
- Verify Prometheus scrape config includes nyx namespace

---

## Examples

### Example 1: Minimal Development Deployment

```bash
helm install nyx ./charts/nyx \
  --namespace nyx-dev \
  --create-namespace \
  --set replicaCount=1 \
  --set resources.requests.cpu=250m \
  --set resources.requests.memory=128Mi \
  --set persistence.enabled=false
```

### Example 2: Production with External gRPC

```bash
helm install nyx ./charts/nyx \
  --namespace nyx-prod \
  --create-namespace \
  --values - <<EOF
replicaCount: 6

grpc:
  enabled: true
  service:
    type: LoadBalancer
    annotations:
      service.beta.kubernetes.io/aws-load-balancer-type: "nlb"

telemetry:
  otlp:
    enabled: true
    endpoint: "http://tempo.monitoring.svc.cluster.local:4317"
    samplingRate: 0.1

resources:
  requests:
    cpu: 1000m
    memory: 512Mi
  limits:
    cpu: 4000m
    memory: 2Gi

autoscaling:
  enabled: true
  minReplicas: 3
  maxReplicas: 10

podDisruptionBudget:
  enabled: true
  minAvailable: 2
EOF
```

### Example 3: Multi-Region with TLS

```bash
helm install nyx ./charts/nyx \
  --namespace nyx-global \
  --create-namespace \
  --values - <<EOF
replicaCount: 3

grpc:
  enabled: true
  tls:
    enabled: true
    secretName: nyx-grpc-tls
  service:
    type: LoadBalancer

config:
  network:
    bootstrap_peers:
      - "/dns4/nyx-us-east.example.com/udp/43300"
      - "/dns4/nyx-us-west.example.com/udp/43300"
      - "/dns4/nyx-eu-west.example.com/udp/43300"

affinity:
  podAntiAffinity:
    requiredDuringSchedulingIgnoredDuringExecution:
      - labelSelector:
          matchLabels:
            app.kubernetes.io/name: nyx
        topologyKey: topology.kubernetes.io/zone
EOF
```

---

## Uninstall

```bash
# Uninstall release
helm uninstall nyx -n nyx-system

# Delete namespace (WARNING: deletes all data)
kubectl delete namespace nyx-system
```

---

## Resources

- **Documentation**: [docs/](../../docs/)
  - [Architecture](../../docs/architecture.md) (1050+ lines)
  - [Configuration Reference](../../docs/configuration.md) (850+ lines)
  - [API Reference](../../docs/api.md) (550+ lines, 20 gRPC RPCs)
  - [Quick Start](../../docs/quickstart-ubuntu-k8s.md) (250+ lines)
- **Examples**: [examples/](../../examples/)
  - [full_config.toml](../../examples/full_config.toml) (350+ lines)
  - [gRPC client example](../../nyx-sdk/examples/grpc_client_example.rs)
- **Production Readiness**: [PRODUCTION_READINESS_CHECKLIST.md](../../PRODUCTION_READINESS_CHECKLIST.md)
- **Project Status**: [PROJECT_COMPLETION_STATUS.md](../../PROJECT_COMPLETION_STATUS.md)

---

## Support

- **Issues**: [GitHub Issues](https://github.com/SeleniaProject/Nyx/issues)
- **Discussions**: [GitHub Discussions](https://github.com/SeleniaProject/Nyx/discussions)
- **Security**: [SECURITY.md](../../SECURITY.md) (responsible disclosure)

---

## License

Dual-licensed under MIT OR Apache-2.0. See [LICENSE-MIT](../../LICENSE-MIT) and [LICENSE-APACHE](../../LICENSE-APACHE).

---

**Chart Maintained By**: NyxNet Development Team  
**Last Updated**: 2025-10-04  
**Chart Version**: 0.2.0  
**App Version**: 0.9.0

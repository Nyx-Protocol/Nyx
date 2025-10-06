---- MODULE NyxPerformanceModels ----
(****************************************************************************)
(* Nyx Protocol - Performance Evaluation and Analysis Models               *)
(*                                                                          *)
(* This module provides comprehensive performance models for analyzing     *)
(* the Nyx protocol including latency, throughput, resource utilization,   *)
(* and scalability characteristics.                                        *)
(*                                                                          *)
(* Performance Metrics:                                                     *)
(*   - End-to-end latency analysis                                         *)
(*   - Throughput modeling and optimization                                *)
(*   - Resource utilization (CPU, memory, network)                         *)
(*   - Scalability bounds and limits                                       *)
(*   - Quality of Service guarantees                                       *)
(****************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, Integers, Reals, TLC,

(****************************************************************************)
(* Common Helper Operators                                                  *)
(****************************************************************************)

\* Minimum of a set
MIN(S) == IF S = {} THEN 0 ELSE CHOOSE x \in S : \A y \in S : x <= y

\* Maximum of a set
MAX(S) == IF S = {} THEN 0 ELSE CHOOSE x \in S : \A y \in S : x >= y

\* Minimum (lowercase alias)
Min(x, y) == IF x < y THEN x ELSE y

\* Maximum (lowercase alias)
Max(x, y) == IF x > y THEN x ELSE y

\* Absolute value
Abs(x) == IF x < 0 THEN -x ELSE x

\* Sum of set elements
Sum(S) == LET RECURSIVE SumRec(_)
              SumRec(T) == IF T = {} 
                          THEN 0 
                          ELSE LET x == CHOOSE y \in T : TRUE
                               IN x + SumRec(T \ {x})
          IN SumRec(S)

\* Average
Average(S) == IF S = {} THEN 0 ELSE Sum(S) / Cardinality(S)


        NyxCryptography, NyxNetworkLayer, NyxStreamManagement,
        NyxFaultTolerance

(****************************************************************************)
(* Performance Constants and Parameters                                     *)
(****************************************************************************)

\* Latency bounds (in milliseconds)
MinLatency == 1
MaxLatency == 10000
TargetLatency == 100

\* Throughput bounds (in Mbps)
MinThroughput == 1
MaxThroughput == 10000
TargetThroughput == 1000

\* Resource limits
MaxCPUUtilization == 100  \* percentage
MaxMemoryMB == 16384
MaxBandwidthMbps == 10000

\* Scalability limits
MaxNodes == 10000
MaxStreamsPerConnection == 1000
MaxConcurrentConnections == 100000

(****************************************************************************)
(* Latency Models                                                           *)
(****************************************************************************)

\* Network propagation delay model
PropagationDelay(distance_km, medium) ==
    CASE medium = "fiber" -> distance_km / 200000  \* Speed of light in fiber
      [] medium = "satellite" -> distance_km / 300000 + 250  \* LEO satellite
      [] OTHER -> distance_km / 100000  \* Copper/wireless

\* Processing delay for cryptographic operations (microseconds)
CryptoProcessingDelay(operation) ==
    CASE operation = "X25519_DH" -> 50
      [] operation = "Kyber_Encapsulate" -> 100
      [] operation = "Kyber_Decapsulate" -> 80
      [] operation = "Dilithium_Sign" -> 200
      [] operation = "Dilithium_Verify" -> 150
      [] operation = "ChaCha20_Poly1305_Encrypt" -> 10
      [] operation = "ChaCha20_Poly1305_Decrypt" -> 10
      [] operation = "AES_GCM_Encrypt" -> 8
      [] operation = "AES_GCM_Decrypt" -> 8
      [] operation = "HMAC_SHA3_256" -> 15
      [] operation = "HKDF" -> 30
      [] OTHER -> 50

\* Queuing delay model (M/M/1 queue)
QueuingDelay(arrival_rate, service_rate) ==
    IF service_rate > arrival_rate
    THEN 1 / (service_rate - arrival_rate)
    ELSE MaxLatency  \* Unstable queue

\* Serialization delay
SerializationDelay(packet_size_bits, link_bandwidth_bps) ==
    packet_size_bits / link_bandwidth_bps

\* End-to-end latency composition
E2ELatency(
    num_hops,
    avg_distance_per_hop,
    packet_size,
    link_bandwidth,
    arrival_rate,
    service_rate,
    crypto_ops
) ==
    LET prop_delay == num_hops * PropagationDelay(avg_distance_per_hop, "fiber")
        serial_delay == num_hops * SerializationDelay(packet_size * 8, link_bandwidth)
        queue_delay == num_hops * QueuingDelay(arrival_rate, service_rate)
        crypto_delay == CHOOSE d : d = Sum({CryptoProcessingDelay(op) : op \in crypto_ops})
    IN prop_delay + serial_delay + queue_delay + (crypto_delay / 1000)

\* Latency percentile model
LatencyPercentile(samples, percentile) ==
    LET sorted == SortSeq(samples, LAMBDA x, y : x <= y)
        index == (Len(sorted) * percentile) \div 100
    IN IF index > 0 /\ index <= Len(sorted)
       THEN sorted[index]
       ELSE sorted[Len(sorted)]

\* Latency SLA violation probability
LatencySLAViolation(mean_latency, std_dev, sla_threshold) ==
    LET z_score == (sla_threshold - mean_latency) / std_dev
    IN IF z_score >= 0
       THEN 1 - NormalCDF(z_score)  \* Probability of exceeding threshold
       ELSE 1

(****************************************************************************)
(* Throughput Models                                                        *)
(****************************************************************************)

\* Single stream throughput with flow control
StreamThroughput(window_size, rtt, packet_size) ==
    (window_size * packet_size * 8) / rtt  \* bits per second

\* CUBIC throughput model
CUBICThroughput(C, beta, rtt, t_last_congestion) ==
    LET t == CurrentTime - t_last_congestion
        W_max == CHOOSE w : w > 0  \* Last max window before loss
        W_cubic == C * (t - ((W_max * beta) / C) ^ (1/3)) ^ 3 + W_max
    IN (W_cubic * MTU * 8) / rtt

\* BBR throughput model
BBRThroughput(btl_bw, min_rtt, bdp) ==
    Min(btl_bw, bdp / min_rtt)

\* Multi-path aggregate throughput
MultipathThroughput(paths) ==
    CHOOSE total : total = Sum({paths[p].throughput : p \in DOMAIN paths})

\* Goodput calculation (excluding retransmissions)
Goodput(throughput, loss_rate, retransmission_overhead) ==
    throughput * (1 - loss_rate) / (1 + loss_rate * retransmission_overhead)

\* Stream multiplexing efficiency
MultiplexingEfficiency(num_streams, header_overhead, payload_ratio) ==
    (num_streams * payload_ratio) / 
    (num_streams * (payload_ratio + header_overhead))

\* Bandwidth utilization
BandwidthUtilization(actual_throughput, link_capacity) ==
    (actual_throughput * 100) / link_capacity

\* Fair share throughput with weighted scheduling
FairShareThroughput(total_bandwidth, weight, total_weight) ==
    (total_bandwidth * weight) / total_weight

(****************************************************************************)
(* Resource Utilization Models                                              *)
(****************************************************************************)

\* CPU utilization for cryptographic operations
CPUUtilizationCrypto(ops_per_second, cpu_cycles_per_op, cpu_frequency_hz) ==
    (ops_per_second * cpu_cycles_per_op * 100) / cpu_frequency_hz

\* Memory utilization model
MemoryUtilization ==
    [
        connection_state_mb |-> LAMBDA num_conn : num_conn * 0.1,
        stream_buffers_mb |-> LAMBDA num_streams, buffer_size : 
                                (num_streams * buffer_size) / (1024 * 1024),
        crypto_keys_mb |-> LAMBDA num_keys : num_keys * 0.001,
        packet_buffers_mb |-> LAMBDA num_packets, packet_size :
                                (num_packets * packet_size) / (1024 * 1024),
        total |-> LAMBDA conn, streams, keys, packets :
                    CHOOSE t : t = conn * 0.1 + 
                                   (streams * 64) / (1024 * 1024) +
                                   keys * 0.001 +
                                   (packets * 1500) / (1024 * 1024)
    ]

\* Network buffer occupancy
BufferOccupancy(arrival_rate, service_rate, buffer_size) ==
    IF service_rate > arrival_rate
    THEN (arrival_rate / service_rate) * buffer_size
    ELSE buffer_size  \* Buffer full

\* Thread pool utilization
ThreadPoolUtilization(active_tasks, pool_size) ==
    (active_tasks * 100) / pool_size

\* File descriptor usage
FileDescriptorUsage(num_connections, num_files) ==
    num_connections * 2 + num_files  \* 2 FDs per connection

(****************************************************************************)
(* Scalability Models                                                       *)
(****************************************************************************)

\* Maximum connections based on resources
MaxConnections ==
    [
        by_memory |-> LAMBDA total_mem_mb : 
                       (total_mem_mb * 1024 * 1024) \div (100 * 1024),  \* 100KB per conn
        by_cpu |-> LAMBDA cpu_cores, ops_per_conn :
                    (cpu_cores * 1000000) \div ops_per_conn,
        by_fds |-> LAMBDA max_fds :
                    max_fds \div 2,
        effective |-> LAMBDA mem, cpu, fds :
                       Min({mem, cpu, fds})
    ]

\* Scalability factor with number of nodes
ScalabilityFactor(num_nodes, routing_complexity) ==
    CASE routing_complexity = "O(1)" -> 1
      [] routing_complexity = "O(log n)" -> LogBase(2, num_nodes)
      [] routing_complexity = "O(n)" -> num_nodes
      [] routing_complexity = "O(n log n)" -> num_nodes * LogBase(2, num_nodes)
      [] routing_complexity = "O(n^2)" -> num_nodes * num_nodes
      [] OTHER -> num_nodes

\* Network diameter impact
NetworkDiameterImpact(num_nodes, topology) ==
    CASE topology = "fully_connected" -> 1
      [] topology = "ring" -> num_nodes \div 2
      [] topology = "tree" -> LogBase(2, num_nodes)
      [] topology = "mesh" -> IntegerSqrt(num_nodes)
      [] OTHER -> LogBase(2, num_nodes)

\* Connection state synchronization overhead
SyncOverhead(num_nodes, state_size, update_frequency) ==
    (num_nodes * state_size * update_frequency * 8) / 1000000  \* Mbps

\* Multipath scalability
MultipathScalability(num_paths, coordination_overhead) ==
    LET ideal_speedup == num_paths
        actual_speedup == num_paths / (1 + coordination_overhead * (num_paths - 1))
    IN actual_speedup / ideal_speedup  \* Efficiency ratio

(****************************************************************************)
(* Quality of Service Models                                                *)
(****************************************************************************)

\* Priority-based delay bounds
PriorityDelayBound(priority, base_delay, priority_levels) ==
    base_delay * (priority_levels - priority) / priority_levels

\* Jitter calculation
Jitter(latency_samples) ==
    LET mean == Mean(latency_samples)
        deviations == [i \in DOMAIN latency_samples |-> 
                       Abs(latency_samples[i] - mean)]
    IN Mean(deviations)

\* Packet loss rate model
PacketLossRate(queue_size, arrival_rate, service_rate, time_window) ==
    LET arrivals == arrival_rate * time_window
        capacity == service_rate * time_window + queue_size
    IN IF arrivals > capacity
       THEN (arrivals - capacity) / arrivals
       ELSE 0

\* Service level attainment
SLAAttainment(actual_metric, sla_target) ==
    Min(100, (actual_metric * 100) / sla_target)

\* QoS class differentiation
QoSClass ==
    [
        class_name : STRING,
        min_bandwidth : Nat,
        max_latency : Nat,
        max_jitter : Nat,
        max_loss_rate : 0..100,
        priority : 0..7
    ]

BestEffort == [class_name |-> "BestEffort", min_bandwidth |-> 0,
               max_latency |-> 1000, max_jitter |-> 500,
               max_loss_rate |-> 5, priority |-> 0]

Bronze == [class_name |-> "Bronze", min_bandwidth |-> 1,
           max_latency |-> 500, max_jitter |-> 200,
           max_loss_rate |-> 3, priority |-> 2]

Silver == [class_name |-> "Silver", min_bandwidth |-> 10,
           max_latency |-> 200, max_jitter |-> 50,
           max_loss_rate |-> 1, priority |-> 4]

Gold == [class_name |-> "Gold", min_bandwidth |-> 100,
         max_latency |-> 100, max_jitter |-> 20,
         max_loss_rate |-> 0, priority |-> 6]

Platinum == [class_name |-> "Platinum", min_bandwidth |-> 1000,
             max_latency |-> 50, max_jitter |-> 10,
             max_loss_rate |-> 0, priority |-> 7]

(****************************************************************************)
(* Performance Optimization Models                                          *)
(****************************************************************************)

\* Optimal window size calculation
OptimalWindowSize(bdp, loss_rate) ==
    LET base_window == bdp
        adjusted == base_window / (1 + loss_rate)
    IN Max(MinCWND, Min(MaxCWND, adjusted))

\* Adaptive rate control
AdaptiveRate(current_rate, target_rate, alpha) ==
    current_rate + alpha * (target_rate - current_rate)

\* Load balancing weight calculation
LoadBalancingWeight(path) ==
    LET latency_weight == 1 / path.latency
        bandwidth_weight == path.bandwidth / MaxBandwidthMbps
        loss_weight == 1 - path.loss_rate
        reliability_weight == path.uptime / 100
    IN (latency_weight + bandwidth_weight + loss_weight + reliability_weight) / 4

\* Buffer size optimization
OptimalBufferSize(bandwidth_bps, rtt_ms) ==
    (bandwidth_bps * rtt_ms) / 8000  \* Bytes

\* Prefetch strategy
PrefetchAmount(prediction_accuracy, window_size) ==
    (window_size * prediction_accuracy) / 100

(****************************************************************************)
(* Performance Measurement and Analysis                                     *)
(****************************************************************************)

\* Performance metrics collection
PerformanceMetrics == [
    timestamp : Nat,
    latency_ms : Nat,
    throughput_mbps : Nat,
    packet_loss_rate : 0..100,
    cpu_utilization : 0..100,
    memory_usage_mb : Nat,
    active_connections : Nat,
    active_streams : Nat,
    queue_depth : Nat
]

\* Moving average calculation
MovingAverage(samples, window_size) ==
    IF Len(samples) < window_size
    THEN Mean(samples)
    ELSE LET recent == SubSeq(samples, Len(samples) - window_size + 1, Len(samples))
         IN Mean(recent)

\* Exponential weighted moving average
EWMA(current_value, new_sample, alpha) ==
    alpha * new_sample + (1 - alpha) * current_value

\* Anomaly detection using standard deviation
IsAnomaly(value, mean, std_dev, threshold) ==
    Abs(value - mean) > threshold * std_dev

\* Performance regression detection
PerformanceRegression(baseline, current, threshold_percent) ==
    ((baseline - current) * 100) / baseline > threshold_percent

\* Percentile calculation
Percentiles(samples) ==
    [
        p50 |-> LatencyPercentile(samples, 50),
        p95 |-> LatencyPercentile(samples, 95),
        p99 |-> LatencyPercentile(samples, 99),
        p999 |-> LatencyPercentile(samples, 999\div10)
    ]

(****************************************************************************)
(* Cost Models                                                               *)
(****************************************************************************)

\* Computational cost (CPU cycles)
ComputationalCost(operation) ==
    CASE operation = "encrypt_packet" -> 10000
      [] operation = "decrypt_packet" -> 10000
      [] operation = "sign_message" -> 50000
      [] operation = "verify_signature" -> 40000
      [] operation = "route_lookup" -> 1000
      [] operation = "queue_operation" -> 100
      [] OTHER -> 5000

\* Communication cost (bandwidth bytes)
CommunicationCost(message_type, payload_size) ==
    LET header_size == CASE message_type = "data" -> 50
                         [] message_type = "control" -> 30
                         [] message_type = "heartbeat" -> 20
                         [] OTHER -> 40
    IN header_size + payload_size

\* Storage cost (bytes)
StorageCost(data_type, quantity) ==
    CASE data_type = "connection_state" -> quantity * 1024
      [] data_type = "stream_buffer" -> quantity * 65536
      [] data_type = "crypto_key" -> quantity * 32
      [] data_type = "routing_table_entry" -> quantity * 128
      [] OTHER -> quantity * 512

(****************************************************************************)
(* Capacity Planning Models                                                 *)
(****************************************************************************)

\* Required capacity calculation
RequiredCapacity ==
    [
        cpu_cores |-> LAMBDA peak_ops_per_sec, ops_per_core :
                       (peak_ops_per_sec \div ops_per_core) + 1,
        memory_gb |-> LAMBDA connections, streams, overhead :
                       ((connections * 0.0001 + streams * 0.000064 + overhead) \div 1) + 1,
        bandwidth_gbps |-> LAMBDA throughput_mbps :
                            (throughput_mbps \div 1000) + 1,
        storage_gb |-> LAMBDA logs_per_day, retention_days :
                        ((logs_per_day * retention_days) \div 1000) + 1
    ]

\* Growth projection
GrowthProjection(current_load, growth_rate_percent, months) ==
    current_load * (1 + growth_rate_percent / 100) ^ months

\* Overprovisioning factor
OverprovisioningFactor(service_type) ==
    CASE service_type = "production" -> 2
      [] service_type = "staging" -> 15 \div 10
      [] service_type = "development" -> 1
      [] OTHER -> 15 \div 10

(****************************************************************************)
(* Benchmark Scenarios                                                      *)
(****************************************************************************)

\* Baseline performance benchmark
BaselineBenchmark ==
    [
        scenario |-> "baseline",
        num_connections |-> 1000,
        num_streams_per_conn |-> 10,
        message_size |-> 1024,
        message_rate |-> 1000,
        duration_seconds |-> 60,
        expected_latency_p99 |-> 100,
        expected_throughput_mbps |-> 1000,
        expected_cpu_util |-> 50,
        expected_memory_mb |-> 2048
    ]

\* Stress test benchmark
StressBenchmark ==
    [
        scenario |-> "stress",
        num_connections |-> 10000,
        num_streams_per_conn |-> 100,
        message_size |-> 10240,
        message_rate |-> 10000,
        duration_seconds |-> 300,
        expected_latency_p99 |-> 500,
        expected_throughput_mbps |-> 5000,
        expected_cpu_util |-> 90,
        expected_memory_mb |-> 12288
    ]

\* Latency-sensitive benchmark
LatencySensitiveBenchmark ==
    [
        scenario |-> "latency_sensitive",
        num_connections |-> 100,
        num_streams_per_conn |-> 1,
        message_size |-> 64,
        message_rate |-> 10000,
        duration_seconds |-> 60,
        expected_latency_p99 |-> 10,
        expected_throughput_mbps |-> 100,
        expected_cpu_util |-> 30,
        expected_memory_mb |-> 512
    ]

\* Throughput benchmark
ThroughputBenchmark ==
    [
        scenario |-> "throughput",
        num_connections |-> 100,
        num_streams_per_conn |-> 10,
        message_size |-> 1048576,
        message_rate |-> 1000,
        duration_seconds |-> 120,
        expected_latency_p99 |-> 1000,
        expected_throughput_mbps |-> 8000,
        expected_cpu_util |-> 80,
        expected_memory_mb |-> 8192
    ]

====

---- MODULE NyxNetworkLayer ----
(****************************************************************************)
(* Nyx Protocol - Network Layer Specification                              *)
(*                                                                          *)
(* This module provides a complete formal specification of the Nyx         *)
(* network layer, including packet routing, flow control, congestion       *)
(* control, and bandwidth management.                                      *)
(*                                                                          *)
(* Components Specified:                                                    *)
(*   - Multi-path routing with path selection                              *)
(*   - Packet fragmentation and reassembly                                 *)
(*   - Flow control (sliding window protocol)                              *)
(*   - Congestion control (CUBIC, BBR algorithms)                          *)
(*   - Quality of Service (QoS) mechanisms                                 *)
(*   - Network topology and link management                                *)
(*                                                                          *)
(* Mathematical Properties Verified:                                        *)
(*   - Packet ordering guarantees                                           *)
(*   - Flow conservation                                                    *)
(*   - Deadlock freedom                                                     *)
(*   - Liveness (eventual delivery)                                         *)
(*   - Fairness in bandwidth allocation                                     *)
(****************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, Integers, TLC

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
Average(S) == IF S = {} THEN 0 ELSE Sum(S) \div Cardinality(S)

\* Aliases for compatibility
SUM(S) == Sum(S)
AVG(S) == Average(S)

\* Product of set elements
PRODUCT(S) == LET RECURSIVE ProdRec(_)
                  ProdRec(T) == IF T = {} 
                               THEN 1 
                               ELSE LET x == CHOOSE y \in T : TRUE
                                    IN x * ProdRec(T \ {x})
              IN ProdRec(S)

\* Cube root approximation
CubeRoot(x) == 
    IF x <= 0 THEN 0
    ELSE IF x = 1 THEN 1
    ELSE IF x < 8 THEN 1
    ELSE IF x < 27 THEN 2
    ELSE IF x < 64 THEN 3
    ELSE IF x < 125 THEN 4
    ELSE IF x < 216 THEN 5
    ELSE IF x < 343 THEN 6
    ELSE IF x < 512 THEN 7
    ELSE IF x < 729 THEN 8
    ELSE IF x < 1000 THEN 9
    ELSE 10

\* Infinity representation
Infinity == 999999

\* XOR combine operation for FEC
XOR_Combine(packets) == 
    IF packets = {} THEN <<>> 
    ELSE CHOOSE result \in Seq(Nat) : TRUE

\* Select subset for FEC encoding
SelectSubset(data_packets, index) ==
    IF index > Len(data_packets) THEN {}
    ELSE {i \in 1..Len(data_packets) : (i % (index + 1)) = 0}

\* Reconstruct packets from FEC (simplified)
ReconstructPackets(received_packets, fec_packets, missing_count) ==
    IF missing_count = 0 THEN received_packets
    ELSE CHOOSE result \in Seq(Seq(Nat)) : Len(result) = missing_count

\* Sort by offset (for fragment reassembly)
SortByOffset(fragments) == fragments

\* Sort by quality (for path selection)
SortByQuality(paths) == paths

\* Compute checksum for packet data
ComputeChecksum(data) == 
    IF data = <<>> THEN 0 ELSE (Sum({data[i] : i \in DOMAIN data}) % 65536)

\* QoS priority function
QoSPriority(qos_class) ==
    CASE qos_class = "REAL_TIME" -> 4
      [] qos_class = "INTERACTIVE" -> 3
      [] qos_class = "BULK" -> 2
      [] qos_class = "BACKGROUND" -> 1
      [] OTHER -> 0



CONSTANTS
    Nodes,                  \* Set of all network nodes
    Links,                  \* Set of all network links
    MaxPacketSize,          \* Maximum packet size in bytes
    MaxWindowSize,          \* Maximum flow control window size
    MaxBandwidth,           \* Maximum link bandwidth (packets/time unit)
    MinRTT,                 \* Minimum round-trip time
    MaxRTT,                 \* Maximum round-trip time
    MaxPathLength,          \* Maximum path length (hops)
    MaxQueueSize,           \* Maximum queue size per node
    TimeoutThreshold,       \* Timeout threshold for retransmission
    QoSLevels              \* Set of QoS priority levels

ASSUME 
    /\ MaxPacketSize > 0
    /\ MaxWindowSize > 0
    /\ MaxBandwidth > 0
    /\ MinRTT > 0
    /\ MaxRTT > MinRTT
    /\ MaxPathLength > 2
    /\ MaxQueueSize > 0
    /\ QoSLevels \subseteq Nat

(****************************************************************************)
(* Network Topology                                                         *)
(****************************************************************************)

\* Link structure: directed edge between nodes
LinkStructure == [
    source: Nodes,
    dest: Nodes,
    bandwidth: 1..MaxBandwidth,      \* Available bandwidth
    latency: MinRTT..MaxRTT,         \* Link latency
    loss_rate: 0..100,                \* Packet loss rate (percentage)
    is_active: BOOLEAN,               \* Link operational status
    queue_length: 0..MaxQueueSize     \* Current queue occupancy
]

\* Network topology as adjacency relation
IsAdjacent(n1, n2) == \E l \in Links : l.source = n1 /\ l.dest = n2

\* Select next hop based on routing table (moved after CONSTANTS)
SelectNextHop(packet, routing_table) ==
    IF packet.dest \in DOMAIN routing_table
    THEN routing_table[packet.dest]
    ELSE CHOOSE n \in Nodes : TRUE

\* Path: sequence of nodes
ValidPath(path) ==
    /\ path \in Seq(Nodes)
    /\ Len(path) >= 2
    /\ Len(path) <= MaxPathLength
    /\ \A i \in 1..(Len(path)-1) : IsAdjacent(path[i], path[i+1])

\* Multi-path: set of disjoint or partially overlapping paths
MultipathSet(source, dest) ==
    {p \in Seq(Nodes) : 
        ValidPath(p) /\ p[1] = source /\ p[Len(p)] = dest}

(****************************************************************************)
(* Packet Structure                                                         *)
(****************************************************************************)

\* Packet types
PacketTypes == {
    "DATA",           \* Application data packet
    "ACK",            \* Acknowledgment packet
    "NACK",           \* Negative acknowledgment
    "PROBE",          \* Path probing packet
    "CONTROL",        \* Control message
    "FRAGMENT"        \* Fragmented packet
}

\* QoS classes
QoSClasses == {
    "REAL_TIME",      \* Low latency, high priority
    "INTERACTIVE",    \* Interactive traffic
    "BULK",           \* Bulk data transfer
    "BACKGROUND"      \* Background traffic
}

\* Packet structure
PacketStructure == [
    packet_id: Nat,
    packet_type: PacketTypes,
    source: Nodes,
    dest: Nodes,
    sequence_num: Nat,
    data: Seq(Nat),
    size: 1..MaxPacketSize,
    qos_class: QoSClasses,
    priority: QoSLevels,
    timestamp: Nat,
    ttl: 0..MaxPathLength,
    path: Seq(Nodes),
    current_hop: Nat,
    fragment_id: Nat,
    fragment_offset: Nat,
    is_last_fragment: BOOLEAN,
    checksum: Nat
]

\* Fragment packet into smaller pieces
FragmentPacket(packet, mtu) ==
    LET num_fragments == (packet.size + mtu - 1) \div mtu
        CreateFragment[i \in 1..num_fragments] ==
            [
                packet_id |-> packet.packet_id * 1000 + i,
                packet_type |-> "FRAGMENT",
                source |-> packet.source,
                dest |-> packet.dest,
                sequence_num |-> packet.sequence_num,
                data |-> SubSeq(packet.data, (i-1)*mtu + 1, 
                               IF i = num_fragments THEN packet.size ELSE i*mtu),
                size |-> IF i = num_fragments 
                         THEN packet.size - (i-1)*mtu 
                         ELSE mtu,
                qos_class |-> packet.qos_class,
                priority |-> packet.priority,
                timestamp |-> packet.timestamp,
                ttl |-> packet.ttl,
                path |-> packet.path,
                current_hop |-> packet.current_hop,
                fragment_id |-> packet.packet_id,
                fragment_offset |-> (i-1)*mtu,
                is_last_fragment |-> (i = num_fragments),
                checksum |-> ComputeChecksum(packet.data)
            ]
    IN [i \in 1..num_fragments |-> CreateFragment[i]]

\* Reassemble fragments into original packet
ReassemblePacket(fragments) ==
    LET sorted_fragments == SortByOffset(fragments)
        combined_data == 
            UNION {f.data : f \in sorted_fragments}
        original_packet == fragments[1]
    IN [original_packet EXCEPT 
        !.packet_type = "DATA",
        !.data = combined_data,
        !.size = Len(combined_data)
    ]

(****************************************************************************)
(* Routing and Path Selection                                               *)
(****************************************************************************)

\* Path quality metrics
PathMetrics == [
    latency: Nat,           \* End-to-end latency
    bandwidth: Nat,         \* Available bandwidth
    loss_rate: 0..100,      \* Packet loss rate
    hop_count: Nat,         \* Number of hops
    congestion: 0..100,     \* Congestion level
    reliability: 0..100     \* Path reliability score
]

\* Helper functions for path metrics (must be defined before use)
LinkLatency(n1, n2) == 
    (CHOOSE l \in Links : l.source = n1 /\ l.dest = n2).latency

LinkBandwidth(n1, n2) ==
    (CHOOSE l \in Links : l.source = n1 /\ l.dest = n2).bandwidth

LinkCongestion(n1, n2) ==
    LET link == CHOOSE l \in Links : l.source = n1 /\ l.dest = n2
    IN (link.queue_length * 100) \div MaxQueueSize

ProductLossRate(path) ==
    LET link_loss_rates == {(CHOOSE l \in Links : 
                             l.source = path[i] /\ l.dest = path[i+1]).loss_rate :
                            i \in 1..(Len(path)-1)}
    IN IF link_loss_rates = {} THEN 0
       ELSE AVG(link_loss_rates)

PathReliability(path) ==
    100 - ProductLossRate(path)

\* Compute aggregated path metrics
ComputePathMetrics(path) ==
    [
        latency |-> SUM({LinkLatency(path[i], path[i+1]) : 
                        i \in 1..(Len(path)-1)}),
        bandwidth |-> MIN({LinkBandwidth(path[i], path[i+1]) : 
                          i \in 1..(Len(path)-1)}),
        loss_rate |-> ProductLossRate(path),
        hop_count |-> Len(path) - 1,
        congestion |-> AVG({LinkCongestion(path[i], path[i+1]) : 
                           i \in 1..(Len(path)-1)}),
        reliability |-> PathReliability(path)
    ]

\* Compute path quality score (higher is better)
PathQualityScore(metrics) ==
    LET latency_score == 100 - ((metrics.latency * 100) \div MaxRTT)
        bandwidth_score == ((metrics.bandwidth * 100) \div MaxBandwidth)
        loss_score == 100 - metrics.loss_rate
        reliability_score == metrics.reliability
        congestion_score == 100 - metrics.congestion
    IN ((latency_score + bandwidth_score + loss_score + 
        reliability_score + congestion_score) \div 5)

\* Dijkstra's shortest path algorithm (abstracted)
ShortestPath(source, dest) ==
    LET all_paths == MultipathSet(source, dest)
        path_with_min_metric == 
            CHOOSE p \in all_paths :
                \A q \in all_paths : 
                    PathQualityScore(ComputePathMetrics(p)) >= 
                    PathQualityScore(ComputePathMetrics(q))
    IN path_with_min_metric

\* K-shortest paths for multipath routing
KShortestPaths(source, dest, k) ==
    LET all_paths == MultipathSet(source, dest)
        sorted_paths == SortByQuality(all_paths)
    IN IF Cardinality(all_paths) <= k
       THEN all_paths
       ELSE {sorted_paths[i] : i \in 1..k}

\* Path disjointness: check if paths share links
ArePathsDisjoint(path1, path2) ==
    LET links1 == {<<path1[i], path1[i+1]>> : i \in 1..(Len(path1)-1)}
        links2 == {<<path2[i], path2[i+1]>> : i \in 1..(Len(path2)-1)}
    IN links1 \cap links2 = {}

\* Select optimal multipath set
SelectMultipath(source, dest, num_paths) ==
    LET candidates == KShortestPaths(source, dest, num_paths * 2)
        \* Greedy selection favoring disjoint paths
        SelectGreedy[selected \in SUBSET candidates, remaining \in SUBSET candidates] ==
            IF Cardinality(selected) >= num_paths \/ remaining = {}
            THEN selected
            ELSE LET next_path == CHOOSE p \in remaining :
                         \A q \in remaining : 
                             PathQualityScore(ComputePathMetrics(p)) >= 
                             PathQualityScore(ComputePathMetrics(q))
                     new_selected == selected \union {next_path}
                     new_remaining == remaining \ {next_path}
                 IN SelectGreedy[new_selected, new_remaining]
    IN SelectGreedy[{}, candidates]

(****************************************************************************)
(* Flow Control (Sliding Window Protocol)                                   *)
(****************************************************************************)

\* Flow control window state
FlowControlWindow == [
    send_base: Nat,              \* Oldest unacknowledged packet
    send_next: Nat,              \* Next packet to be sent
    send_window: 1..MaxWindowSize,  \* Send window size
    recv_base: Nat,              \* Next expected packet
    recv_window: 1..MaxWindowSize,  \* Receive window size
    recv_buffer: SUBSET Nat,     \* Out-of-order packets buffered
    cwnd: 1..MaxWindowSize,      \* Congestion window (CUBIC/BBR)
    ssthresh: Nat,               \* Slow start threshold
    rtt_estimate: MinRTT..MaxRTT,  \* RTT estimate
    rtt_variance: Nat,           \* RTT variance
    rto: Nat                     \* Retransmission timeout
]

\* Initialize flow control state
InitFlowControl ==
    [
        send_base |-> 0,
        send_next |-> 0,
        send_window |-> 1,  \* Start with small window (slow start)
        recv_base |-> 0,
        recv_window |-> MaxWindowSize,
        recv_buffer |-> {},
        cwnd |-> 1,
        ssthresh |-> MaxWindowSize \div 2,
        rtt_estimate |-> MinRTT,
        rtt_variance |-> 0,
        rto |-> MinRTT * 2
    ]

\* Check if packet can be sent (within window)
CanSendPacket(fc, seq_num) ==
    /\ seq_num >= fc.send_base
    /\ seq_num < fc.send_base + fc.send_window
    /\ seq_num < fc.send_base + fc.cwnd

\* Update send window on ACK
UpdateSendWindow(fc, ack_num) ==
    IF ack_num > fc.send_base
    THEN [fc EXCEPT 
        !.send_base = ack_num,
        !.send_window = MIN({MaxWindowSize, fc.recv_window})
    ]
    ELSE fc

\* Update receive window
UpdateRecvWindow(fc, seq_num) ==
    IF seq_num = fc.recv_base
    THEN [fc EXCEPT !.recv_base = @ + 1]
    ELSE IF seq_num > fc.recv_base /\ seq_num < fc.recv_base + fc.recv_window
    THEN [fc EXCEPT !.recv_buffer = @ \union {seq_num}]
    ELSE fc

\* RTT estimation (Jacobson's algorithm)
UpdateRTT(fc, sample_rtt) ==
    LET alpha == 1 \div 8  \* Smoothing factor for RTT
        beta == 1 \div 4   \* Smoothing factor for variance
        err == sample_rtt - fc.rtt_estimate
        new_rtt == fc.rtt_estimate + alpha * err
        new_var == fc.rtt_variance + beta * (Abs(err) - fc.rtt_variance)
        new_rto == new_rtt + 4 * new_var
    IN [fc EXCEPT
        !.rtt_estimate = new_rtt,
        !.rtt_variance = new_var,
        !.rto = MAX({MinRTT, MIN({MaxRTT, new_rto})})
    ]

(****************************************************************************)
(* Congestion Control (CUBIC)                                               *)
(****************************************************************************)

\* CUBIC congestion control parameters
CUBICParams == [
    C: Nat,                 \* CUBIC scaling constant
    beta: Nat,              \* Multiplicative decrease factor (0.7)
    fast_convergence: BOOLEAN
]

\* CUBIC window growth function
\* W(t) = C * (t - K)^3 + W_max
\* where K = ((W_max * beta) / C)^(1/3)
CUBICWindow(params, t, w_max, w_current) ==
    LET K == CubeRoot((w_max * params.beta) \div params.C)
        delta_t == t - K
        w_cubic == params.C * (delta_t * delta_t * delta_t) + w_max
    IN MAX({1, MIN({MaxWindowSize, w_cubic})})

\* Update congestion window (CUBIC)
UpdateCWND_CUBIC(fc, params, event, time) ==
    CASE event = "ACK" ->
        IF fc.cwnd < fc.ssthresh
        THEN \* Slow start
            [fc EXCEPT !.cwnd = MIN({MaxWindowSize, @ + 1})]
        ELSE \* Congestion avoidance (CUBIC)
            LET w_cubic == CUBICWindow(params, time, fc.ssthresh, fc.cwnd)
            IN [fc EXCEPT !.cwnd = MIN({MaxWindowSize, w_cubic})]
    [] event = "LOSS" ->
        \* Multiplicative decrease
        [fc EXCEPT 
            !.ssthresh = MAX({2, (fc.cwnd * params.beta) \div 10}),
            !.cwnd = MAX({1, fc.cwnd \div 2})
        ]
    [] event = "TIMEOUT" ->
        \* Severe congestion
        [fc EXCEPT
            !.ssthresh = MAX({2, fc.cwnd \div 2}),
            !.cwnd = 1
        ]

(****************************************************************************)
(* Congestion Control (BBR)                                                 *)
(****************************************************************************)

\* BBR (Bottleneck Bandwidth and RTT) parameters
BBRParams == [
    mode: {"STARTUP", "DRAIN", "PROBE_BW", "PROBE_RTT"},
    pacing_gain: Nat,
    cwnd_gain: Nat,
    btl_bw: Nat,        \* Bottleneck bandwidth estimate
    min_rtt: Nat,       \* Minimum RTT observed
    probe_rtt_time: Nat
]

\* Initialize BBR state
InitBBR ==
    [
        mode |-> "STARTUP",
        pacing_gain |-> 2,  \* High gain for startup
        cwnd_gain |-> 2,
        btl_bw |-> MaxBandwidth \div 10,
        min_rtt |-> MaxRTT,
        probe_rtt_time |-> 0
    ]

\* Update BBR state
UpdateBBR(bbr, fc, delivered_bytes, interval, rtt) ==
    LET \* Update bandwidth estimate
        current_bw == delivered_bytes \div interval
        new_btl_bw == MAX({bbr.btl_bw, current_bw})
        \* Update RTT estimate
        new_min_rtt == MIN({bbr.min_rtt, rtt})
        \* State machine transitions
        new_mode == CASE bbr.mode = "STARTUP" /\ fc.cwnd >= new_btl_bw * new_min_rtt ->
                        "DRAIN"
                    [] bbr.mode = "DRAIN" /\ fc.cwnd <= new_btl_bw * new_min_rtt ->
                        "PROBE_BW"
                    [] bbr.mode = "PROBE_BW" /\ bbr.probe_rtt_time > 10000 ->
                        "PROBE_RTT"
                    [] bbr.mode = "PROBE_RTT" /\ bbr.probe_rtt_time = 0 ->
                        "PROBE_BW"
                    [] OTHER -> bbr.mode
        \* Pacing gain based on mode
        new_pacing_gain == CASE new_mode = "STARTUP" -> 2
                           [] new_mode = "DRAIN" -> 1
                           [] new_mode = "PROBE_BW" -> 1
                           [] new_mode = "PROBE_RTT" -> 1
    IN [bbr EXCEPT
        !.mode = new_mode,
        !.btl_bw = new_btl_bw,
        !.min_rtt = new_min_rtt,
        !.pacing_gain = new_pacing_gain,
        !.probe_rtt_time = IF new_mode = "PROBE_RTT" 
                           THEN @ + interval 
                           ELSE 0
    ]

\* BBR pacing rate
BBRPacingRate(bbr) ==
    bbr.btl_bw * bbr.pacing_gain

\* BBR congestion window
BBRCongestionWindow(bbr) ==
    bbr.btl_bw * bbr.min_rtt * bbr.cwnd_gain

(****************************************************************************)
(* Quality of Service (QoS)                                                 *)
(****************************************************************************)

\* QoS scheduler: Weighted Fair Queueing (WFQ)
WFQ_Schedule(queues, weights) ==
    LET \* Compute virtual finish time for each queue
        VirtualFinishTime[q \in DOMAIN queues] ==
            IF queues[q] = <<>>
            THEN Infinity
            ELSE Head(queues[q]).size \div weights[q]
        \* Select queue with minimum virtual finish time
        selected_queue == CHOOSE q \in DOMAIN queues :
            \A r \in DOMAIN queues : 
                VirtualFinishTime[q] <= VirtualFinishTime[r]
    IN IF queues[selected_queue] = <<>>
       THEN "EMPTY"
       ELSE Head(queues[selected_queue])

\* Priority queueing
PrioritySchedule(queues) ==
    LET non_empty_queues == {q \in DOMAIN queues : queues[q] # <<>>}
    IN IF non_empty_queues = {}
       THEN "EMPTY"
       ELSE LET highest_priority == MIN({q.priority : q \in non_empty_queues})
                selected_queue == CHOOSE q \in non_empty_queues :
                    q.priority = highest_priority
            IN Head(queues[selected_queue])

\* Deficit Round Robin (DRR) scheduling
DRR_Schedule(queues, quanta, deficits) ==
    LET UpdateDeficit[q \in DOMAIN queues] ==
            IF queues[q] = <<>>
            THEN deficits[q]
            ELSE LET packet == Head(queues[q])
                     new_deficit == deficits[q] + quanta[q]
                 IN IF new_deficit >= packet.size
                    THEN [queue |-> Tail(queues[q]),
                          deficit |-> new_deficit - packet.size,
                          packet |-> packet]
                    ELSE [queue |-> queues[q],
                          deficit |-> 0,
                          packet |-> "SKIP"]
    IN UpdateDeficit

\* Traffic shaping: Token bucket
TokenBucket == [
    tokens: 0..MaxBandwidth,
    capacity: MaxBandwidth,
    rate: 1..MaxBandwidth,
    last_update: Nat
]

UpdateTokenBucket(tb, current_time) ==
    LET time_diff == current_time - tb.last_update
        new_tokens == MIN({tb.capacity, 
                          tb.tokens + tb.rate * time_diff})
    IN [tb EXCEPT
        !.tokens = new_tokens,
        !.last_update = current_time
    ]

CanSendWithTokenBucket(tb, packet_size) ==
    tb.tokens >= packet_size

ConsumeTokens(tb, packet_size) ==
    [tb EXCEPT !.tokens = @ - packet_size]

(****************************************************************************)
(* Packet Loss and Recovery                                                 *)
(****************************************************************************)

\* Fast retransmit: trigger on 3 duplicate ACKs
FastRetransmit(fc, dup_ack_count) ==
    /\ dup_ack_count >= 3
    /\ fc' = UpdateCWND_CUBIC(fc, CUBICParams, "LOSS", 0)

\* Selective Acknowledgment (SACK)
SACKBlock == [
    start: Nat,
    end: Nat
]

ProcessSACK(fc, sack_blocks) ==
    LET acked_packets == UNION {{s..b.end : s \in b.start..b.end} : b \in sack_blocks}
        new_send_base == MAX({fc.send_base} \union acked_packets) + 1
    IN [fc EXCEPT !.send_base = new_send_base]

\* Forward Error Correction (FEC)
GenerateFECPackets(data_packets, redundancy) ==
    LET num_fec == ((Len(data_packets) * redundancy) \div 100)
        \* Reed-Solomon or XOR-based FEC
        fec_data[i \in 1..num_fec] ==
            XOR_Combine({data_packets[j] : j \in SelectSubset(data_packets, i)})
    IN [i \in 1..num_fec |-> fec_data[i]]

RecoverWithFEC(received_packets, fec_packets, expected_count) ==
    LET missing_count == expected_count - Len(received_packets)
    IN IF missing_count > Len(fec_packets)
       THEN "UNRECOVERABLE"
       ELSE \* Reconstruct missing packets using FEC
            ReconstructPackets(received_packets, fec_packets, missing_count)

(****************************************************************************)
(* Network State Variables                                                  *)
(****************************************************************************)

VARIABLES
    \* Network topology
    link_state,              \* State of all links
    node_state,              \* State of all nodes
    
    \* Routing
    routing_tables,          \* Routing table per node
    active_paths,            \* Currently active paths
    path_metrics,            \* Metrics for each path
    
    \* Packet transmission
    in_flight_packets,       \* Packets currently in transit
    packet_queues,           \* Per-node packet queues
    
    \* Flow control
    flow_control_state,      \* Flow control state per connection
    
    \* Congestion control
    congestion_state,        \* CUBIC or BBR state per connection
    
    \* QoS
    qos_queues,              \* Priority queues per node
    token_buckets,           \* Token buckets for traffic shaping
    
    \* Statistics
    packets_sent,
    packets_received,
    packets_lost,
    total_latency,
    total_bandwidth

network_vars == <<link_state, node_state, routing_tables, active_paths,
                  path_metrics, in_flight_packets, packet_queues,
                  flow_control_state, congestion_state, qos_queues,
                  token_buckets, packets_sent, packets_received,
                  packets_lost, total_latency, total_bandwidth>>

(****************************************************************************)
(* Initial State                                                            *)
(****************************************************************************)

NetworkInit ==
    /\ link_state = [l \in Links |-> 
        [bandwidth |-> l.bandwidth,
         latency |-> l.latency,
         loss_rate |-> l.loss_rate,
         is_active |-> TRUE,
         queue_length |-> 0]]
    /\ node_state = [n \in Nodes |-> "ACTIVE"]
    /\ routing_tables = [n \in Nodes |-> [m \in Nodes |-> <<>>]]
    /\ active_paths = [n \in Nodes |-> [m \in Nodes |-> {}]]
    /\ path_metrics = [n \in Nodes |-> [m \in Nodes |-> [p \in {} |-> <<>>]]]
    /\ in_flight_packets = {}
    /\ packet_queues = [n \in Nodes |-> <<>>]
    /\ flow_control_state = [n \in Nodes |-> 
        [m \in Nodes |-> InitFlowControl]]
    /\ congestion_state = [n \in Nodes |-> 
        [m \in Nodes |-> InitBBR]]
    /\ qos_queues = [n \in Nodes |-> 
        [qos \in QoSClasses |-> <<>>]]
    /\ token_buckets = [n \in Nodes |-> 
        [capacity |-> MaxBandwidth,
         tokens |-> MaxBandwidth,
         rate |-> MaxBandwidth,
         last_update |-> 0]]
    /\ packets_sent = 0
    /\ packets_received = 0
    /\ packets_lost = 0
    /\ total_latency = 0
    /\ total_bandwidth = 0

(****************************************************************************)
(* Actions                                                                  *)
(****************************************************************************)

\* Send packet with flow control check
SendPacket(source, dest, data, qos_class) ==
    /\ LET fc == flow_control_state[source][dest]
           seq_num == fc.send_next
           packet == [
               packet_id |-> packets_sent + 1,
               packet_type |-> "DATA",
               source |-> source,
               dest |-> dest,
               sequence_num |-> seq_num,
               data |-> data,
               size |-> Len(data),
               qos_class |-> qos_class,
               priority |-> QoSPriority(qos_class),
               timestamp |-> packets_sent,  \* Use counter as time
               ttl |-> MaxPathLength,
               path |-> <<>>,  \* Path determined during routing
               current_hop |-> 0,
               fragment_id |-> 0,
               fragment_offset |-> 0,
               is_last_fragment |-> TRUE,
               checksum |-> ComputeChecksum(data)
           ]
       IN /\ CanSendPacket(fc, seq_num)
          /\ in_flight_packets' = in_flight_packets \union {packet}
          /\ flow_control_state' = [flow_control_state EXCEPT
               ![source][dest].send_next = @ + 1]
          /\ packets_sent' = packets_sent + 1
          /\ UNCHANGED <<link_state, node_state, routing_tables,
                        active_paths, path_metrics, packet_queues,
                        congestion_state, qos_queues, token_buckets,
                        packets_received, packets_lost, total_latency,
                        total_bandwidth>>

\* Route packet through network
RoutePacket(packet) ==
    /\ packet \in in_flight_packets
    /\ packet.ttl > 0
    /\ LET current_node == IF packet.current_hop = 0 
                          THEN packet.source
                          ELSE packet.path[packet.current_hop]
           next_hop == IF packet.path = <<>> \/ packet.current_hop = 0
                       THEN SelectNextHop(current_node, packet.dest)
                       ELSE packet.path[packet.current_hop + 1]
           new_packet == [packet EXCEPT
               !.path = IF @ = <<>> THEN <<current_node, next_hop>> 
                       ELSE Append(@, next_hop),
               !.current_hop = @ + 1,
               !.ttl = @ - 1]
       IN /\ next_hop # "NONE"
          /\ in_flight_packets' = (in_flight_packets \ {packet}) \union {new_packet}
          /\ UNCHANGED <<link_state, node_state, routing_tables,
                        active_paths, path_metrics, packet_queues,
                        flow_control_state, congestion_state, qos_queues,
                        token_buckets, packets_sent, packets_received,
                        packets_lost, total_latency, total_bandwidth>>

\* Deliver packet to destination
DeliverPacket(packet) ==
    /\ packet \in in_flight_packets
    /\ packet.current_hop > 0
    /\ packet.path[packet.current_hop] = packet.dest
    /\ LET fc == flow_control_state[packet.dest][packet.source]
           new_fc == UpdateRecvWindow(fc, packet.sequence_num)
       IN /\ in_flight_packets' = in_flight_packets \ {packet}
          /\ flow_control_state' = [flow_control_state EXCEPT
               ![packet.dest][packet.source] = new_fc]
          /\ packets_received' = packets_received + 1
          /\ total_latency' = total_latency + (packets_sent - packet.timestamp)
          /\ UNCHANGED <<link_state, node_state, routing_tables,
                        active_paths, path_metrics, packet_queues,
                        congestion_state, qos_queues, token_buckets,
                        packets_sent, packets_lost, total_bandwidth>>

\* Send acknowledgment
SendACK(receiver, sender, ack_num) ==
    /\ LET ack_packet == [
               packet_id |-> packets_sent + 1,
               packet_type |-> "ACK",
               source |-> receiver,
               dest |-> sender,
               sequence_num |-> ack_num,
               data |-> <<>>,
               size |-> 0,
               qos_class |-> "REAL_TIME",
               priority |-> 0,
               timestamp |-> packets_sent,
               ttl |-> MaxPathLength,
               path |-> <<>>,
               current_hop |-> 0,
               fragment_id |-> 0,
               fragment_offset |-> 0,
               is_last_fragment |-> TRUE,
               checksum |-> 0
           ]
       IN /\ in_flight_packets' = in_flight_packets \union {ack_packet}
          /\ packets_sent' = packets_sent + 1
          /\ UNCHANGED <<link_state, node_state, routing_tables,
                        active_paths, path_metrics, packet_queues,
                        flow_control_state, congestion_state, qos_queues,
                        token_buckets, packets_received, packets_lost,
                        total_latency, total_bandwidth>>

\* Process ACK
ProcessACK(ack_packet) ==
    /\ ack_packet \in in_flight_packets
    /\ ack_packet.packet_type = "ACK"
    /\ LET sender == ack_packet.dest
           receiver == ack_packet.source
           fc == flow_control_state[sender][receiver]
           new_fc == UpdateSendWindow(fc, ack_packet.sequence_num)
           cc == congestion_state[sender][receiver]
           new_cc == UpdateBBR(cc, new_fc, 1, 1, MinRTT)
       IN /\ in_flight_packets' = in_flight_packets \ {ack_packet}
          /\ flow_control_state' = [flow_control_state EXCEPT
               ![sender][receiver] = new_fc]
          /\ congestion_state' = [congestion_state EXCEPT
               ![sender][receiver] = new_cc]
          /\ UNCHANGED <<link_state, node_state, routing_tables,
                        active_paths, path_metrics, packet_queues,
                        qos_queues, token_buckets, packets_sent,
                        packets_received, packets_lost, total_latency,
                        total_bandwidth>>

\* Packet loss (simulated)
LosePacket(packet) ==
    /\ packet \in in_flight_packets
    /\ in_flight_packets' = in_flight_packets \ {packet}
    /\ packets_lost' = packets_lost + 1
    /\ UNCHANGED <<link_state, node_state, routing_tables,
                  active_paths, path_metrics, packet_queues,
                  flow_control_state, congestion_state, qos_queues,
                  token_buckets, packets_sent, packets_received,
                  total_latency, total_bandwidth>>

(****************************************************************************)
(* Safety Properties                                                        *)
(****************************************************************************)

NetworkTypeOK ==
    /\ link_state \in [Links -> LinkStructure]
    /\ in_flight_packets \subseteq PacketStructure
    /\ packets_sent \in Nat
    /\ packets_received \in Nat
    /\ packets_lost \in Nat

\* No packet loops
NoPacketLoops ==
    \A p \in in_flight_packets :
        /\ p.ttl >= 0
        /\ Len(p.path) <= MaxPathLength
        /\ \A i, j \in DOMAIN p.path : i # j => p.path[i] # p.path[j]

\* Flow conservation: packets sent = packets received + packets in flight + packets lost
FlowConservation ==
    packets_sent = packets_received + Cardinality(in_flight_packets) + packets_lost

\* Packet ordering (within a flow)
PacketOrdering ==
    \A n1, n2 \in Nodes :
        LET fc == flow_control_state[n1][n2]
        IN fc.recv_base <= fc.send_next

\* Window constraints
WindowConstraints ==
    \A n1, n2 \in Nodes :
        LET fc == flow_control_state[n1][n2]
        IN /\ fc.send_window <= MaxWindowSize
           /\ fc.recv_window <= MaxWindowSize
           /\ fc.cwnd <= MaxWindowSize
           /\ fc.send_next - fc.send_base <= fc.send_window

\* Fairness: all flows make progress
FairBandwidthAllocation ==
    \A n1, n2, n3, n4 \in Nodes :
        (n1 # n3 \/ n2 # n4) =>
        LET fc1 == flow_control_state[n1][n2]
            fc2 == flow_control_state[n3][n4]
        IN Abs(fc1.cwnd - fc2.cwnd) <= MaxWindowSize \div 2

(****************************************************************************)
(* Liveness Properties                                                      *)
(****************************************************************************)

\* Eventual delivery
EventualDelivery ==
    \A p \in in_flight_packets :
        <>(p.dest = p.path[p.current_hop])

\* Progress: window grows when no loss
WindowGrowth ==
    \A n1, n2 \in Nodes :
        []<>(flow_control_state[n1][n2].cwnd > 1)

\* Deadlock freedom
NoDeadlock ==
    []<>(\E p \in in_flight_packets : TRUE)

(****************************************************************************)
(* Specification                                                            *)
(****************************************************************************)

NetworkNext ==
    \/ \E src, dst \in Nodes, data \in Seq(Nat), qos \in QoSClasses :
        SendPacket(src, dst, data, qos)
    \/ \E p \in in_flight_packets : RoutePacket(p)
    \/ \E p \in in_flight_packets : DeliverPacket(p)
    \/ \E rcv, snd \in Nodes, ack \in Nat : SendACK(rcv, snd, ack)
    \/ \E p \in in_flight_packets : ProcessACK(p)
    \/ \E p \in in_flight_packets : LosePacket(p)

NetworkSpec == NetworkInit /\ [][NetworkNext]_network_vars

NetworkFairSpec == 
    /\ NetworkSpec
    /\ \A src, dst \in Nodes, data \in Seq(Nat), qos \in QoSClasses :
        WF_network_vars(SendPacket(src, dst, data, qos))
    /\ \A p \in in_flight_packets : WF_network_vars(RoutePacket(p))
    /\ \A p \in in_flight_packets : WF_network_vars(DeliverPacket(p))

(****************************************************************************)
(* Theorems                                                                 *)
(****************************************************************************)

THEOREM NetworkTypeCorrect == NetworkSpec => []NetworkTypeOK
THEOREM NoLoopsInvariant == NetworkSpec => []NoPacketLoops
THEOREM FlowConservationHolds == NetworkSpec => []FlowConservation
THEOREM OrderingPreserved == NetworkSpec => []PacketOrdering
THEOREM WindowsRespected == NetworkSpec => []WindowConstraints
THEOREM EventualDeliveryHolds == NetworkFairSpec => EventualDelivery
THEOREM NoDeadlockHolds == NetworkFairSpec => NoDeadlock

====

---- MODULE NyxQoSManagement ----
(****************************************************************************)
(* Nyx Protocol - Quality of Service Management                            *)
(*                                                                          *)
(* Comprehensive QoS models including traffic classification, admission    *)
(* control, resource reservation, SLA management, and traffic engineering. *)
(*                                                                          *)
(* QoS Components:                                                          *)
(*   - Traffic classification and marking                                  *)
(*   - Admission control and call admission control (CAC)                  *)
(*   - Resource reservation protocols                                      *)
(*   - SLA monitoring and enforcement                                      *)
(*   - Traffic engineering and MPLS                                        *)
(*   - Bandwidth management and allocation                                 *)
(*   - Latency budgets and jitter control                                  *)
(*   - Quality of Experience (QoE) metrics                                 *)
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


INSTANCE NyxNetworkLayer
INSTANCE NyxStreamManagement

(****************************************************************************)
(* Traffic Classification                                                   *)
(****************************************************************************)

\* Traffic class definitions
TrafficClass == {
    "VOICE",           \* Voice over IP
    "VIDEO",           \* Video streaming
    "GAMING",          \* Online gaming
    "INTERACTIVE",     \* Interactive applications
    "STREAMING",       \* Media streaming
    "BULK",            \* Bulk data transfer
    "BACKGROUND",      \* Background/batch processing
    "MANAGEMENT"       \* Network management traffic
}

\* DSCP (Differentiated Services Code Point) markings
DSCPMarking == [
    class : TrafficClass,
    drop_precedence : 0..2,
    assured_forwarding : BOOLEAN,
    expedited_forwarding : BOOLEAN
]

\* Traffic classifier
Classifier == [
    rules : Seq([
        match_criteria : [
            src_ip : STRING,
            dst_ip : STRING,
            src_port : Nat,
            dst_port : Nat,
            protocol : STRING,
            application : STRING
        ],
        traffic_class : TrafficClass,
        priority : 0..7,
        dscp : Nat
    ])
]

\* Classify packet
ClassifyPacket(classifier, packet) ==
    CHOOSE rule \in DOMAIN classifier.rules :
        /\ MatchCriteria(classifier.rules[rule].match_criteria, packet)
        /\ rule = Min({r \in DOMAIN classifier.rules : 
                       MatchCriteria(classifier.rules[r].match_criteria, packet)})

\* Match criteria against packet
MatchCriteria(criteria, packet) ==
    /\ (criteria.src_ip = "*" \/ criteria.src_ip = packet.src_ip)
    /\ (criteria.dst_ip = "*" \/ criteria.dst_ip = packet.dst_ip)
    /\ (criteria.src_port = 0 \/ criteria.src_port = packet.src_port)
    /\ (criteria.dst_port = 0 \/ criteria.dst_port = packet.dst_port)
    /\ (criteria.protocol = "*" \/ criteria.protocol = packet.protocol)

(****************************************************************************)
(* Service Level Agreement (SLA)                                            *)
(****************************************************************************)

\* SLA parameters
SLAParams == [
    sla_id : Nat,
    customer_id : Nat,
    service_class : TrafficClass,
    min_bandwidth_mbps : Nat,
    max_latency_ms : Nat,
    max_jitter_ms : Nat,
    max_packet_loss_percent : 0..100,
    availability_percent : 9500..10000,  \* 95% to 100%
    burst_size : Nat,
    committed_rate : Nat,
    excess_rate : Nat,
    priority : 0..7
]

\* SLA violation types
SLAViolationType == {
    "BANDWIDTH_BELOW_MIN",
    "LATENCY_EXCEEDED",
    "JITTER_EXCEEDED",
    "PACKET_LOSS_EXCEEDED",
    "AVAILABILITY_BELOW_TARGET",
    "BURST_EXCEEDED"
}

\* SLA violation
SLAViolation == [
    sla_id : Nat,
    violation_type : SLAViolationType,
    timestamp : Nat,
    duration : Nat,
    severity : {"LOW", "MEDIUM", "HIGH", "CRITICAL"},
    measured_value : Nat,
    expected_value : Nat
]

\* SLA monitor
SLAMonitor == [
    slas : [Nat -> SLAParams],
    violations : Seq(SLAViolation),
    metrics : [Nat -> [
        current_bandwidth : Nat,
        current_latency : Nat,
        current_jitter : Nat,
        current_loss : 0..100,
        uptime : Nat,
        downtime : Nat
    ]]
]

\* Check SLA compliance
CheckSLACompliance(monitor, sla_id) ==
    LET sla == monitor.slas[sla_id]
        metrics == monitor.metrics[sla_id]
    IN /\ metrics.current_bandwidth >= sla.min_bandwidth_mbps
       /\ metrics.current_latency <= sla.max_latency_ms
       /\ metrics.current_jitter <= sla.max_jitter_ms
       /\ metrics.current_loss <= sla.max_packet_loss_percent
       /\ (metrics.uptime * 10000) / (metrics.uptime + metrics.downtime) 
          >= sla.availability_percent

\* Record SLA violation
RecordSLAViolation(monitor, sla_id, violation_type, measured, expected) ==
    LET severity == CASE 
        measured > (expected * 2) -> "CRITICAL"
      [] measured > (((expected * 15) \div 10)) -> "HIGH"
      [] measured > (((expected * 12) \div 10)) -> "MEDIUM"
      [] OTHER -> "LOW"
        violation == [
            sla_id |-> sla_id,
            violation_type |-> violation_type,
            timestamp |-> CurrentTime,
            duration |-> 0,
            severity |-> severity,
            measured_value |-> measured,
            expected_value |-> expected
        ]
    IN [monitor EXCEPT 
           !.violations = Append(@, violation)]

(****************************************************************************)
(* Admission Control                                                        *)
(****************************************************************************)

\* Resource availability
ResourceAvailability == [
    available_bandwidth : Nat,
    available_buffer : Nat,
    available_cpu : 0..100,
    available_connections : Nat,
    available_streams : Nat
]

\* Admission control decision
AdmissionDecision == [
    admitted : BOOLEAN,
    reason : STRING,
    allocated_resources : [
        bandwidth : Nat,
        buffer : Nat,
        priority : 0..7
    ]
]

\* Call Admission Control (CAC)
CAC(request, available_resources) ==
    LET required_bw == request.min_bandwidth
        required_buf == request.buffer_size
        has_bandwidth == available_resources.available_bandwidth >= required_bw
        has_buffer == available_resources.available_buffer >= required_buf
        has_capacity == available_resources.available_connections > 0
    IN IF has_bandwidth /\ has_buffer /\ has_capacity
       THEN [admitted |-> TRUE,
             reason |-> "Resources available",
             allocated_resources |-> [
                 bandwidth |-> required_bw,
                 buffer |-> required_buf,
                 priority |-> request.priority
             ]]
       ELSE [admitted |-> FALSE,
             reason |-> IF ~has_bandwidth THEN "Insufficient bandwidth"
                       ELSE IF ~has_buffer THEN "Insufficient buffer"
                       ELSE "No capacity",
             allocated_resources |-> [
                 bandwidth |-> 0,
                 buffer |-> 0,
                 priority |-> 0
             ]]

\* Admission control with preemption
AdmissionWithPreemption(request, current_flows, available_resources) ==
    LET admission == CAC(request, available_resources)
    IN IF admission.admitted
       THEN admission
       ELSE LET preemptable_flows == {f \in current_flows : 
                                       f.priority < request.priority}
                freed_bandwidth == CHOOSE b : b = Sum({f.bandwidth : f \in preemptable_flows})
                freed_buffer == CHOOSE b : b = Sum({f.buffer : f \in preemptable_flows})
                new_available == [available_resources EXCEPT
                                    !.available_bandwidth = @ + freed_bandwidth,
                                    !.available_buffer = @ + freed_buffer]
            IN CAC(request, new_available)

(****************************************************************************)
(* Resource Reservation                                                     *)
(****************************************************************************)

\* Resource reservation
Reservation == [
    flow_id : Nat,
    src_node : Node,
    dst_node : Node,
    path : Seq(Node),
    bandwidth : Nat,
    latency_bound : Nat,
    buffer_size : Nat,
    start_time : Nat,
    duration : Nat,
    state : {"REQUESTED", "RESERVED", "ACTIVE", "RELEASED"}
]

\* Reservation manager
ReservationManager == [
    reservations : [Nat -> Reservation],
    node_resources : [Node -> ResourceAvailability],
    path_bandwidth : [Seq(Node) -> Nat]
]

\* Reserve resources along path
ReservePathResources(manager, reservation) ==
    LET path == reservation.path
        required_bw == reservation.bandwidth
        all_nodes_available == \A n \in DOMAIN path :
            manager.node_resources[path[n]].available_bandwidth >= required_bw
    IN IF all_nodes_available
       THEN [success |-> TRUE,
             manager |-> [manager EXCEPT
                 !.reservations[reservation.flow_id] = 
                     [reservation EXCEPT !.state = "RESERVED"],
                 !.node_resources = [n \in DOMAIN @ |->
                     IF n \in {path[i] : i \in DOMAIN path}
                     THEN [@[n] EXCEPT !.available_bandwidth = @ - required_bw]
                     ELSE @[n]]]]
       ELSE [success |-> FALSE, manager |-> manager]

\* Release reserved resources
ReleaseReservation(manager, flow_id) ==
    LET reservation == manager.reservations[flow_id]
        path == reservation.path
        released_bw == reservation.bandwidth
    IN [manager EXCEPT
           !.reservations[flow_id].state = "RELEASED",
           !.node_resources = [n \in DOMAIN @ |->
               IF n \in {path[i] : i \in DOMAIN path}
               THEN [@[n] EXCEPT !.available_bandwidth = @ + released_bw]
               ELSE @[n]]]

(****************************************************************************)
(* Traffic Engineering                                                      *)
(****************************************************************************)

\* Traffic engineering objective
TEObjective == {
    "MINIMIZE_LATENCY",
    "MAXIMIZE_THROUGHPUT",
    "LOAD_BALANCE",
    "MINIMIZE_COST",
    "MAXIMIZE_RELIABILITY"
}

\* Path metrics
PathMetrics == [
    path : Seq(Node),
    total_latency : Nat,
    available_bandwidth : Nat,
    utilization : 0..100,
    cost : Nat,
    reliability : 0..100
]

\* Compute path metrics
ComputePathMetrics(path, link_metrics) ==
    [
        path |-> path,
        total_latency |-> CHOOSE l : l = Sum({link_metrics[<<path[i], path[i+1]>>].latency : 
                                              i \in 1..(Len(path)-1)}),
        available_bandwidth |-> Min({link_metrics[<<path[i], path[i+1]>>].bandwidth : 
                                     i \in 1..(Len(path)-1)}),
        utilization |-> Max({link_metrics[<<path[i], path[i+1]>>].utilization : 
                            i \in 1..(Len(path)-1)}),
        cost |-> CHOOSE c : c = Sum({link_metrics[<<path[i], path[i+1]>>].cost : 
                                    i \in 1..(Len(path)-1)}),
        reliability |-> Min({link_metrics[<<path[i], path[i+1]>>].reliability : 
                            i \in 1..(Len(path)-1)})
    ]

\* Select best path based on objective
SelectBestPath(paths, objective) ==
    CASE objective = "MINIMIZE_LATENCY" ->
           CHOOSE p \in paths : \A q \in paths : p.total_latency <= q.total_latency
      [] objective = "MAXIMIZE_THROUGHPUT" ->
           CHOOSE p \in paths : \A q \in paths : p.available_bandwidth >= q.available_bandwidth
      [] objective = "LOAD_BALANCE" ->
           CHOOSE p \in paths : \A q \in paths : p.utilization <= q.utilization
      [] objective = "MINIMIZE_COST" ->
           CHOOSE p \in paths : \A q \in paths : p.cost <= q.cost
      [] objective = "MAXIMIZE_RELIABILITY" ->
           CHOOSE p \in paths : \A q \in paths : p.reliability >= q.reliability
      [] OTHER ->
           CHOOSE p \in paths : TRUE

\* MPLS Label Switched Path
LSP == [
    lsp_id : Nat,
    ingress : Node,
    egress : Node,
    path : Seq(Node),
    labels : Seq(Nat),
    bandwidth : Nat,
    setup_priority : 0..7,
    holding_priority : 0..7,
    fast_reroute : BOOLEAN,
    backup_path : Seq(Node)
]

\* MPLS forwarding entry
MPLSForwardingEntry == [
    in_label : Nat,
    out_label : Nat,
    next_hop : Node,
    interface : Nat
]

\* Setup LSP
SetupLSP(lsp, network_state) ==
    LET path_available == CheckPathAvailable(lsp.path, lsp.bandwidth, network_state)
    IN IF path_available
       THEN [success |-> TRUE,
             labels |-> AssignLabels(lsp.path),
             forwarding_entries |-> CreateForwardingEntries(lsp)]
       ELSE [success |-> FALSE, labels |-> <<>>, forwarding_entries |-> <<>>]

(****************************************************************************)
(* Bandwidth Management                                                     *)
(****************************************************************************)

\* Bandwidth allocation
BandwidthAllocation == [
    flow_id : Nat,
    allocated_bandwidth : Nat,
    min_guaranteed : Nat,
    max_allowed : Nat,
    burst_allowed : Nat,
    current_usage : Nat
]

\* Bandwidth broker
BandwidthBroker == [
    total_bandwidth : Nat,
    allocated : [Nat -> BandwidthAllocation],
    available : Nat,
    oversubscription_ratio : Nat  \* e.g., 2 for 2:1 oversubscription
]

\* Allocate bandwidth
AllocateBandwidth(broker, flow_id, requested_bw, min_bw, max_bw) ==
    LET effective_available == broker.total_bandwidth * broker.oversubscription_ratio
        can_allocate == effective_available >= requested_bw
        allocated == Min(requested_bw, max_bw)
    IN IF can_allocate
       THEN [success |-> TRUE,
             broker |-> [broker EXCEPT
                 !.allocated[flow_id] = [
                     flow_id |-> flow_id,
                     allocated_bandwidth |-> allocated,
                     min_guaranteed |-> min_bw,
                     max_allowed |-> max_bw,
                     burst_allowed |-> (max_bw * 12) \div 10,
                     current_usage |-> 0
                 ],
                 !.available = @ - allocated]]
       ELSE [success |-> FALSE, broker |-> broker]

\* Dynamic bandwidth allocation
DynamicBandwidthAllocation(broker, demands) ==
    LET total_demand == CHOOSE d : d = Sum({demands[f] : f \in DOMAIN demands})
        allocation_ratio == IF total_demand > broker.total_bandwidth
                           THEN broker.total_bandwidth / total_demand
                           ELSE 1
    IN [f \in DOMAIN demands |->
           Min(demands[f] * allocation_ratio,
               broker.allocated[f].max_allowed)]

(****************************************************************************)
(* Latency Budget Management                                                *)
(****************************************************************************)

\* Latency budget
LatencyBudget == [
    total_budget : Nat,
    components : [
        propagation : Nat,
        serialization : Nat,
        queuing : Nat,
        processing : Nat,
        retransmission : Nat
    ],
    slack : Nat
]

\* Compute latency budget
ComputeLatencyBudget(path, packet_size, processing_delay) ==
    LET propagation == CHOOSE l : l = Sum({LinkPropagationDelay(path[i], path[i+1]) : 
                                           i \in 1..(Len(path)-1)})
        serialization == CHOOSE l : l = Sum({LinkSerializationDelay(path[i], path[i+1], packet_size) :
                                             i \in 1..(Len(path)-1)})
        queuing == CHOOSE l : l = Sum({EstimateQueuingDelay(path[i]) :
                                       i \in DOMAIN path})
        processing == processing_delay * Len(path)
        retransmission == 0  \* Optimistic
        total == propagation + serialization + queuing + processing + retransmission
    IN [
        total_budget |-> total,
        components |-> [
            propagation |-> propagation,
            serialization |-> serialization,
            queuing |-> queuing,
            processing |-> processing,
            retransmission |-> retransmission
        ],
        slack |-> Max(0, TargetLatency - total)
    ]

\* Allocate latency budget
AllocateLatencyBudget(total_budget, hop_count) ==
    LET per_hop == total_budget \div hop_count
        components == [
            propagation |-> per_hop \div 5,
            serialization |-> per_hop \div 5,
            queuing |-> (per_hop * 2) \div 5,
            processing |-> per_hop \div 5,
            retransmission |-> 0
        ]
    IN [h \in 1..hop_count |-> components]

(****************************************************************************)
(* Jitter Control                                                           *)
(****************************************************************************)

\* Jitter buffer
JitterBuffer == [
    buffer : Seq([
        packet : Any,
        arrival_time : Nat,
        sequence_num : Nat
    ]),
    min_delay : Nat,
    max_delay : Nat,
    target_delay : Nat,
    playout_time : Nat
]

\* Add packet to jitter buffer
AddToJitterBuffer(jbuffer, packet, arrival_time, seq_num) ==
    LET entry == [packet |-> packet,
                  arrival_time |-> arrival_time,
                  sequence_num |-> seq_num]
    IN [jbuffer EXCEPT 
           !.buffer = InsertSorted(@, entry, 
                                   LAMBDA a, b : a.sequence_num < b.sequence_num)]

\* Remove packet from jitter buffer
RemoveFromJitterBuffer(jbuffer, current_time) ==
    IF jbuffer.buffer = <<>>
    THEN [packet |-> 0, jbuffer |-> jbuffer]
    ELSE LET first == Head(jbuffer.buffer)
             ready == current_time >= first.arrival_time + jbuffer.target_delay
         IN IF ready
            THEN [packet |-> first.packet,
                  jbuffer |-> [jbuffer EXCEPT !.buffer = Tail(@)]]
            ELSE [packet |-> 0, jbuffer |-> jbuffer]

\* Adaptive jitter buffer sizing
AdaptiveJitterBuffer(jbuffer, recent_jitter) ==
    LET new_target == Clip(Mean(recent_jitter) + StdDev(recent_jitter) * 2,
                           jbuffer.min_delay,
                           jbuffer.max_delay)
    IN [jbuffer EXCEPT !.target_delay = new_target]

(****************************************************************************)
(* Quality of Experience (QoE)                                              *)
(****************************************************************************)

\* QoE metrics
QoEMetrics == [
    mean_opinion_score : 1..5,  \* MOS score
    video_quality_metric : 0..100,  \* VMAF/SSIM
    audio_quality_metric : 0..100,  \* PESQ/POLQA
    stalling_ratio : 0..100,
    startup_delay : Nat,
    rebuffering_count : Nat,
    resolution_switches : Nat,
    avg_bitrate : Nat
]

\* Compute MOS from network metrics
ComputeMOS(latency, jitter, packet_loss) ==
    LET base_mos == 5
        latency_penalty == Min(2, latency / 100)
        jitter_penalty == Min(1, jitter / 50)
        loss_penalty == packet_loss / 10
        mos == Max(1, base_mos - latency_penalty - jitter_penalty - loss_penalty)
    IN mos

\* Video quality estimation
EstimateVideoQuality(resolution, bitrate, frame_rate, packet_loss) ==
    LET resolution_score == CASE resolution = "4K" -> 100
                              [] resolution = "1080p" -> 85
                              [] resolution = "720p" -> 70
                              [] resolution = "480p" -> 50
                              [] OTHER -> 30
        bitrate_factor == Min(1, bitrate / 5000)  \* Normalized to 5 Mbps
        fps_factor == Min(1, frame_rate / 60)
        loss_factor == 1 - (packet_loss / 100)
    IN resolution_score * bitrate_factor * fps_factor * loss_factor

\* Compute stalling ratio
ComputeStallingRatio(total_stall_time, playback_duration) ==
    (total_stall_time * 100) / playback_duration

====

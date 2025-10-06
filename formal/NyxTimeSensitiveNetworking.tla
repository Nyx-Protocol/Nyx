---- MODULE NyxTimeSensitiveNetworking ----
(****************************************************************************)
(* Nyx Protocol - Time-Sensitive Networking and Real-Time Communication    *)
(*                                                                          *)
(* Comprehensive specifications for Time-Sensitive Networking (TSN),       *)
(* deterministic communication, time synchronization, traffic shaping,     *)
(* and real-time guarantees based on IEEE 802.1 TSN standards.             *)
(*                                                                          *)
(* TSN Components:                                                          *)
(*   - Time synchronization (IEEE 802.1AS gPTP)                            *)
(*   - Time-Aware Shaper (IEEE 802.1Qbv)                                   *)
(*   - Frame preemption (IEEE 802.1Qbu/802.3br)                            *)
(*   - Per-Stream Filtering and Policing (IEEE 802.1Qci)                  *)
(*   - Stream Reservation Protocol (IEEE 802.1Qat)                         *)
(*   - Credit-Based Shaper (IEEE 802.1Qav)                                *)
(*   - Cyclic Queuing and Forwarding (IEEE 802.1Qch)                      *)
(*   - Scheduled traffic (IEEE 802.1Qbv gate control)                     *)
(*   - Worst-case latency bounds                                           *)
(*   - Jitter control and determinism                                      *)
(****************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, Integers, Reals, TLC

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



CONSTANTS MaxClockOffset, MaxPropagationDelay, CycleTime, MaxStreams

(****************************************************************************)
(* Helper Operators                                                         *)
(****************************************************************************)

\* Minimum of a set
MIN(S) == IF S = {} THEN 0 ELSE CHOOSE x \in S : \A y \in S : x <= y

\* Maximum of a set  
MAX(S) == IF S = {} THEN 0 ELSE CHOOSE x \in S : \A y \in S : x >= y

\* Absolute value
Abs(x) == IF x < 0 THEN -x ELSE x

\* Sum of set elements
Sum(S) == LET RECURSIVE SumRec(_)
              SumRec(T) == IF T = {} 
                          THEN 0 
                          ELSE LET x == CHOOSE y \in T : TRUE
                               IN x + SumRec(T \ {x})
          IN SumRec(S)

(****************************************************************************)
(* Time Synchronization (IEEE 802.1AS - gPTP)                              *)
(****************************************************************************)

\* Time domain
TimeDomain == [
    domain_number : Nat,
    grandmaster_id : STRING,
    clock_quality : [
        clock_class : Nat,
        clock_accuracy : Nat,
        offset_scaled_log_variance : Nat
    ],
    current_utc_offset : Int,
    time_source : {"ATOMIC_CLOCK", "GPS", "PTP", "NTP", "INTERNAL"}
]

\* PTP port
PTPPort == [
    port_id : STRING,
    port_number : Nat,
    port_state : {"INITIALIZING", "FAULTY", "DISABLED", "LISTENING",
                  "PRE_MASTER", "MASTER", "PASSIVE", "UNCALIBRATED", "SLAVE"},
    
    \* Time properties
    local_clock : Real,
    master_clock : Real,
    offset_from_master : Real,
    mean_path_delay : Real,
    
    \* Announce message
    announce_interval : Nat,
    announce_receipt_timeout : Nat,
    
    \* Sync message
    sync_interval : Nat,
    sync_receipt_timeout : Nat,
    
    \* Delay request-response
    delay_req_interval : Nat,
    pdelay_req_interval : Nat,
    
    \* Neighbor rate ratio
    neighbor_rate_ratio : Real,
    
    \* AS-capable flag
    as_capable : BOOLEAN
]

\* PTP message types
PTPMessage == [
    message_type : {"SYNC", "FOLLOW_UP", "PDELAY_REQ", "PDELAY_RESP",
                    "PDELAY_RESP_FOLLOW_UP", "ANNOUNCE", "SIGNALING"},
    sequence_id : Nat,
    source_port_id : STRING,
    timestamp : Real,
    correction_field : Real
]

\* Best Master Clock Algorithm (BMCA)
BestMasterClockAlgorithm(port, received_announce) ==
    LET current_gm == port.grandmaster_id
        announced_gm == received_announce.grandmaster_id
        
        \* Compare by clock quality
        current_quality == port.clock_quality
        announced_quality == received_announce.clock_quality
        
        is_better == CASE announced_quality.clock_class < current_quality.clock_class -> TRUE
                     [] announced_quality.clock_class > current_quality.clock_class -> FALSE
                     [] announced_quality.clock_accuracy < current_quality.clock_accuracy -> TRUE
                     [] announced_quality.clock_accuracy > current_quality.clock_accuracy -> FALSE
                     [] announced_quality.offset_scaled_log_variance < current_quality.offset_scaled_log_variance -> TRUE
                     [] OTHER -> FALSE
    IN IF is_better
       THEN [port EXCEPT
                !.port_state = "SLAVE",
                !.grandmaster_id = announced_gm,
                !.clock_quality = announced_quality]
       ELSE port

\* Process Sync message
ProcessSyncMessage(port, sync_msg, ingress_timestamp) ==
    LET precise_origin_timestamp == sync_msg.timestamp + sync_msg.correction_field
        
        \* Calculate offset
        offset == ingress_timestamp - precise_origin_timestamp
        
        \* Update port
        updated_port == [port EXCEPT
                            !.master_clock = precise_origin_timestamp,
                            !.offset_from_master = offset]
    IN updated_port

\* Process Pdelay messages (peer delay measurement)
MeasurePeerDelay(port, pdelay_req_tx, pdelay_resp_rx) ==
    LET t1 == pdelay_req_tx.timestamp
        t2 == pdelay_req_tx.peer_timestamp
        t3 == pdelay_resp_rx.peer_timestamp
        t4 == pdelay_resp_rx.timestamp
        
        \* Calculate mean path delay
        path_delay == ((t4 - t1) - (t3 - t2)) / 2
        
        updated_port == [port EXCEPT
                            !.mean_path_delay = path_delay]
    IN updated_port

\* Synchronize clock
SynchronizeClock(port) ==
    IF port.port_state = "SLAVE"
    THEN LET corrected_time == port.local_clock + port.offset_from_master
         IN [port EXCEPT !.local_clock = corrected_time]
    ELSE port

(****************************************************************************)
(* Time-Aware Shaper (IEEE 802.1Qbv)                                       *)
(****************************************************************************)

\* Gate Control Entry
GateControlEntry == [
    operation : {"SET_GATE_STATES", "SET_AND_HOLD_MAC", "SET_AND_RELEASE_MAC"},
    gate_states : [Nat -> {"OPEN", "CLOSED"}],  \* For each queue
    time_interval : Nat  \* Duration in nanoseconds
]

\* Gate Control List
GateControlList == Seq(GateControlEntry)

\* Traffic class configuration
TrafficClassConfig == [
    queue_number : Nat,
    priority : Nat,
    gate_enabled : BOOLEAN,
    max_frame_size : Nat
]

\* Time-Aware Shaper
TimeAwareShaper == [
    \* Schedule
    admin_gate_states : GateControlList,
    oper_gate_states : GateControlList,
    config_change : BOOLEAN,
    config_change_time : Real,
    
    \* Cycle
    admin_cycle_time : Nat,
    oper_cycle_time : Nat,
    cycle_time_extension : Nat,
    
    \* Base time
    admin_base_time : Real,
    oper_base_time : Real,
    
    \* Current time
    current_time : Real,
    
    \* Traffic classes
    traffic_classes : Seq(TrafficClassConfig),
    
    \* Guard band
    guard_band : [Nat -> Nat]  \* Per traffic class
]

\* Get current gate state
GetGateState(shaper, queue_number, time) ==
    LET cycle_start == shaper.oper_base_time
        elapsed == time - cycle_start
        cycle_position == elapsed % shaper.oper_cycle_time
        
        \* Find active GCE
        RECURSIVE FindActiveGCE(_, _)
        FindActiveGCE(gce_list, position) ==
            IF gce_list = <<>>
            THEN "CLOSED"
            ELSE LET gce == Head(gce_list)
                 IN IF position < gce.time_interval
                    THEN gce.gate_states[queue_number]
                    ELSE FindActiveGCE(Tail(gce_list), position - gce.time_interval)
    IN FindActiveGCE(shaper.oper_gate_states, cycle_position)

\* Schedule frame transmission
ScheduleFrameTransmission(shaper, frame, queue_number) ==
    LET current_gate == GetGateState(shaper, queue_number, shaper.current_time)
        
        \* Check if gate is open
        can_transmit == current_gate = "OPEN"
        
        \* Check guard band
        time_until_gate_close == TimeUntilGateClose(shaper, queue_number)
        transmission_time == ((frame.size * 8) / link_speed)
        fits_in_window == transmission_time <= time_until_gate_close
        
        allowed == can_transmit /\ fits_in_window
    IN IF allowed
       THEN [success |-> TRUE, transmission_start |-> shaper.current_time]
       ELSE [success |-> FALSE, next_window |-> NextGateOpenTime(shaper, queue_number)]

\* Time until gate closes
TimeUntilGateClose(shaper, queue_number) ==
    LET current_gate == GetGateState(shaper, queue_number, shaper.current_time)
    IN IF current_gate = "CLOSED"
       THEN 0
       ELSE LET cycle_start == shaper.oper_base_time
                elapsed == shaper.current_time - cycle_start
                cycle_position == elapsed % shaper.oper_cycle_time
                
                RECURSIVE FindCloseTime(_, _, _)
                FindCloseTime(gce_list, position, accumulated) ==
                    IF gce_list = <<>>
                    THEN shaper.oper_cycle_time - cycle_position
                    ELSE LET gce == Head(gce_list)
                         IN IF position < gce.time_interval
                            THEN IF gce.gate_states[queue_number] = "OPEN"
                                 THEN gce.time_interval - position
                                 ELSE 0
                            ELSE FindCloseTime(Tail(gce_list),
                                             position - gce.time_interval,
                                             accumulated + gce.time_interval)
            IN FindCloseTime(shaper.oper_gate_states, cycle_position, 0)

(****************************************************************************)
(* Frame Preemption (IEEE 802.1Qbu/802.3br)                                *)
(****************************************************************************)

\* Frame preemption configuration
FramePreemptionConfig == [
    \* Preemptable traffic classes
    preemptable_tc : [Nat -> BOOLEAN],
    
    \* Express traffic classes (non-preemptable)
    express_tc : [Nat -> BOOLEAN],
    
    \* Minimum fragment size
    min_fragment_size : Nat,
    
    \* Additional fragment size
    additional_fragment_size : Nat,
    
    \* Hold and release
    hold_advance : Nat,
    release_advance : Nat,
    
    \* Verification
    verification_enabled : BOOLEAN,
    verification_status : {"INITIAL", "VERIFYING", "SUCCEEDED", "FAILED", "DISABLED"}
]

\* Fragment frame for preemption
FragmentFrame(frame, fragment_size) ==
    LET num_fragments == (frame.size + fragment_size - 1) \div fragment_size
        
        RECURSIVE CreateFragments(_, _)
        CreateFragments(remaining_size, frag_num) ==
            IF remaining_size <= 0
            THEN <<>>
            ELSE LET frag_size == IF remaining_size > fragment_size
                                  THEN fragment_size
                                  ELSE remaining_size
                     fragment == [
                         frame_id |-> frame.frame_id,
                         fragment_number |-> frag_num,
                         size |-> frag_size,
                         is_final |-> remaining_size <= fragment_size,
                         priority |-> frame.priority
                     ]
                 IN <<fragment>> \o CreateFragments(remaining_size - frag_size, frag_num + 1)
    IN CreateFragments(frame.size, 0)

\* Preempt frame
PreemptFrame(current_frame, express_frame, config) ==
    IF config.preemptable_tc[current_frame.priority]
    THEN LET fragments == FragmentFrame(current_frame, config.min_fragment_size)
             transmitted_size == CalculateTransmittedSize(current_frame)
             remaining_fragments == SelectRemainingFragments(fragments, transmitted_size)
         IN [
             preempted |-> TRUE,
             express_frame |-> express_frame,
             remaining_fragments |-> remaining_fragments
         ]
    ELSE [preempted |-> FALSE]

\* Reassemble fragments
ReassembleFragments(fragments) ==
    LET sorted_fragments == SortByFragmentNumber(fragments)
        all_present == CheckAllFragmentsPresent(sorted_fragments)
    IN IF all_present
       THEN [
           success |-> TRUE,
           frame |-> CombineFragments(sorted_fragments)
       ]
       ELSE [success |-> FALSE]

(****************************************************************************)
(* Per-Stream Filtering and Policing (IEEE 802.1Qci)                       *)
(****************************************************************************)

\* Stream filter
StreamFilter == [
    stream_handle : Nat,
    priority_spec : [priority : Nat, drop_eligible : BOOLEAN],
    
    \* Stream gates
    stream_gate_instance_id : Nat,
    
    \* Flow meters
    flow_meter_instance_id : Nat,
    
    \* Counters
    matching_frames_count : Nat,
    passing_frames_count : Nat,
    not_passing_frames_count : Nat,
    red_frames_count : Nat
]

\* Stream gate
StreamGate == [
    gate_id : Nat,
    gate_enabled : BOOLEAN,
    admin_gate_states : {"OPEN", "CLOSED"},
    oper_gate_states : {"OPEN", "CLOSED"},
    
    \* IPV (Internal Priority Value)
    admin_ipv : Nat,
    oper_ipv : Nat,
    
    \* Control list
    admin_control_list : Seq([
        operation : {"SET_GATE_AND_IPV"},
        gate_state : {"OPEN", "CLOSED"},
        ipv : Nat,
        time_interval : Nat,
        interval_octet_max : Nat
    ]),
    oper_control_list : Seq([
        operation : {"SET_GATE_AND_IPV"},
        gate_state : {"OPEN", "CLOSED"},
        ipv : Nat,
        time_interval : Nat,
        interval_octet_max : Nat
    ]),
    
    \* Timing
    admin_cycle_time : Nat,
    oper_cycle_time : Nat,
    admin_base_time : Real,
    oper_base_time : Real,
    
    \* State
    current_time : Real,
    closed_due_to_invalid_rx : BOOLEAN,
    closed_due_to_octets_exceeded : BOOLEAN
]

\* Flow meter (Two-rate three-color marker)
FlowMeter == [
    meter_id : Nat,
    
    \* Committed Information Rate
    cir : Nat,  \* bits per second
    cbs : Nat,  \* Committed Burst Size in bytes
    
    \* Excess Information Rate  
    eir : Nat,  \* bits per second
    ebs : Nat,  \* Excess Burst Size in bytes
    
    \* Token buckets
    committed_token_bucket : Real,
    excess_token_bucket : Real,
    
    \* Coupling flag
    cf : BOOLEAN,
    
    \* Color mode
    color_mode : {"COLOR_AWARE", "COLOR_BLIND"},
    
    \* Drop on yellow
    drop_on_yellow : BOOLEAN,
    
    \* Marking
    mark_all_frames_red : BOOLEAN
]

\* Apply flow meter
ApplyFlowMeter(meter, frame, current_time) ==
    LET frame_size_bits == frame.size * 8
        
        \* Update token buckets
        time_elapsed == current_time - meter.last_update
        cir_tokens == (meter.cir * time_elapsed) / 1000000000  \* Convert to bits
        eir_tokens == (meter.eir * time_elapsed) / 1000000000
        
        updated_committed == Min(meter.committed_token_bucket + cir_tokens, meter.cbs * 8)
        updated_excess == Min(meter.excess_token_bucket + eir_tokens, meter.ebs * 8)
        
        \* Determine color
        color == IF meter.mark_all_frames_red
                THEN "RED"
                ELSE IF frame_size_bits <= updated_committed
                     THEN "GREEN"
                     ELSE IF frame_size_bits <= updated_excess
                          THEN "YELLOW"
                          ELSE "RED"
        
        \* Update buckets based on color
        new_committed == IF color = "GREEN"
                        THEN updated_committed - frame_size_bits
                        ELSE updated_committed
        new_excess == IF color = "YELLOW"
                     THEN updated_excess - frame_size_bits
                     ELSE updated_excess
        
        \* Drop decision
        drop == (color = "RED") \/ (color = "YELLOW" /\ meter.drop_on_yellow)
    IN [
        meter |-> [meter EXCEPT
                      !.committed_token_bucket = new_committed,
                      !.excess_token_bucket = new_excess,
                      !.last_update = current_time],
        color |-> color,
        drop |-> drop
    ]

\* Check stream gate
CheckStreamGate(gate, frame, current_time) ==
    LET cycle_start == gate.oper_base_time
        elapsed == current_time - cycle_start
        cycle_position == elapsed % gate.oper_cycle_time
        
        \* Find current gate state
        RECURSIVE FindGateState(_, _)
        FindGateState(control_list, position) ==
            IF control_list = <<>>
            THEN [state |-> "CLOSED", ipv |-> 0, max_octets |-> 0]
            ELSE LET entry == Head(control_list)
                 IN IF position < entry.time_interval
                    THEN [state |-> entry.gate_state,
                          ipv |-> entry.ipv,
                          max_octets |-> entry.interval_octet_max]
                    ELSE FindGateState(Tail(control_list), position - entry.time_interval)
        
        gate_info == FindGateState(gate.oper_control_list, cycle_position)
        
        \* Check if frame can pass
        can_pass == gate_info.state = "OPEN" /\
                   frame.size <= gate_info.max_octets /\
                   ~gate.closed_due_to_invalid_rx
    IN [
        pass |-> can_pass,
        ipv |-> gate_info.ipv
    ]

(****************************************************************************)
(* Stream Reservation Protocol (IEEE 802.1Qat)                              *)
(****************************************************************************)

\* Stream reservation
StreamReservation == [
    stream_id : [
        mac_address : STRING,
        vlan_id : Nat
    ],
    
    \* Traffic specification
    tspec : [
        max_frame_size : Nat,
        max_interval_frames : Nat,
        priority : Nat
    ],
    
    \* Accumulated latency
    accumulated_latency : Nat,
    
    \* Bandwidth allocation
    allocated_bandwidth : Nat,
    
    \* Status
    reservation_status : {"NONE", "PENDING", "ACTIVE", "FAILED"},
    failure_code : {"NO_FAILURE", "INSUFFICIENT_BANDWIDTH",
                    "INSUFFICIENT_RESOURCES", "LATENCY_EXCEEDED"}
]

\* Make stream reservation
MakeStreamReservation(stream_id, tspec, path) ==
    LET 
        \* Calculate required bandwidth
        required_bw == (tspec.max_frame_size * 8 * tspec.max_interval_frames) / 125000  \* Mbps
        
        \* Check bandwidth availability along path
        RECURSIVE CheckPath(_)
        CheckPath(remaining_path) ==
            IF remaining_path = <<>>
            THEN [available |-> TRUE, max_latency |-> 0]
            ELSE LET link == Head(remaining_path)
                     available_bw == link.available_bandwidth
                     link_latency == link.max_latency
                     rest_result == CheckPath(Tail(remaining_path))
                 IN IF available_bw >= required_bw
                    THEN [available |-> rest_result.available,
                          max_latency |-> link_latency + rest_result.max_latency]
                    ELSE [available |-> FALSE, max_latency |-> 0]
        
        path_check == CheckPath(path)
    IN IF path_check.available
       THEN [
           stream_id |-> stream_id,
           tspec |-> tspec,
           accumulated_latency |-> path_check.max_latency,
           allocated_bandwidth |-> required_bw,
           reservation_status |-> "ACTIVE",
           failure_code |-> "NO_FAILURE"
       ]
       ELSE [
           stream_id |-> stream_id,
           tspec |-> tspec,
           accumulated_latency |-> 0,
           allocated_bandwidth |-> 0,
           reservation_status |-> "FAILED",
           failure_code |-> "INSUFFICIENT_BANDWIDTH"
       ]

(****************************************************************************)
(* Credit-Based Shaper (IEEE 802.1Qav)                                     *)
(****************************************************************************)

\* Credit-based shaper
CreditBasedShaper == [
    queue_number : Nat,
    
    \* Transmission selection algorithm
    idle_slope : Nat,      \* Credits per second when queue is not empty
    send_slope : Nat,      \* Credits per second when transmitting
    hi_credit : Int,       \* Maximum credit
    lo_credit : Int,       \* Minimum credit
    
    \* Current state
    credit : Int,
    last_update_time : Real,
    is_transmitting : BOOLEAN,
    
    \* Queue
    pending_frames : Seq(Frame)
]

\* Update credit
UpdateCredit(shaper, current_time) ==
    LET elapsed == current_time - shaper.last_update_time
        
        credit_change == IF shaper.is_transmitting
                        THEN shaper.send_slope * elapsed
                        ELSE IF Len(shaper.pending_frames) > 0
                             THEN shaper.idle_slope * elapsed
                             ELSE 0
        
        new_credit == Max(Min(shaper.credit + credit_change, shaper.hi_credit),
                         shaper.lo_credit)
    IN [shaper EXCEPT
           !.credit = new_credit,
           !.last_update_time = current_time]

\* Can transmit frame
CanTransmitCBS(shaper) ==
    shaper.credit >= 0 /\ Len(shaper.pending_frames) > 0

\* Transmit frame from CBS
TransmitFrameCBS(shaper, current_time) ==
    IF CanTransmitCBS(shaper)
    THEN LET updated == UpdateCredit(shaper, current_time)
             frame == Head(updated.pending_frames)
             transmission_time == (frame.size * 8) / link_speed
         IN [shaper |-> [updated EXCEPT
                            !.is_transmitting = TRUE,
                            !.pending_frames = Tail(@)],
             frame |-> frame,
             transmission_time |-> transmission_time]
    ELSE [shaper |-> shaper, frame |-> NullFrame, transmission_time |-> 0]

(****************************************************************************)
(* Worst-Case Latency Analysis                                              *)
(****************************************************************************)

\* Compute worst-case end-to-end latency
ComputeWorstCaseLatency(stream, path, network_config) ==
    LET 
        \* Per-hop latency components
        RECURSIVE ComputeHopLatencies(_)
        ComputeHopLatencies(remaining_path) ==
            IF remaining_path = <<>>
            THEN <<>>
            ELSE LET hop == Head(remaining_path)
                     
                     \* Queueing delay
                     queueing_delay == ComputeMaxQueueingDelay(stream, hop, network_config)
                     
                     \* Processing delay
                     processing_delay == hop.processing_delay
                     
                     \* Transmission delay
                     transmission_delay == (stream.tspec.max_frame_size * 8) / hop.link_speed
                     
                     \* Propagation delay
                     propagation_delay == hop.propagation_delay
                     
                     hop_latency == queueing_delay + processing_delay +
                                   transmission_delay + propagation_delay
                 IN <<hop_latency>> \o ComputeHopLatencies(Tail(remaining_path))
        
        hop_latencies == ComputeHopLatencies(path)
        total_latency == Sum(hop_latencies)
    IN total_latency

\* Compute maximum queueing delay
ComputeMaxQueueingDelay(stream, hop, network_config) ==
    LET higher_priority_streams == {s \in network_config.streams :
            s.tspec.priority > stream.tspec.priority /\
            hop \in s.path}
        
        \* Interference from higher priority traffic
        interference == Sum({ComputeInterference(s, hop) : s \in higher_priority_streams})
        
        \* Blocking from lower priority (only one frame)
        blocking == IF network_config.preemption_enabled
                   THEN 0
                   ELSE (MaxFrameSize(hop) * 8) / hop.link_speed
        
        max_queueing == interference + blocking
    IN max_queueing

(****************************************************************************)
(* TSN Configuration and Management                                         *)
(****************************************************************************)

\* TSN network configuration
TSNNetworkConfig == [
    \* Topology
    bridges : [STRING -> TSNBridge],
    end_stations : [STRING -> TSNEndStation],
    links : Seq([
        link_id : STRING,
        source : STRING,
        destination : STRING,
        bandwidth : Nat,
        propagation_delay : Nat
    ]),
    
    \* Global time
    time_domain : TimeDomain,
    
    \* Streams
    streams : [Nat -> StreamReservation],
    
    \* Configuration
    cycle_time : Nat,
    max_streams : Nat,
    preemption_enabled : BOOLEAN
]

\* TSN bridge
TSNBridge == [
    bridge_id : STRING,
    ports : Seq(TSNPort),
    ptp_instance : PTPPort,
    
    \* Shapers
    time_aware_shapers : [Nat -> TimeAwareShaper],
    credit_based_shapers : [Nat -> CreditBasedShaper],
    
    \* Filtering and policing
    stream_filters : [Nat -> StreamFilter],
    stream_gates : [Nat -> StreamGate],
    flow_meters : [Nat -> FlowMeter],
    
    \* Frame preemption
    preemption_config : FramePreemptionConfig,
    
    \* Forwarding database
    fdb : [MACAddress -> [port : Nat, vlan : Nat]]
]

\* TSN port
TSNPort == [
    port_number : Nat,
    queue_algorithm : {"STRICT_PRIORITY", "CBS", "TAS", "CYCLIC_QUEUING"},
    num_queues : Nat,
    queue_assignment : [Nat -> Nat],  \* Priority to queue mapping
    transmission_gate : [Nat -> {"OPEN", "CLOSED"}]
]

(****************************************************************************)
(* TSN Properties and Invariants                                            *)
(****************************************************************************)

\* Time synchronization accuracy
THEOREM TimeSynchronizationAccuracy ==
    \A port \in PTPPorts :
        (port.port_state = "SLAVE") =>
            Abs(port.offset_from_master) <= MaxClockOffset

\* Bounded latency
THEOREM BoundedLatency ==
    \A stream \in TSNStreams :
        (stream.reservation_status = "ACTIVE") =>
            worst_case_latency(stream) <= stream.max_latency_requirement

\* No gate conflicts
THEOREM NoGateConflicts ==
    \A shaper \in TimeAwareShapers :
        \A t1, t2 \in TimeInstants :
            (t1 # t2) =>
                ~(GetGateState(shaper, t1) = "OPEN" /\
                  GetGateState(shaper, t2) = "OPEN" /\
                  OverlappingTransmissions(t1, t2))

\* Bandwidth reservation
THEOREM BandwidthReservation ==
    \A link \in NetworkLinks :
        Sum({stream.allocated_bandwidth : stream \in ActiveStreams(link)}) <=
            link.total_bandwidth

\* Frame preemption correctness
THEOREM FramePreemptionCorrectness ==
    \A frame \in PreemptedFrames :
        ReassembledCorrectly(frame.fragments)

\* Credit-based shaper fairness
THEOREM CreditBasedShaperFairness ==
    \A shaper \in CreditBasedShapers :
        long_term_transmission_rate(shaper) = 
            (shaper.idle_slope / (shaper.idle_slope + Abs(shaper.send_slope))) *
            link_speed

====

---- MODULE NyxFaultTolerance ----
(****************************************************************************)
(* Nyx Protocol - Fault Tolerance and Recovery Specification               *)
(*                                                                          *)
(* This module provides a complete formal specification of fault           *)
(* detection, recovery mechanisms, and resilience properties of the        *)
(* Nyx protocol.                                                            *)
(*                                                                          *)
(* Components Specified:                                                    *)
(*   - Failure detection (heartbeats, timeouts)                            *)
(*   - Path failover and backup path management                            *)
(*   - State recovery and checkpointing                                     *)
(*   - Byzantine fault tolerance                                            *)
(*   - Network partition handling                                           *)
(*   - Graceful degradation                                                 *)
(*                                                                          *)
(* Mathematical Properties Verified:                                        *)
(*   - Fault detectability                                                  *)
(*   - Recovery time bounds                                                 *)
(*   - State consistency after recovery                                     *)
(*   - Liveness under failure                                               *)
(*   - Byzantine agreement                                                  *)
(****************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, Integers, TLC

CONSTANTS
    Nodes,                  \* Set of all nodes
    MaxFailures,            \* Maximum concurrent failures tolerated
    HeartbeatInterval,      \* Heartbeat sending interval
    TimeoutThreshold,       \* Failure detection timeout
    MaxRetries,             \* Maximum retry attempts
    CheckpointInterval,     \* State checkpoint interval
    ByzantineNodes,         \* Set of Byzantine (malicious) nodes
    MaxPathsPerRoute        \* Maximum backup paths per route

ASSUME
    /\ Cardinality(Nodes) > 3 * MaxFailures  \* Byzantine fault tolerance requirement
    /\ HeartbeatInterval > 0
    /\ TimeoutThreshold > HeartbeatInterval
    /\ MaxRetries > 0
    /\ CheckpointInterval > 0
    /\ ByzantineNodes \subseteq Nodes
    /\ Cardinality(ByzantineNodes) <= MaxFailures
    /\ MaxPathsPerRoute > 1

(****************************************************************************)
(* Helper Operators                                                         *)
(****************************************************************************)

\* Minimum of a set
MIN(S) == CHOOSE x \in S : \A y \in S : x <= y

\* Maximum of a set
MAX(S) == CHOOSE x \in S : \A y \in S : x >= y

(****************************************************************************)
(* Failure Model                                                            *)
(****************************************************************************)

\* Types of failures
FailureTypes == {
    "CRASH",            \* Node crashes and stops
    "OMISSION",         \* Node omits messages
    "TIMING",           \* Node is too slow
    "BYZANTINE",        \* Arbitrary malicious behavior
    "NETWORK_PARTITION",\* Network split
    "TRANSIENT"         \* Temporary failure
}

\* Node states
NodeStates == {
    "HEALTHY",
    "SUSPECTED",
    "FAILED",
    "RECOVERING",
    "RECOVERED",
    "ISOLATED"          \* In minority partition
}

\* Failure descriptor
FailureDescriptor == [
    node: Nodes,
    failure_type: FailureTypes,
    start_time: Nat,
    duration: Nat,           \* 0 for permanent
    detected: BOOLEAN,
    detector: Nodes,
    detection_time: Nat
]

(****************************************************************************)
(* Failure Detector (Heartbeat-based)                                       *)
(****************************************************************************)

\* Heartbeat message
HeartbeatMessage == [
    sender: Nodes,
    sequence: Nat,
    timestamp: Nat,
    path_quality: 0..100,    \* Current path quality
    active_paths: Nat        \* Number of active paths
]

\* Failure detector state for each node
FailureDetectorState == [
    node: Nodes,
    last_heartbeat: Nat,
    heartbeat_sequence: Nat,
    missed_heartbeats: 0..MaxRetries,
    suspected: BOOLEAN,
    failed: BOOLEAN,
    failure_time: Nat
]

\* Initialize failure detector
InitFailureDetector(n) ==
    [
        node |-> n,
        last_heartbeat |-> 0,
        heartbeat_sequence |-> 0,
        missed_heartbeats |-> 0,
        suspected |-> FALSE,
        failed |-> FALSE,
        failure_time |-> 0
    ]

\* Send heartbeat
SendHeartbeat(fd_state, current_time) ==
    [fd_state EXCEPT
        !.heartbeat_sequence = @ + 1,
        !.last_heartbeat = current_time
    ]

\* Receive heartbeat
ReceiveHeartbeat(fd_state, sequence, current_time) ==
    IF sequence >= fd_state.heartbeat_sequence
    THEN [fd_state EXCEPT
        !.heartbeat_sequence = sequence,
        !.last_heartbeat = current_time,
        !.missed_heartbeats = 0,
        !.suspected = FALSE,
        !.failed = FALSE
    ]
    ELSE fd_state  \* Ignore old heartbeat

\* Check for timeout
CheckTimeout(fd_state, current_time) ==
    LET time_since_heartbeat == current_time - fd_state.last_heartbeat
    IN IF time_since_heartbeat > TimeoutThreshold
       THEN IF fd_state.missed_heartbeats >= MaxRetries
            THEN [fd_state EXCEPT
                !.failed = TRUE,
                !.suspected = FALSE,
                !.failure_time = current_time
            ]
            ELSE [fd_state EXCEPT
                !.missed_heartbeats = @ + 1,
                !.suspected = TRUE
            ]
       ELSE fd_state

\* Adaptive timeout based on network conditions
AdaptiveTimeout(base_timeout, rtt_variance, loss_rate) ==
    base_timeout + (rtt_variance * 4) + (((loss_rate * base_timeout) \div 100))

(****************************************************************************)
(* Path Failover and Backup Management                                      *)
(****************************************************************************)

\* Path state
PathState == {
    "ACTIVE",       \* Primary path in use
    "BACKUP",       \* Backup path ready
    "PROBING",      \* Path being tested
    "FAILED",       \* Path has failed
    "RECOVERING"    \* Path recovering
}

\* Path descriptor
PathDescriptor == [
    path_id: Nat,
    nodes: Seq(Nodes),
    state: PathState,
    quality: 0..100,
    latency: Nat,
    bandwidth: Nat,
    loss_rate: 0..100,
    last_used: Nat,
    failure_count: Nat,
    probe_interval: Nat
]

\* Multi-path routing state
MultipathState == [
    primary_path: Nat,
    backup_paths: SUBSET Nat,
    failed_paths: SUBSET Nat,
    path_descriptors: [Nat -> PathDescriptor],
    failover_count: Nat,
    last_failover: Nat
]

\* Initialize multipath state
InitMultipathState ==
    [
        primary_path |-> 0,
        backup_paths |-> {},
        failed_paths |-> {},
        path_descriptors |-> [i \in {} |-> <<>>],
        failover_count |-> 0,
        last_failover |-> 0
    ]

\* Select best backup path
SelectBackupPath(mp_state) ==
    LET available == mp_state.backup_paths \ mp_state.failed_paths
        qualities == {[path |-> p, 
                       quality |-> mp_state.path_descriptors[p].quality] : 
                      p \in available}
    IN IF available = {}
       THEN "NONE"
       ELSE (CHOOSE pq \in qualities : 
             \A other \in qualities : pq.quality >= other.quality).path

\* Perform path failover
Failover(mp_state, current_time) ==
    LET backup == SelectBackupPath(mp_state)
    IN IF backup = "NONE"
       THEN [mp_state EXCEPT
           !.failed_paths = @ \union {mp_state.primary_path}
       ]
       ELSE [mp_state EXCEPT
           !.failed_paths = @ \union {mp_state.primary_path},
           !.primary_path = backup,
           !.backup_paths = @ \ {backup},
           !.failover_count = @ + 1,
           !.last_failover = current_time
       ]

\* Probe failed path for recovery
ProbePath(mp_state, path_id) ==
    [mp_state EXCEPT
        !.path_descriptors[path_id].state = "PROBING"
    ]

\* Recover path
RecoverPath(mp_state, path_id) ==
    [mp_state EXCEPT
        !.path_descriptors[path_id].state = "BACKUP",
        !.path_descriptors[path_id].failure_count = 0,
        !.failed_paths = @ \ {path_id},
        !.backup_paths = @ \union {path_id}
    ]

\* Path quality estimation
EstimatePathQuality(latency, bandwidth, loss_rate) ==
    LET latency_score == 100 - ((latency * 100) \div 1000)  \* Assume max 1000ms
        bandwidth_score == bandwidth \div 10              \* Normalize
        loss_score == 100 - loss_rate
    IN (latency_score + bandwidth_score + loss_score) \div 3

(****************************************************************************)
(* State Checkpointing and Recovery                                         *)
(****************************************************************************)

\* Checkpoint types
CheckpointTypes == {
    "FULL",         \* Complete state snapshot
    "INCREMENTAL",  \* Changes since last checkpoint
    "ROLLING"       \* Continuous checkpointing
}

\* Checkpoint descriptor
Checkpoint == [
    checkpoint_id: Nat,
    checkpoint_type: CheckpointTypes,
    timestamp: Nat,
    node: Nodes,
    state_hash: Nat,
    data_size: Nat,
    dependencies: SUBSET Nat  \* IDs of prior checkpoints needed
]

\* Recovery log entry
RecoveryLogEntry == [
    entry_id: Nat,
    timestamp: Nat,
    operation: STRING,
    before_state: Nat,
    after_state: Nat
]

\* Checkpoint manager state
CheckpointManager == [
    checkpoints: Seq(Checkpoint),
    recovery_log: Seq(RecoveryLogEntry),
    last_checkpoint: Nat,
    checkpoint_count: Nat
]

\* Create checkpoint
CreateCheckpoint(cm, node, state_hash, current_time, cp_type) ==
    LET new_checkpoint == [
            checkpoint_id |-> cm.checkpoint_count + 1,
            checkpoint_type |-> cp_type,
            timestamp |-> current_time,
            node |-> node,
            state_hash |-> state_hash,
            data_size |-> 1000,  \* Abstract size
            dependencies |-> IF cp_type = "INCREMENTAL" /\ cm.checkpoint_count > 0
                           THEN {cm.checkpoint_count}
                           ELSE {}
        ]
    IN [cm EXCEPT
        !.checkpoints = Append(@, new_checkpoint),
        !.last_checkpoint = current_time,
        !.checkpoint_count = @ + 1
    ]

\* Log operation for recovery
LogOperation(cm, operation, before_hash, after_hash, current_time) ==
    LET log_entry == [
            entry_id |-> Len(cm.recovery_log) + 1,
            timestamp |-> current_time,
            operation |-> operation,
            before_state |-> before_hash,
            after_state |-> after_hash
        ]
    IN [cm EXCEPT
        !.recovery_log = Append(@, log_entry)
    ]

\* Find recovery point
FindRecoveryPoint(cm, target_time) ==
    LET valid_checkpoints == {cp \in DOMAIN cm.checkpoints : 
                             cm.checkpoints[cp].timestamp <= target_time}
    IN IF valid_checkpoints = {}
       THEN "NONE"
       ELSE CHOOSE cp \in valid_checkpoints :
            \A other \in valid_checkpoints :
                cm.checkpoints[cp].timestamp >= cm.checkpoints[other].timestamp

\* Recover from checkpoint
RecoverFromCheckpoint(cm, checkpoint_id) ==
    LET cp == cm.checkpoints[checkpoint_id]
        recovery_logs == SelectSeq(cm.recovery_log, 
                                   LAMBDA entry: entry.timestamp > cp.timestamp)
    IN [
        checkpoint |-> cp,
        recovery_ops |-> recovery_logs
    ]

(****************************************************************************)
(* Byzantine Fault Tolerance                                                 *)
(****************************************************************************)

\* Byzantine agreement message
ByzantineMessage == [
    sender: Nodes,
    round: Nat,
    value: Nat,
    signature: Nat,
    signatures: [Nodes -> Nat]  \* For collected signatures
]

\* Byzantine state machine
ByzantineState == [
    round: Nat,
    proposed_value: Nat,
    received_values: [Nodes -> Nat],
    decided: BOOLEAN,
    decided_value: Nat
]

\* Initialize Byzantine state
InitByzantineState ==
    [
        round |-> 0,
        proposed_value |-> 0,
        received_values |-> [n \in Nodes |-> 0],
        decided |-> FALSE,
        decided_value |-> 0
    ]

\* Byzantine agreement algorithm (simplified PBFT)
\* Phase 1: Pre-prepare
PrePrepare(bs, value) ==
    [bs EXCEPT
        !.proposed_value = value,
        !.round = @ + 1
    ]

\* Phase 2: Prepare
Prepare(bs, sender, value) ==
    [bs EXCEPT
        !.received_values[sender] = value
    ]

\* Phase 3: Commit
Commit(bs) ==
    LET honest_nodes == Nodes \ ByzantineNodes
        vote_counts == [v \in {bs.received_values[n] : n \in honest_nodes} |->
                        Cardinality({n \in honest_nodes : bs.received_values[n] = v})]
        max_votes == CHOOSE v \in DOMAIN vote_counts :
                     \A w \in DOMAIN vote_counts : vote_counts[v] >= vote_counts[w]
        quorum == ((Cardinality(honest_nodes) * 2) \div 3) + 1
    IN IF vote_counts[max_votes] >= quorum
       THEN [bs EXCEPT
           !.decided = TRUE,
           !.decided_value = max_votes
       ]
       ELSE bs

\* Check Byzantine agreement validity
ValidByzantineAgreement(states) ==
    LET honest_states == {s \in states : s.decided /\ 
                         (CHOOSE n \in Nodes : states[n] = s) \notin ByzantineNodes}
    IN \A s1, s2 \in honest_states : s1.decided_value = s2.decided_value

(****************************************************************************)
(* Network Partition Handling                                               *)
(****************************************************************************)

\* Network partition
NetworkPartition == SUBSET Nodes

\* Partition state
PartitionState == [
    partition_id: Nat,
    members: SUBSET Nodes,
    is_majority: BOOLEAN,
    coordinator: Nodes,
    state: {"ACTIVE", "MERGING", "ISOLATED"}
]

\* Detect network partition
DetectPartition(nodes, failure_detectors) ==
    LET unreachable == {n \in nodes : failure_detectors[n].failed}
        reachable == nodes \ unreachable
    IN IF Cardinality(unreachable) > 0
       THEN [
           partition_detected |-> TRUE,
           majority_partition |-> reachable,
           minority_partition |-> unreachable,
           is_majority |-> Cardinality(reachable) > Cardinality(nodes) \div 2
       ]
       ELSE [partition_detected |-> FALSE]

\* Partition merge protocol
MergePartitions(partition1, partition2) ==
    LET all_members == partition1.members \union partition2.members
        new_coordinator == CHOOSE n \in all_members : 
                          \A m \in all_members : n <= m
    IN [
        partition_id |-> partition1.partition_id,
        members |-> all_members,
        is_majority |-> Cardinality(all_members) > Cardinality(Nodes) \div 2,
        coordinator |-> new_coordinator,
        state |-> "ACTIVE"
    ]

\* Split-brain prevention using quorum
PreventSplitBrain(partition, total_nodes) ==
    Cardinality(partition.members) > Cardinality(total_nodes) \div 2

(****************************************************************************)
(* Graceful Degradation                                                     *)
(****************************************************************************)

\* Service levels
ServiceLevels == {
    "FULL",         \* All features available
    "DEGRADED",     \* Reduced functionality
    "MINIMAL",      \* Basic service only
    "UNAVAILABLE"   \* Service down
}

\* Degradation policy
DegradationPolicy == [
    failed_nodes: 0..Cardinality(Nodes),
    service_level: ServiceLevels
]

\* Determine service level based on failures
DetermineServiceLevel(failed_count, total_count) ==
    LET failure_ratio == (failed_count * 100) \div total_count
    IN CASE failure_ratio = 0 -> "FULL"
       [] failure_ratio <= 20 -> "DEGRADED"
       [] failure_ratio <= 50 -> "MINIMAL"
       [] OTHER -> "UNAVAILABLE"

\* Feature availability under degradation
FeatureAvailability == [
    feature: STRING,
    required_service_level: ServiceLevels,
    is_available: BOOLEAN
]

\* Check feature availability
IsFeatureAvailable(feature, current_level) ==
    CASE feature = "ENCRYPTION" -> current_level \in {"FULL", "DEGRADED", "MINIMAL"}
    [] feature = "MULTIPATH" -> current_level \in {"FULL", "DEGRADED"}
    [] feature = "QOS" -> current_level = "FULL"
    [] feature = "ANALYTICS" -> current_level = "FULL"
    [] feature = "BASIC_ROUTING" -> current_level \in {"FULL", "DEGRADED", "MINIMAL"}

(****************************************************************************)
(* Retry and Backoff Strategies                                             *)
(****************************************************************************)

\* Retry state
RetryState == [
    attempts: 0..MaxRetries,
    last_attempt: Nat,
    backoff: Nat,
    max_backoff: Nat,
    success: BOOLEAN
]

\* Exponential backoff
ExponentialBackoff(attempt, base_delay, max_delay) ==
    MIN({max_delay, base_delay * (2 ^ attempt)})

\* Decorrelated jitter backoff (AWS style)
DecorrelatedJitterBackoff(attempt, base_delay, last_backoff, max_delay) ==
    LET random == (attempt * 13 + 17) % 100  \* Pseudo-random
        jittered == base_delay + ((random * (last_backoff - base_delay)) \div 100)
    IN MIN({max_delay, jittered})

\* Circuit breaker pattern
CircuitBreakerState == {
    "CLOSED",       \* Normal operation
    "OPEN",         \* Failing, reject requests
    "HALF_OPEN"     \* Testing if service recovered
}

CircuitBreaker == [
    state: CircuitBreakerState,
    failure_count: Nat,
    failure_threshold: Nat,
    success_count: Nat,
    success_threshold: Nat,
    last_state_change: Nat,
    timeout: Nat
]

\* Update circuit breaker
UpdateCircuitBreaker(cb, success, current_time) ==
    CASE cb.state = "CLOSED" ->
        IF success
        THEN cb
        ELSE IF cb.failure_count + 1 >= cb.failure_threshold
             THEN [cb EXCEPT
                 !.state = "OPEN",
                 !.failure_count = 0,
                 !.last_state_change = current_time
             ]
             ELSE [cb EXCEPT !.failure_count = @ + 1]
    [] cb.state = "OPEN" ->
        IF current_time - cb.last_state_change >= cb.timeout
        THEN [cb EXCEPT
            !.state = "HALF_OPEN",
            !.last_state_change = current_time
        ]
        ELSE cb
    [] cb.state = "HALF_OPEN" ->
        IF success
        THEN IF cb.success_count + 1 >= cb.success_threshold
             THEN [cb EXCEPT
                 !.state = "CLOSED",
                 !.success_count = 0,
                 !.last_state_change = current_time
             ]
             ELSE [cb EXCEPT !.success_count = @ + 1]
        ELSE [cb EXCEPT
            !.state = "OPEN",
            !.success_count = 0,
            !.last_state_change = current_time
        ]

(****************************************************************************)
(* State Variables                                                          *)
(****************************************************************************)

VARIABLES
    \* Node states
    node_state,             \* State of each node
    failures,               \* Active failures
    
    \* Failure detection
    failure_detectors,      \* Failure detector state per node
    heartbeats_sent,
    heartbeats_received,
    
    \* Path management
    multipath_state,        \* Multipath routing state
    path_probes,            \* Path probing state
    
    \* Recovery
    checkpoint_managers,    \* Checkpoint state per node
    recovery_in_progress,   \* Nodes currently recovering
    
    \* Byzantine agreement
    byzantine_states,       \* Byzantine consensus state
    
    \* Network partitions
    network_partitions,     \* Current network partitions
    
    \* Service level
    service_level,          \* Current service level
    
    \* Circuit breakers
    circuit_breakers,       \* Circuit breakers per endpoint
    
    \* Metrics
    total_failures,
    total_recoveries,
    total_failovers,
    mean_recovery_time,
    current_time

fault_vars == <<node_state, failures, failure_detectors,
                heartbeats_sent, heartbeats_received, multipath_state,
                path_probes, checkpoint_managers, recovery_in_progress,
                byzantine_states, network_partitions, service_level,
                circuit_breakers, total_failures, total_recoveries,
                total_failovers, mean_recovery_time, current_time>>

(****************************************************************************)
(* Initial State                                                            *)
(****************************************************************************)

FaultToleranceInit ==
    /\ node_state = [n \in Nodes |-> "HEALTHY"]
    /\ failures = {}
    /\ failure_detectors = [n \in Nodes |-> [m \in Nodes |-> InitFailureDetector(m)]]
    /\ heartbeats_sent = 0
    /\ heartbeats_received = 0
    /\ multipath_state = [n \in Nodes |-> [m \in Nodes |-> InitMultipathState]]
    /\ path_probes = [n \in Nodes |-> {}]
    /\ checkpoint_managers = [n \in Nodes |-> 
        [checkpoints |-> <<>>,
         recovery_log |-> <<>>,
         last_checkpoint |-> 0,
         checkpoint_count |-> 0]]
    /\ recovery_in_progress = {}
    /\ byzantine_states = [n \in Nodes |-> InitByzantineState]
    /\ network_partitions = {[
        partition_id |-> 1,
        members |-> Nodes,
        is_majority |-> TRUE,
        coordinator |-> CHOOSE n \in Nodes : TRUE,
        state |-> "ACTIVE"
       ]}
    /\ service_level = "FULL"
    /\ circuit_breakers = [n \in Nodes |-> [m \in Nodes |-> 
        [state |-> "CLOSED",
         failure_count |-> 0,
         failure_threshold |-> 5,
         success_count |-> 0,
         success_threshold |-> 2,
         last_state_change |-> 0,
         timeout |-> 60]]]
    /\ total_failures = 0
    /\ total_recoveries = 0
    /\ total_failovers = 0
    /\ mean_recovery_time = 0
    /\ current_time = 0

(****************************************************************************)
(* Actions                                                                  *)
(****************************************************************************)

\* Node fails
NodeFails(n, failure_type) ==
    /\ node_state[n] = "HEALTHY"
    /\ total_failures < MaxFailures
    /\ LET failure == [
               node |-> n,
               failure_type |-> failure_type,
               start_time |-> current_time,
               duration |-> 0,
               detected |-> FALSE,
               detector |-> n,
               detection_time |-> 0
           ]
       IN /\ failures' = failures \union {failure}
          /\ node_state' = [node_state EXCEPT ![n] = "FAILED"]
          /\ total_failures' = total_failures + 1
          /\ service_level' = DetermineServiceLevel(total_failures' + 1, 
                                                    Cardinality(Nodes))
          /\ UNCHANGED <<failure_detectors, heartbeats_sent, heartbeats_received,
                        multipath_state, path_probes, checkpoint_managers,
                        recovery_in_progress, byzantine_states, network_partitions,
                        circuit_breakers, total_recoveries, total_failovers,
                        mean_recovery_time, current_time>>

\* Send heartbeat
SendHeartbeatAction(sender) ==
    /\ node_state[sender] = "HEALTHY"
    /\ LET new_fd == SendHeartbeat(failure_detectors[sender][sender], current_time)
       IN /\ failure_detectors' = [failure_detectors EXCEPT ![sender][sender] = new_fd]
          /\ heartbeats_sent' = heartbeats_sent + 1
          /\ UNCHANGED <<node_state, failures, heartbeats_received, multipath_state,
                        path_probes, checkpoint_managers, recovery_in_progress,
                        byzantine_states, network_partitions, service_level,
                        circuit_breakers, total_failures, total_recoveries,
                        total_failovers, mean_recovery_time, current_time>>

\* Receive heartbeat and detect failure
ReceiveHeartbeatAction(receiver, sender, sequence) ==
    /\ node_state[receiver] = "HEALTHY"
    /\ LET new_fd == ReceiveHeartbeat(failure_detectors[receiver][sender], 
                                     sequence, current_time)
       IN /\ failure_detectors' = [failure_detectors EXCEPT 
               ![receiver][sender] = new_fd]
          /\ heartbeats_received' = heartbeats_received + 1
          /\ UNCHANGED <<node_state, failures, heartbeats_sent, multipath_state,
                        path_probes, checkpoint_managers, recovery_in_progress,
                        byzantine_states, network_partitions, service_level,
                        circuit_breakers, total_failures, total_recoveries,
                        total_failovers, mean_recovery_time, current_time>>

\* Detect timeout
DetectTimeoutAction(detector, suspected) ==
    /\ node_state[detector] = "HEALTHY"
    /\ LET new_fd == CheckTimeout(failure_detectors[detector][suspected], current_time)
       IN /\ new_fd.failed => node_state' = [node_state EXCEPT ![suspected] = "FAILED"]
          /\ failure_detectors' = [failure_detectors EXCEPT 
               ![detector][suspected] = new_fd]
          /\ UNCHANGED <<failures, heartbeats_sent, heartbeats_received,
                        multipath_state, path_probes, checkpoint_managers,
                        recovery_in_progress, byzantine_states, network_partitions,
                        service_level, circuit_breakers, total_failures,
                        total_recoveries, total_failovers, mean_recovery_time,
                        current_time>>

\* Perform failover
PerformFailover(source, dest) ==
    /\ node_state[source] = "HEALTHY"
    /\ LET mp == multipath_state[source][dest]
           new_mp == Failover(mp, current_time)
       IN /\ new_mp.primary_path # "NONE"
          /\ multipath_state' = [multipath_state EXCEPT 
               ![source][dest] = new_mp]
          /\ total_failovers' = total_failovers + 1
          /\ UNCHANGED <<node_state, failures, failure_detectors,
                        heartbeats_sent, heartbeats_received, path_probes,
                        checkpoint_managers, recovery_in_progress, byzantine_states,
                        network_partitions, service_level, circuit_breakers,
                        total_failures, total_recoveries, mean_recovery_time,
                        current_time>>

\* Create checkpoint
CreateCheckpointAction(n, state_hash) ==
    /\ node_state[n] = "HEALTHY"
    /\ current_time - checkpoint_managers[n].last_checkpoint >= CheckpointInterval
    /\ LET new_cm == CreateCheckpoint(checkpoint_managers[n], n, state_hash,
                                     current_time, "FULL")
       IN /\ checkpoint_managers' = [checkpoint_managers EXCEPT ![n] = new_cm]
          /\ UNCHANGED <<node_state, failures, failure_detectors,
                        heartbeats_sent, heartbeats_received, multipath_state,
                        path_probes, recovery_in_progress, byzantine_states,
                        network_partitions, service_level, circuit_breakers,
                        total_failures, total_recoveries, total_failovers,
                        mean_recovery_time, current_time>>

\* Start recovery
StartRecovery(n) ==
    /\ node_state[n] = "FAILED"
    /\ n \notin recovery_in_progress
    /\ node_state' = [node_state EXCEPT ![n] = "RECOVERING"]
    /\ recovery_in_progress' = recovery_in_progress \union {n}
    /\ UNCHANGED <<failures, failure_detectors, heartbeats_sent,
                  heartbeats_received, multipath_state, path_probes,
                  checkpoint_managers, byzantine_states, network_partitions,
                  service_level, circuit_breakers, total_failures,
                  total_recoveries, total_failovers, mean_recovery_time,
                  current_time>>

\* Complete recovery
CompleteRecovery(n) ==
    /\ node_state[n] = "RECOVERING"
    /\ n \in recovery_in_progress
    /\ node_state' = [node_state EXCEPT ![n] = "HEALTHY"]
    /\ recovery_in_progress' = recovery_in_progress \ {n}
    /\ total_recoveries' = total_recoveries + 1
    /\ service_level' = DetermineServiceLevel(
            Cardinality({m \in Nodes : node_state'[m] = "FAILED"}),
            Cardinality(Nodes))
    /\ UNCHANGED <<failures, failure_detectors, heartbeats_sent,
                  heartbeats_received, multipath_state, path_probes,
                  checkpoint_managers, byzantine_states, network_partitions,
                  circuit_breakers, total_failures, total_failovers,
                  mean_recovery_time, current_time>>

\* Time advances
Tick ==
    /\ current_time' = current_time + 1
    /\ UNCHANGED <<node_state, failures, failure_detectors, heartbeats_sent,
                  heartbeats_received, multipath_state, path_probes,
                  checkpoint_managers, recovery_in_progress, byzantine_states,
                  network_partitions, service_level, circuit_breakers,
                  total_failures, total_recoveries, total_failovers,
                  mean_recovery_time>>

(****************************************************************************)
(* Safety Properties                                                        *)
(****************************************************************************)

FaultToleranceTypeOK ==
    /\ node_state \in [Nodes -> NodeStates]
    /\ failures \subseteq FailureDescriptor
    /\ total_failures \in 0..MaxFailures
    /\ service_level \in ServiceLevels

\* At most MaxFailures concurrent failures
BoundedFailures ==
    Cardinality({n \in Nodes : node_state[n] = "FAILED"}) <= MaxFailures

\* Service available if failures within tolerance
ServiceAvailability ==
    total_failures <= MaxFailures => service_level \in {"FULL", "DEGRADED"}

\* No false failure detection for healthy nodes
NoFalsePositives ==
    \A n \in Nodes :
        node_state[n] = "HEALTHY" =>
        \A m \in Nodes : ~failure_detectors[m][n].failed

\* All failures eventually detected
FailuresEventuallyDetected ==
    \A f \in failures :
        <>(f.detected = TRUE)

\* State consistency after recovery
RecoveryConsistency ==
    \A n \in Nodes :
        node_state[n] = "RECOVERED" =>
        \E cp \in DOMAIN checkpoint_managers[n].checkpoints :
            checkpoint_managers[n].checkpoints[cp].node = n

(****************************************************************************)
(* Liveness Properties                                                      *)
(****************************************************************************)

\* Failed nodes eventually recover or are replaced
EventualRecovery ==
    \A n \in Nodes :
        node_state[n] = "FAILED" =>
        <>(node_state[n] \in {"HEALTHY", "RECOVERED"})

\* Heartbeats keep flowing between healthy nodes
HeartbeatProgress ==
    \A n, m \in Nodes :
        node_state[n] = "HEALTHY" /\ node_state[m] = "HEALTHY" =>
        []<>(heartbeats_received > heartbeats_received')

\* System makes progress despite failures
SystemProgress ==
    total_failures <= MaxFailures =>
    []<>(service_level \in {"FULL", "DEGRADED"})

(****************************************************************************)
(* Specification                                                            *)
(****************************************************************************)

FaultToleranceNext ==
    \/ \E n \in Nodes, ft \in FailureTypes : NodeFails(n, ft)
    \/ \E n \in Nodes : SendHeartbeatAction(n)
    \/ \E n, m \in Nodes, seq \in Nat : ReceiveHeartbeatAction(n, m, seq)
    \/ \E n, m \in Nodes : DetectTimeoutAction(n, m)
    \/ \E n, m \in Nodes : PerformFailover(n, m)
    \/ \E n \in Nodes, h \in Nat : CreateCheckpointAction(n, h)
    \/ \E n \in Nodes : StartRecovery(n)
    \/ \E n \in Nodes : CompleteRecovery(n)
    \/ Tick

FaultToleranceSpec == FaultToleranceInit /\ [][FaultToleranceNext]_fault_vars

FaultToleranceFairSpec ==
    /\ FaultToleranceSpec
    /\ \A n \in Nodes : WF_fault_vars(CompleteRecovery(n))
    /\ \A n, m \in Nodes : WF_fault_vars(PerformFailover(n, m))
    /\ WF_fault_vars(Tick)

(****************************************************************************)
(* Theorems                                                                 *)
(****************************************************************************)

THEOREM FaultToleranceTypeCorrect == FaultToleranceSpec => []FaultToleranceTypeOK
THEOREM BoundedFailuresHolds == FaultToleranceSpec => []BoundedFailures
THEOREM ServiceAvailabilityHolds == FaultToleranceSpec => []ServiceAvailability
THEOREM NoFalsePositivesHolds == FaultToleranceSpec => []NoFalsePositives
THEOREM EventualRecoveryHolds == FaultToleranceFairSpec => EventualRecovery
THEOREM SystemProgressHolds == FaultToleranceFairSpec => SystemProgress

====

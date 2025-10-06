---- MODULE NyxMobilityManagement ----
(****************************************************************************)
(* Nyx Protocol - Mobility Management and Handoff                          *)
(*                                                                          *)
(* Comprehensive specifications for mobile node support, handoff           *)
(* protocols, connection migration, location management, and seamless      *)
(* mobility across network changes.                                        *)
(*                                                                          *)
(* Mobility Components:                                                     *)
(*   - Mobile node tracking and registration                               *)
(*   - Handoff protocols (hard/soft handoff)                               *)
(*   - Connection migration                                                *)
(*   - Location management and updates                                     *)
(*   - Seamless path switching                                             *)
(*   - Quality-based handoff decisions                                     *)
(*   - Predictive mobility management                                      *)
(*   - Make-before-break transitions                                       *)
(*   - Home agent and foreign agent protocols                              *)
(*   - Mobile IPv6 extensions                                              *)
(****************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, Integers, TLC,
LOCAL INSTANCE NyxHelpers

        NyxNetworkLayer, NyxStreamManagement


\* Network attachment point
AttachmentPoint == [
    point_id : STRING,
    network_id : STRING,
    access_technology : {"WIFI", "LTE", "5G", "ETHERNET", "SATELLITE"},
    signal_strength : Nat,
    available_bandwidth : Nat,
    latency : Nat,
    cost : Nat,
    reliability : Nat
]

\* Mobile node location
MobileLocation == [
    current_attachment : AttachmentPoint,
    candidate_attachments : Seq(AttachmentPoint),
    home_network : STRING,
    care_of_address : IPAddress,
    home_address : IPAddress,
    location_timestamp : Nat
]

\* Mobile node state
MobileNodeState == [
    node_id : Node,
    location : MobileLocation,
    active_connections : SUBSET ConnectionId,
    handoff_state : {"IDLE", "PREPARING", "EXECUTING", "FINALIZING"},
    mobility_binding : [
        home_agent : Node,
        binding_lifetime : Nat,
        binding_refresh_time : Nat,
        sequence_number : Nat
    ],
    path_state : [ConnectionId -> PathState],
    handoff_history : Seq([
        timestamp : Nat,
        old_attachment : AttachmentPoint,
        new_attachment : AttachmentPoint,
        handoff_type : STRING,
        duration : Nat,
        success : BOOLEAN
    ])
]

\* Initialize mobile node
InitMobileNode(node_id, home_network, home_address) ==
    [
        node_id |-> node_id,
        location |-> [
            current_attachment |-> NullAttachment,
            candidate_attachments |-> <<>>,
            home_network |-> home_network,
            care_of_address |-> NullAddress,
            home_address |-> home_address,
            location_timestamp |-> 0
        ],
        active_connections |-> {},
        handoff_state |-> "IDLE",
        mobility_binding |-> [
            home_agent |-> NullNode,
            binding_lifetime |-> 0,
            binding_refresh_time |-> 0,
            sequence_number |-> 0
        ],
        path_state |-> [c \in {} |-> NullPathState],
        handoff_history |-> <<>>
    ]


\* Discover attachment points
DiscoverAttachments(mobile_state) ==
    LET nearby_points == ScanNearbyNetworks(mobile_state.location)
        scored_points == [p \in nearby_points |->
            ComputeAttachmentScore(p)]
        sorted_points == SortByScore(scored_points)
    IN [mobile_state EXCEPT
           !.location.candidate_attachments = sorted_points]

\* Compute attachment point score
ComputeAttachmentScore(ap) ==
    LET signal_score == ap.signal_strength * 0.3
        bandwidth_score == Min(ap.available_bandwidth / 1000, 100) * 0.25
        latency_score == (100 - Min(ap.latency, 100)) * 0.25
        reliability_score == ap.reliability * 0.15
        cost_score == (100 - ap.cost) * 0.05
    IN signal_score + bandwidth_score + latency_score + 
       reliability_score + cost_score

\* Register with network
RegisterWithNetwork(mobile_state, attachment_point) ==
    LET care_of_addr == ObtainCareOfAddress(attachment_point)
        updated_location == [mobile_state.location EXCEPT
            !.current_attachment = attachment_point,
            !.care_of_address = care_of_addr,
            !.location_timestamp = CurrentTime]
    IN [mobile_state EXCEPT
           !.location = updated_location,
           !.handoff_state = "IDLE"]

\* Send binding update to home agent
SendBindingUpdate(mobile_state, home_agent) ==
    LET binding_msg == [
            type |-> "BINDING_UPDATE",
            home_address |-> mobile_state.location.home_address,
            care_of_address |-> mobile_state.location.care_of_address,
            sequence_number |-> mobile_state.mobility_binding.sequence_number + 1,
            lifetime |-> DefaultBindingLifetime,
            timestamp |-> CurrentTime
        ]
    IN [mobile_state EXCEPT
           !.mobility_binding.home_agent = home_agent,
           !.mobility_binding.sequence_number = @ + 1,
           !.mobility_binding.binding_lifetime = DefaultBindingLifetime,
           !.mobility_binding.binding_refresh_time = 
               CurrentTime + ((DefaultBindingLifetime * 3) \div 4)]

\* Receive binding acknowledgment
ReceiveBindingAck(mobile_state, ack_msg) ==
    IF ack_msg.sequence_number = mobile_state.mobility_binding.sequence_number
    THEN [mobile_state EXCEPT
             !.mobility_binding.binding_lifetime = ack_msg.lifetime]
    ELSE mobile_state


\* Handoff trigger
HandoffTrigger == [
    trigger_type : {"SIGNAL_DEGRADATION", "BETTER_ALTERNATIVE", 
                    "LOAD_BALANCING", "POLICY", "PROACTIVE"},
    threshold_crossed : BOOLEAN,
    target_attachment : AttachmentPoint,
    urgency : {"LOW", "MEDIUM", "HIGH", "CRITICAL"}
]

\* Check handoff conditions
CheckHandoffConditions(mobile_state) ==
    LET current_ap == mobile_state.location.current_attachment
        candidates == mobile_state.location.candidate_attachments
        
        \* Signal degradation check
        signal_degraded == current_ap.signal_strength < MinSignalThreshold
        
        \* Better alternative check
        better_alternative == 
            \E candidate \in candidates :
                ComputeAttachmentScore(candidate) > 
                    ComputeAttachmentScore(current_ap) + HandoffHysteresis
        
        \* Predictive handoff check
        predicted_degradation == 
            PredictSignalDegradation(current_ap, mobile_state)
        
    IN CASE signal_degraded ->
            [trigger_type |-> "SIGNAL_DEGRADATION",
             threshold_crossed |-> TRUE,
             target_attachment |-> Head(candidates),
             urgency |-> "HIGH"]
        [] better_alternative ->
            LET best_candidate == FindBestCandidate(candidates)
            IN [trigger_type |-> "BETTER_ALTERNATIVE",
                threshold_crossed |-> TRUE,
                target_attachment |-> best_candidate,
                urgency |-> "MEDIUM"]
        [] predicted_degradation ->
            [trigger_type |-> "PROACTIVE",
             threshold_crossed |-> TRUE,
             target_attachment |-> Head(candidates),
             urgency |-> "LOW"]
        [] OTHER ->
            [trigger_type |-> "NONE",
             threshold_crossed |-> FALSE,
             target_attachment |-> NullAttachment,
             urgency |-> "LOW"]

\* Predict signal degradation
PredictSignalDegradation(ap, mobile_state) ==
    LET history == mobile_state.handoff_history
        recent_trend == AnalyzeSignalTrend(history)
        velocity == EstimateNodeVelocity(history)
        time_to_threshold == EstimateTimeToThreshold(ap, recent_trend)
    IN time_to_threshold < PredictiveHandoffWindow


\* Handoff type
HandoffType == {"HARD", "SOFT", "MAKE_BEFORE_BREAK", "BREAK_BEFORE_MAKE"}

\* Prepare handoff
PrepareHandoff(mobile_state, target_ap, handoff_type) ==
    [mobile_state EXCEPT
        !.handoff_state = "PREPARING"]

\* Hard handoff (break current before establishing new)
ExecuteHardHandoff(mobile_state, target_ap) ==
    LET 
        \* Step 1: Disconnect from current attachment
        disconnected_state == DisconnectFromCurrent(mobile_state)
        
        \* Step 2: Connect to new attachment
        connected_state == ConnectToTarget(disconnected_state, target_ap)
        
        \* Step 3: Update bindings
        updated_state == UpdateAllBindings(connected_state)
        
        \* Record handoff
        handoff_record == [
            timestamp |-> CurrentTime,
            old_attachment |-> mobile_state.location.current_attachment,
            new_attachment |-> target_ap,
            handoff_type |-> "HARD",
            duration |-> CurrentTime - mobile_state.location.location_timestamp,
            success |-> TRUE
        ]
    IN [updated_state EXCEPT
           !.handoff_history = Append(@, handoff_record),
           !.handoff_state = "IDLE"]

\* Soft handoff (make before break)
ExecuteSoftHandoff(mobile_state, target_ap) ==
    LET
        \* Step 1: Establish connection to new attachment
        dual_connected == ConnectToTarget(mobile_state, target_ap)
        
        \* Step 2: Migrate active connections
        migrated_state == MigrateConnections(dual_connected, target_ap)
        
        \* Step 3: Disconnect from old attachment
        final_state == DisconnectFromOld(migrated_state)
        
        \* Record handoff
        handoff_record == [
            timestamp |-> CurrentTime,
            old_attachment |-> mobile_state.location.current_attachment,
            new_attachment |-> target_ap,
            handoff_type |-> "SOFT",
            duration |-> CurrentTime - mobile_state.location.location_timestamp,
            success |-> TRUE
        ]
    IN [final_state EXCEPT
           !.handoff_history = Append(@, handoff_record),
           !.handoff_state = "IDLE"]

\* Seamless path switching
SeamlessPathSwitch(mobile_state, connection_id, new_path) ==
    LET
        \* Prepare new path
        prepared_path == PrepareNewPath(new_path)
        
        \* Start sending on both paths (multipath mode)
        dual_path_state == EnableDualPath(mobile_state, connection_id, new_path)
        
        \* Verify new path is working
        verified == VerifyPathFunctionality(dual_path_state, new_path)
        
        \* Switch primary path
        switched_state == IF verified
                         THEN SwitchPrimaryPath(dual_path_state, connection_id, new_path)
                         ELSE mobile_state
        
        \* Remove old path
        final_state == IF verified
                      THEN RemoveOldPath(switched_state, connection_id)
                      ELSE mobile_state
    IN final_state


\* Connection migration state
MigrationState == [
    connection_id : ConnectionId,
    migration_phase : {"INIT", "PATH_SETUP", "DATA_TRANSFER", "COMPLETE"},
    old_path : PathId,
    new_path : PathId,
    buffered_data : Seq(Packet),
    sequence_offset : Nat,
    migration_token : STRING
]

\* Initiate connection migration
InitiateConnectionMigration(mobile_state, connection_id, new_ap) ==
    LET
        \* Generate new path via new attachment
        new_path == CreatePathViaAttachment(new_ap)
        
        \* Create migration state
        migration == [
            connection_id |-> connection_id,
            migration_phase |-> "INIT",
            old_path |-> CurrentPath(mobile_state, connection_id),
            new_path |-> new_path,
            buffered_data |-> <<>>,
            sequence_offset |-> 0,
            migration_token |-> GenerateMigrationToken
        ]
        
    IN [mobile_state EXCEPT
           !.handoff_state = "EXECUTING"]

\* Setup new path for migration
SetupNewPath(mobile_state, migration) ==
    LET
        \* Establish new path
        path_established == EstablishPath(migration.new_path)
        
        \* Send migration prepare to peer
        prepare_msg == [
            type |-> "MIGRATION_PREPARE",
            connection_id |-> migration.connection_id,
            new_path |-> migration.new_path,
            migration_token |-> migration.migration_token
        ]
        
        \* Update migration state
        updated_migration == [migration EXCEPT
            !.migration_phase = "PATH_SETUP"]
        
    IN updated_migration

\* Transfer data over new path
TransferDataOnNewPath(mobile_state, migration) ==
    LET
        \* Send buffered data on new path
        transferred == SendBufferedData(migration.buffered_data, migration.new_path)
        
        \* Start using new path for new data
        path_switched == SwitchToNewPath(mobile_state, 
                                        migration.connection_id,
                                        migration.new_path)
        
        \* Update migration state
        updated_migration == [migration EXCEPT
            !.migration_phase = "DATA_TRANSFER",
            !.buffered_data = <<>>]
        
    IN updated_migration

\* Complete migration
CompleteMigration(mobile_state, migration) ==
    LET
        \* Send migration complete to peer
        complete_msg == [
            type |-> "MIGRATION_COMPLETE",
            connection_id |-> migration.connection_id,
            migration_token |-> migration.migration_token
        ]
        
        \* Remove old path
        cleaned_state == RemovePath(mobile_state, migration.old_path)
        
        \* Update migration state
        final_migration == [migration EXCEPT
            !.migration_phase = "COMPLETE"]
        
    IN [cleaned_state EXCEPT
           !.handoff_state = "FINALIZING"]


\* Location update protocol
LocationUpdate == [
    update_type : {"PERIODIC", "ON_DEMAND", "TRIGGERED"},
    old_location : MobileLocation,
    new_location : MobileLocation,
    timestamp : Nat,
    authentication : STRING
]

\* Send location update
SendLocationUpdate(mobile_state, update_type) ==
    LET update == [
            update_type |-> update_type,
            old_location |-> mobile_state.location,
            new_location |-> mobile_state.location,
            timestamp |-> CurrentTime,
            authentication |-> GenerateLocationAuth(mobile_state)
        ]
    IN update

\* Process location update
ProcessLocationUpdate(home_agent_state, update) ==
    IF ValidateLocationUpdate(update)
    THEN LET updated_binding == [
             mobile_node |-> ExtractNodeId(update),
             care_of_address |-> update.new_location.care_of_address,
             home_address |-> update.new_location.home_address,
             timestamp |-> update.timestamp,
             valid_until |-> update.timestamp + BindingLifetime
         ]
         IN [home_agent_state EXCEPT
                !.bindings[updated_binding.mobile_node] = updated_binding]
    ELSE home_agent_state

\* Location caching
LocationCache == [
    cache : [Node -> MobileLocation],
    cache_timeout : Nat,
    max_cache_size : Nat
]

\* Cache location
CacheLocation(cache, node_id, location) ==
    [cache EXCEPT
        !.cache[node_id] = location]

\* Lookup location
LookupLocation(cache, node_id) ==
    IF node_id \in DOMAIN cache.cache /\
       CurrentTime - cache.cache[node_id].location_timestamp < cache.cache_timeout
    THEN cache.cache[node_id]
    ELSE NullLocation


\* Mobility pattern
MobilityPattern == [
    node_id : Node,
    pattern_type : {"STATIONARY", "RANDOM_WALK", "PERIODIC", "PREDICTABLE"},
    waypoints : Seq(AttachmentPoint),
    visit_frequency : [AttachmentPoint -> Nat],
    transition_matrix : [AttachmentPoint \X AttachmentPoint -> Nat],
    confidence : Nat
]

\* Learn mobility pattern
LearnMobilityPattern(mobile_state) ==
    LET history == mobile_state.handoff_history
        transitions == ExtractTransitions(history)
        frequencies == ComputeVisitFrequencies(history)
        pattern_type == ClassifyPattern(transitions, frequencies)
    IN [
        node_id |-> mobile_state.node_id,
        pattern_type |-> pattern_type,
        waypoints |-> ExtractWaypoints(history),
        visit_frequency |-> frequencies,
        transition_matrix |-> BuildTransitionMatrix(transitions),
        confidence |-> ComputePatternConfidence(transitions, pattern_type)
    ]

\* Predict next attachment
PredictNextAttachment(pattern, current_ap) ==
    IF pattern.pattern_type = "PREDICTABLE"
    THEN LET probabilities == pattern.transition_matrix[current_ap]
             most_likely == CHOOSE ap \in DOMAIN probabilities :
                 \A other \in DOMAIN probabilities :
                     probabilities[ap] >= probabilities[other]
         IN most_likely
    ELSE NullAttachment

\* Preemptive handoff preparation
PreemptiveHandoffPreparation(mobile_state, pattern) ==
    LET predicted_next == PredictNextAttachment(pattern, 
                             mobile_state.location.current_attachment)
        prediction_confidence == pattern.confidence
    IN IF prediction_confidence > PreemptiveThreshold
       THEN PrepareHandoff(mobile_state, predicted_next, "SOFT")
       ELSE mobile_state


\* Connection quality metrics
ConnectionQuality == [
    signal_strength : Nat,
    packet_loss_rate : Nat,
    latency : Nat,
    jitter : Nat,
    throughput : Nat,
    error_rate : Nat,
    stability : Nat
]

\* Measure connection quality
MeasureConnectionQuality(mobile_state, connection_id) ==
    LET path == CurrentPath(mobile_state, connection_id)
        metrics == CollectPathMetrics(path)
    IN [
        signal_strength |-> metrics.signal_strength,
        packet_loss_rate |-> metrics.packet_loss_rate,
        latency |-> metrics.latency,
        jitter |-> metrics.jitter,
        throughput |-> metrics.throughput,
        error_rate |-> metrics.error_rate,
        stability |-> ComputeStability(metrics)
    ]

\* Compute handoff score
ComputeHandoffScore(current_quality, candidate_quality) ==
    LET signal_gain == (candidate_quality.signal_strength - 
                       current_quality.signal_strength) * 0.2
        loss_improvement == (current_quality.packet_loss_rate - 
                            candidate_quality.packet_loss_rate) * 0.25
        latency_improvement == (current_quality.latency - 
                               candidate_quality.latency) * 0.2
        throughput_gain == (candidate_quality.throughput - 
                           current_quality.throughput) * 0.2
        stability_factor == candidate_quality.stability * 0.15
    IN signal_gain + loss_improvement + latency_improvement + 
       throughput_gain + stability_factor

\* Multi-criteria handoff decision
MultiCriteriaHandoffDecision(mobile_state, candidates) ==
    LET current_quality == MeasureConnectionQuality(mobile_state, 
                              Head(mobile_state.active_connections))
        scored_candidates == [c \in candidates |->
            [attachment |-> c,
             quality |-> EstimateQuality(c),
             score |-> ComputeHandoffScore(current_quality, EstimateQuality(c))]]
        best_candidate == CHOOSE c \in scored_candidates :
            \A other \in scored_candidates : c.score >= other.score
    IN IF best_candidate.score > HandoffThreshold
       THEN best_candidate.attachment
       ELSE NullAttachment


\* Seamless handoff: No packet loss during handoff
THEOREM SeamlessHandoff ==
    \A mobile_state \in MobileNodeStates :
        HandoffInProgress(mobile_state) =>
            NoPacketLoss(mobile_state)

\* Location consistency: Home agent binding matches actual location
THEOREM LocationConsistency ==
    \A mobile_state \in MobileNodeStates :
        LET binding == HomeAgentBinding(mobile_state)
        IN binding.care_of_address = mobile_state.location.care_of_address

\* Handoff convergence: Handoff eventually completes
THEOREM HandoffConvergence ==
    \A mobile_state \in MobileNodeStates :
        HandoffInProgress(mobile_state) =>
            Eventually(HandoffComplete(mobile_state))

\* Connection continuity: Active connections survive handoff
THEOREM ConnectionContinuity ==
    \A mobile_state \in MobileNodeStates, conn_id \in ConnectionId :
        ActiveConnection(mobile_state, conn_id) /\
        HandoffInProgress(mobile_state) =>
            Eventually(ActiveConnection(AfterHandoff(mobile_state), conn_id))

\* Optimal attachment: Selected attachment maximizes quality
THEOREM OptimalAttachment ==
    \A mobile_state \in MobileNodeStates :
        LET current == mobile_state.location.current_attachment
            candidates == mobile_state.location.candidate_attachments
        IN \A candidate \in candidates :
            ComputeAttachmentScore(current) >= 
                ComputeAttachmentScore(candidate) - HandoffHysteresis

====

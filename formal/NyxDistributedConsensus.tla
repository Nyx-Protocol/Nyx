---- MODULE NyxDis(*   - Distributed snapshots                                               *)
(****************************************************************************)  

EXTENDS Naturals, Sequences, FiniteSets, Integers, TLC
LOCAL INSTANCE NyxHelpers

\* Paxos rolesnsensus ----
(****************************************************************************)
(* Nyx Protocol - Distributed Consensus and Coordination                   *)
(*                                                                          *)
(* Comprehensive formal specifications for distributed consensus            *)
(* algorithms, leader election, state machine replication, and             *)
(* distributed coordination primitives.                                    *)
(*                                                                          *)
(* Consensus Components:                                                    *)
(*   - Paxos and Multi-Paxos                                               *)
(*   - Raft consensus algorithm                                            *)
(*   - Byzantine Fault Tolerant (BFT) consensus                            *)
(*   - Leader election protocols                                           *)
(*   - Distributed locks and barriers                                      *)
(*   - State machine replication                                           *)
(*   - Quorum systems                                                      *)
(*   - Atomic broadcast and total order                                    *)
(*   - Viewstamped replication                                             *)
(*   - Distributed snapshots                                               *)
(****************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, Integers, TLC,
LOCAL INSTANCE NyxHelpers

        NyxFaultTolerance, NyxNetworkLayer


\* Paxos roles
PaxosRole == {"PROPOSER", "ACCEPTOR", "LEARNER"}

\* Proposal number (ballot)
ProposalNumber == Nat

\* Proposal value
ProposalValue == Any

\* Paxos state
PaxosState == [
    role : PaxosRole,
    node_id : Node,
    current_proposal : ProposalNumber,
    promised_proposal : ProposalNumber,
    accepted_proposal : ProposalNumber,
    accepted_value : ProposalValue,
    learned_value : ProposalValue,
    promises_received : SUBSET Node,
    accepts_received : SUBSET Node
]

\* Phase 1a: Prepare
Prepare(state, proposal_num) ==
    [state EXCEPT
        !.current_proposal = proposal_num]

\* Phase 1b: Promise
Promise(state, proposal_num, acceptor_id) ==
    IF proposal_num > state.promised_proposal
    THEN [state EXCEPT
             !.promised_proposal = proposal_num,
             !.promises_received = @ \union {acceptor_id}]
    ELSE state

\* Phase 2a: Accept request
AcceptRequest(state, proposal_num, value) ==
    IF proposal_num >= state.promised_proposal
    THEN [state EXCEPT
             !.accepted_proposal = proposal_num,
             !.accepted_value = value]
    ELSE state

\* Phase 2b: Accepted
Accepted(state, proposal_num, value, acceptor_id) ==
    IF proposal_num = state.current_proposal
    THEN [state EXCEPT
             !.accepts_received = @ \union {acceptor_id}]
    ELSE state

\* Learn value
Learn(state, value) ==
    [state EXCEPT
        !.learned_value = value]

\* Multi-Paxos state
MultiPaxosState == [
    instances : [Nat -> PaxosState],
    next_instance : Nat,
    leader : Node,
    stable_leader : BOOLEAN
]

\* Multi-Paxos: Propose in next instance
ProposeNext(mp_state, value) ==
    LET instance == mp_state.next_instance
        new_paxos == Prepare(InitPaxosState, instance)
    IN [mp_state EXCEPT
           !.instances[instance] = new_paxos,
           !.next_instance = @ + 1]


\* Raft node state
RaftNodeState == {"FOLLOWER", "CANDIDATE", "LEADER"}

\* Log entry
LogEntry == [
    index : Nat,
    term : Nat,
    command : Any
]

\* Raft state
RaftState == [
    node_id : Node,
    current_term : Nat,
    voted_for : Node,
    log : Seq(LogEntry),
    commit_index : Nat,
    last_applied : Nat,
    state : RaftNodeState,
    
    \* Leader state
    next_index : [Node -> Nat],
    match_index : [Node -> Nat],
    
    \* Election state
    votes_received : SUBSET Node,
    election_timeout : Nat,
    heartbeat_timeout : Nat
]

\* Request vote RPC
RequestVote(raft, candidate_id, term, last_log_index, last_log_term) ==
    IF term > raft.current_term
    THEN LET log_ok == IF Len(raft.log) = 0
                       THEN TRUE
                       ELSE LET last_entry == raft.log[Len(raft.log)]
                            IN last_log_term > last_entry.term \/
                               (last_log_term = last_entry.term /\
                                last_log_index >= Len(raft.log))
             vote_granted == log_ok /\ (raft.voted_for \in {0, candidate_id})
         IN [raft EXCEPT
                !.current_term = term,
                !.voted_for = IF vote_granted THEN candidate_id ELSE @,
                !.state = "FOLLOWER"]
    ELSE raft

\* Append entries RPC
AppendEntries(raft, leader_id, term, prev_log_index, prev_log_term,
              entries, leader_commit) ==
    IF term < raft.current_term
    THEN raft
    ELSE LET log_ok == prev_log_index = 0 \/
                      (prev_log_index <= Len(raft.log) /\
                       raft.log[prev_log_index].term = prev_log_term)
         IN IF log_ok
            THEN LET new_log == SubSeq(raft.log, 1, prev_log_index) \o entries
                     new_commit == Min(leader_commit, Len(new_log))
                 IN [raft EXCEPT
                        !.current_term = term,
                        !.state = "FOLLOWER",
                        !.log = new_log,
                        !.commit_index = Max(@, new_commit)]
            ELSE [raft EXCEPT
                     !.current_term = term,
                     !.state = "FOLLOWER"]

\* Start election
StartElection(raft) ==
    [raft EXCEPT
        !.current_term = @ + 1,
        !.state = "CANDIDATE",
        !.voted_for = raft.node_id,
        !.votes_received = {raft.node_id}]

\* Receive vote
ReceiveVote(raft, voter_id) ==
    [raft EXCEPT
        !.votes_received = @ \union {voter_id}]

\* Become leader
BecomeLeader(raft, all_nodes) ==
    [raft EXCEPT
        !.state = "LEADER",
        !.next_index = [n \in all_nodes |-> Len(raft.log) + 1],
        !.match_index = [n \in all_nodes |-> 0]]

\* Replicate log entry
ReplicateEntry(raft, command) ==
    LET entry == [index |-> Len(raft.log) + 1,
                  term |-> raft.current_term,
                  command |-> command]
    IN [raft EXCEPT
           !.log = Append(@, entry)]

\* Advance commit index
AdvanceCommitIndex(raft, all_nodes) ==
    LET majority == (Cardinality(all_nodes) \div 2) + 1
        n == CHOOSE n \in Nat :
               n > raft.commit_index /\
               n <= Len(raft.log) /\
               raft.log[n].term = raft.current_term /\
               Cardinality({node \in all_nodes : raft.match_index[node] >= n}) >= majority
    IN [raft EXCEPT !.commit_index = n]


\* PBFT phase
PBFTPhase == {"PRE_PREPARE", "PREPARE", "COMMIT", "REPLY"}

\* PBFT message
PBFTMessage == [
    phase : PBFTPhase,
    view : Nat,
    sequence : Nat,
    digest : STRING,
    replica_id : Node
]

\* PBFT replica state
PBFTState == [
    replica_id : Node,
    view : Nat,
    sequence : Nat,
    primary : Node,
    state : {"NORMAL", "VIEW_CHANGE", "NEW_VIEW"},
    
    \* Message logs
    pre_prepare_log : [Nat -> PBFTMessage],
    prepare_log : [Nat -> SUBSET PBFTMessage],
    commit_log : [Nat -> SUBSET PBFTMessage],
    
    \* Checkpoints
    stable_checkpoint : Nat,
    checkpoint_proofs : [Nat -> SUBSET PBFTMessage],
    
    \* View change
    view_change_votes : SUBSET Node
]

\* Send pre-prepare (primary only)
SendPrePrepare(pbft, sequence, request) ==
    LET digest == Hash(request)
        msg == [phase |-> "PRE_PREPARE",
                view |-> pbft.view,
                sequence |-> sequence,
                digest |-> digest,
                replica_id |-> pbft.replica_id]
    IN [pbft EXCEPT
           !.pre_prepare_log[sequence] = msg,
           !.sequence = Max(@, sequence + 1)]

\* Receive pre-prepare and send prepare
ReceivePrePrepare(pbft, pre_prepare_msg, num_replicas) ==
    IF pre_prepare_msg.view = pbft.view /\
       pre_prepare_msg.replica_id = pbft.primary
    THEN LET prepare_msg == [phase |-> "PREPARE",
                             view |-> pbft.view,
                             sequence |-> pre_prepare_msg.sequence,
                             digest |-> pre_prepare_msg.digest,
                             replica_id |-> pbft.replica_id]
         IN [pbft EXCEPT
                !.pre_prepare_log[pre_prepare_msg.sequence] = pre_prepare_msg,
                !.prepare_log[pre_prepare_msg.sequence] = 
                    @ \union {prepare_msg}]
    ELSE pbft

\* Receive prepare messages
ReceivePrepare(pbft, prepare_msg, num_replicas) ==
    LET seq == prepare_msg.sequence
        prepared == Cardinality(pbft.prepare_log[seq]) >= ((2 * num_replicas) \div 3)
    IN IF prepare_msg.view = pbft.view
       THEN LET commit_msg == [phase |-> "COMMIT",
                               view |-> pbft.view,
                               sequence |-> seq,
                               digest |-> prepare_msg.digest,
                               replica_id |-> pbft.replica_id]
            IN [pbft EXCEPT
                   !.prepare_log[seq] = @ \union {prepare_msg},
                   !.commit_log[seq] = IF prepared
                                      THEN @ \union {commit_msg}
                                      ELSE @]
       ELSE pbft

\* Receive commit messages
ReceiveCommit(pbft, commit_msg, num_replicas) ==
    LET seq == commit_msg.sequence
        committed == Cardinality(pbft.commit_log[seq]) >= ((2 * num_replicas) \div 3) + 1
    IN IF commit_msg.view = pbft.view
       THEN [pbft EXCEPT
                !.commit_log[seq] = @ \union {commit_msg}]
       ELSE pbft

\* View change
InitiateViewChange(pbft, new_view) ==
    [pbft EXCEPT
        !.view = new_view,
        !.state = "VIEW_CHANGE",
        !.primary = new_view % NumReplicas]

\* Create checkpoint
CreateCheckpoint(pbft, sequence) ==
    [pbft EXCEPT
        !.stable_checkpoint = sequence]


\* Bully algorithm state
BullyState == [
    node_id : Node,
    leader : Node,
    is_leader : BOOLEAN,
    election_in_progress : BOOLEAN,
    election_initiator : Node,
    responses_received : SUBSET Node,
    priority : Nat
]

\* Bully: Start election
BullyStartElection(state) ==
    [state EXCEPT
        !.election_in_progress = TRUE,
        !.election_initiator = state.node_id]

\* Bully: Receive election message
BullyReceiveElection(state, sender_id, sender_priority) ==
    IF sender_priority < state.priority
    THEN [state EXCEPT
             !.responses_received = @ \union {sender_id}]
    ELSE [state EXCEPT
             !.election_in_progress = FALSE]

\* Bully: Become leader
BullyBecomeLeader(state) ==
    [state EXCEPT
        !.is_leader = TRUE,
        !.leader = state.node_id,
        !.election_in_progress = FALSE]

\* Ring algorithm state
RingElectionState == [
    node_id : Node,
    next_node : Node,
    leader : Node,
    election_message : [
        initiator : Node,
        participants : Seq(Node),
        active : BOOLEAN
    ]
]

\* Ring: Forward election message
RingForwardElection(state, participants) ==
    [state EXCEPT
        !.election_message.participants = participants]

\* Ring: Complete election
RingCompleteElection(state, participants) ==
    LET leader == CHOOSE n \in DOMAIN participants :
                    \A m \in DOMAIN participants : 
                        Priority(participants[n]) >= Priority(participants[m])
    IN [state EXCEPT
           !.leader = leader,
           !.election_message.active = FALSE]


\* Distributed lock
DistributedLock == [
    lock_id : STRING,
    holder : Node,
    locked : BOOLEAN,
    version : Nat,
    expiry : Nat,
    waiters : Seq(Node)
]

\* Lock manager
LockManager == [
    locks : [STRING -> DistributedLock],
    local_locks : SUBSET STRING,
    lease_duration : Nat
]

\* Acquire lock
AcquireDistributedLock(manager, lock_id, node_id) ==
    IF lock_id \notin DOMAIN manager.locks
    THEN LET lock == [
             lock_id |-> lock_id,
             holder |-> node_id,
             locked |-> TRUE,
             version |-> 1,
             expiry |-> CurrentTime + manager.lease_duration,
             waiters |-> <<>>
         ]
         IN [success |-> TRUE,
             manager |-> [manager EXCEPT
                             !.locks[lock_id] = lock,
                             !.local_locks = @ \union {lock_id}]]
    ELSE IF manager.locks[lock_id].locked = FALSE
         THEN [success |-> TRUE,
               manager |-> [manager EXCEPT
                               !.locks[lock_id].locked = TRUE,
                               !.locks[lock_id].holder = node_id,
                               !.locks[lock_id].version = @ + 1,
                               !.locks[lock_id].expiry = CurrentTime + manager.lease_duration,
                               !.local_locks = @ \union {lock_id}]]
         ELSE [success |-> FALSE,
               manager |-> [manager EXCEPT
                               !.locks[lock_id].waiters = Append(@, node_id)]]

\* Release lock
ReleaseDistributedLock(manager, lock_id, node_id) ==
    IF lock_id \in DOMAIN manager.locks /\
       manager.locks[lock_id].holder = node_id
    THEN LET lock == manager.locks[lock_id]
             next_holder == IF lock.waiters # <<>>
                           THEN Head(lock.waiters)
                           ELSE 0
         IN [manager EXCEPT
                !.locks[lock_id].locked = next_holder # 0,
                !.locks[lock_id].holder = next_holder,
                !.locks[lock_id].waiters = IF next_holder # 0 
                                          THEN Tail(@) 
                                          ELSE <<>>,
                !.local_locks = @ \ {lock_id}]
    ELSE manager

\* Extend lock lease
ExtendLease(manager, lock_id, node_id) ==
    IF lock_id \in DOMAIN manager.locks /\
       manager.locks[lock_id].holder = node_id
    THEN [manager EXCEPT
             !.locks[lock_id].expiry = CurrentTime + manager.lease_duration]
    ELSE manager

\* Check lock expiry
CheckLockExpiry(manager, lock_id) ==
    IF lock_id \in DOMAIN manager.locks /\
       CurrentTime > manager.locks[lock_id].expiry
    THEN ReleaseDistributedLock(manager, lock_id, manager.locks[lock_id].holder)
    ELSE manager


\* Distributed barrier
DistributedBarrier == [
    barrier_id : STRING,
    required_participants : Nat,
    arrived_participants : SUBSET Node,
    generation : Nat,
    released : BOOLEAN
]

\* Barrier coordinator
BarrierCoordinator == [
    barriers : [STRING -> DistributedBarrier]
]

\* Arrive at barrier
ArriveAtBarrier(coordinator, barrier_id, node_id) ==
    LET barrier == coordinator.barriers[barrier_id]
        new_arrived == barrier.arrived_participants \union {node_id}
        all_arrived == Cardinality(new_arrived) = barrier.required_participants
    IN [coordinator EXCEPT
           !.barriers[barrier_id].arrived_participants = new_arrived,
           !.barriers[barrier_id].released = all_arrived,
           !.barriers[barrier_id].generation = 
               IF all_arrived THEN @ + 1 ELSE @]

\* Wait at barrier
WaitAtBarrier(coordinator, barrier_id) ==
    coordinator.barriers[barrier_id].released

\* Reset barrier
ResetBarrier(coordinator, barrier_id) ==
    [coordinator EXCEPT
        !.barriers[barrier_id].arrived_participants = {},
        !.barriers[barrier_id].released = FALSE]


\* State machine
StateMachine == [
    state : Any,
    transition : [Any \X Any -> Any],
    output : [Any \X Any -> Any]
]

\* Replicated state machine
ReplicatedStateMachine == [
    machine : StateMachine,
    log : Seq([command : Any, index : Nat]),
    last_applied : Nat,
    snapshot : Any,
    snapshot_index : Nat
]

\* Apply command
ApplyCommand(rsm, command) ==
    LET new_state == rsm.machine.transition[rsm.machine.state, command]
        output == rsm.machine.output[rsm.machine.state, command]
    IN [rsm EXCEPT
           !.machine.state = new_state,
           !.last_applied = @ + 1]

\* Create snapshot
CreateSnapshot(rsm) ==
    [rsm EXCEPT
        !.snapshot = rsm.machine.state,
        !.snapshot_index = rsm.last_applied]

\* Restore from snapshot
RestoreFromSnapshot(rsm, snapshot, snapshot_index) ==
    [rsm EXCEPT
        !.machine.state = snapshot,
        !.last_applied = snapshot_index,
        !.snapshot = snapshot,
        !.snapshot_index = snapshot_index]


\* Quorum system
QuorumSystem == [
    nodes : SUBSET Node,
    quorums : SUBSET (SUBSET Node),
    read_quorum_size : Nat,
    write_quorum_size : Nat
]

\* Simple majority quorum
MajorityQuorum(nodes) ==
    [
        nodes |-> nodes,
        quorums |-> {q \in SUBSET nodes : 
                     Cardinality(q) > Cardinality(nodes) \div 2},
        read_quorum_size |-> (Cardinality(nodes) \div 2) + 1,
        write_quorum_size |-> (Cardinality(nodes) \div 2) + 1
    ]

\* Byzantine quorum
ByzantineQuorum(nodes, f) ==
    [
        nodes |-> nodes,
        quorums |-> {q \in SUBSET nodes : 
                     Cardinality(q) >= (2 * f) + 1},
        read_quorum_size |-> (2 * f) + 1,
        write_quorum_size |-> (2 * f) + 1
    ]

\* Grid quorum
GridQuorum(nodes) ==
    LET size == IntegerSqrt(Cardinality(nodes))
        grid == [i \in 1..size, j \in 1..size |-> 
                CHOOSE n \in nodes : TRUE]
        row_quorums == {grid[i, j] : i \in 1..size, j \in 1..size}
        col_quorums == {grid[i, j] : j \in 1..size, i \in 1..size}
    IN [
        nodes |-> nodes,
        quorums |-> row_quorums \union col_quorums,
        read_quorum_size |-> size,
        write_quorum_size |-> size
    ]

\* Check quorum intersection
QuorumIntersection(qs, q1, q2) ==
    q1 \in qs.quorums /\ q2 \in qs.quorums =>
        q1 \intersect q2 # {}


\* Total order broadcast
TotalOrderBroadcast == [
    sequence : Nat,
    delivered : Seq([message : Any, sender : Node]),
    pending : [Node -> Seq(Any)],
    agreements : [Nat -> SUBSET Node]
]

\* Broadcast message
Broadcast(tob, sender, message) ==
    [tob EXCEPT
        !.pending[sender] = Append(@, message)]

\* Agree on order
AgreeOrder(tob, sequence, nodes) ==
    [tob EXCEPT
        !.agreements[sequence] = @ \union nodes]

\* Deliver in order
DeliverInOrder(tob, sequence, message, sender) ==
    IF sequence = tob.sequence + 1
    THEN [tob EXCEPT
             !.delivered = Append(@, [message |-> message, sender |-> sender]),
             !.sequence = sequence]
    ELSE tob


\* Snapshot state
SnapshotState == [
    snapshot_id : Nat,
    initiator : Node,
    local_state : [Node -> Any],
    channel_state : [Node \X Node -> Seq(Any)],
    markers_sent : [Node -> SUBSET Node],
    markers_received : [Node -> SUBSET Node],
    complete : BOOLEAN
]

\* Initiate snapshot
InitiateSnapshot(snapshot, node_id) ==
    [snapshot EXCEPT
        !.initiator = node_id,
        !.local_state[node_id] = LocalState(node_id),
        !.markers_sent[node_id] = AllNeighbors(node_id)]

\* Receive marker
ReceiveMarker(snapshot, node_id, sender_id) ==
    IF node_id \notin DOMAIN snapshot.local_state
    THEN [snapshot EXCEPT
             !.local_state[node_id] = LocalState(node_id),
             !.markers_received[node_id] = @ \union {sender_id},
             !.markers_sent[node_id] = AllNeighbors(node_id)]
    ELSE [snapshot EXCEPT
             !.markers_received[node_id] = @ \union {sender_id},
             !.channel_state[<<sender_id, node_id>>] = RecordedMessages]

\* Check snapshot complete
SnapshotComplete(snapshot) ==
    \A n \in Nodes :
        /\ n \in DOMAIN snapshot.local_state
        /\ Cardinality(snapshot.markers_received[n]) = Cardinality(AllNeighbors(n))


\* Agreement: All correct processes decide on the same value
THEOREM ConsensusAgreement ==
    \A p1, p2 \in CorrectProcesses :
        Decided(p1) /\ Decided(p2) =>
            DecidedValue(p1) = DecidedValue(p2)

\* Validity: If all correct processes propose the same value, 
\* then any decided value must be that value
THEOREM ConsensusValidity ==
    (\A p \in CorrectProcesses : Proposed(p) = v) =>
        (\A p \in CorrectProcesses : Decided(p) => DecidedValue(p) = v)

\* Termination: All correct processes eventually decide
THEOREM ConsensusTermination ==
    \A p \in CorrectProcesses : Eventually(Decided(p))

\* Raft log matching property
THEOREM RaftLogMatching ==
    \A r1, r2 \in RaftReplicas, i \in Nat :
        (i <= Len(r1.log) /\ i <= Len(r2.log) /\
         r1.log[i].term = r2.log[i].term) =>
            r1.log[i] = r2.log[i]

\* Raft leader completeness
THEOREM RaftLeaderCompleteness ==
    \A term \in Nat, index \in Nat :
        CommittedInTerm(term, index) =>
            \A later_term \in Nat :
                later_term > term =>
                    LeaderHasEntry(later_term, index)

\* PBFT safety
THEOREM PBFTSafety ==
    \A r1, r2 \in PBFTReplicas, seq \in Nat :
        CommittedAtReplica(r1, seq) /\ CommittedAtReplica(r2, seq) =>
            CommittedValue(r1, seq) = CommittedValue(r2, seq)

\* PBFT liveness (assuming synchrony eventually)
THEOREM PBFTLiveness ==
    EventuallySynchronous =>
        \A request : EventuallyCommitted(request)

====

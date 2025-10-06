---- MODULE NyxStorageLayer ----
(****************************************************************************)
(* Nyx Protocol - Storage and Persistence Layer                            *)
(*                                                                          *)
(* Comprehensive specifications for storage management, persistence,       *)
(* replication, consistency, durability, and data lifecycle.               *)
(*                                                                          *)
(* Storage Components:                                                      *)
(*   - Key-value store with ACID properties                                *)
(*   - Distributed storage with replication                                *)
(*   - Consistency models (strong, eventual, causal)                       *)
(*   - Write-ahead logging and recovery                                    *)
(*   - Snapshot and checkpoint management                                  *)
(*   - Data versioning and conflict resolution                             *)
(*   - Compaction and garbage collection                                   *)
(*   - Caching strategies                                                  *)
(*   - Index management                                                    *)
(*   - Transaction processing                                              *)
(****************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, Integers, TLC,

(****************************************************************************)
(* Common Helper Operators                                                  *)
(****************************************************************************)

* Minimum of a set
MIN(S) == IF S = {} THEN 0 ELSE CHOOSE x in S : \A y in S : x <= y

* Maximum of a set
MAX(S) == IF S = {} THEN 0 ELSE CHOOSE x in S : \A y in S : x >= y

* Minimum (lowercase alias)
Min(x, y) == IF x < y THEN x ELSE y

* Maximum (lowercase alias)
Max(x, y) == IF x > y THEN x ELSE y

* Absolute value
Abs(x) == IF x < 0 THEN -x ELSE x

* Sum of set elements
Sum(S) == LET RECURSIVE SumRec(_)
              SumRec(T) == IF T = {} 
                          THEN 0 
                          ELSE LET x == CHOOSE y in T : TRUE
                               IN x + SumRec(T \ {x})
          IN SumRec(S)

* Average
Average(S) == IF S = {} THEN 0 ELSE Sum(S) / Cardinality(S)


        NyxDistributedConsensus

(****************************************************************************)
(* Key-Value Store                                                          *)
(****************************************************************************)

\* Key and value types
Key == STRING
Value == Any

\* Storage entry
StorageEntry == [
    key : Key,
    value : Value,
    version : Nat,
    timestamp : Nat,
    metadata : [
        ttl : Nat,
        tags : SUBSET STRING,
        checksum : STRING
    ]
]

\* Key-value store state
KVStore == [
    data : [Key -> StorageEntry],
    indices : [STRING -> [Any -> SUBSET Key]],
    size : Nat,
    max_size : Nat
]

\* Put operation
Put(store, key, value) ==
    LET entry == [
            key |-> key,
            value |-> value,
            version |-> IF key \in DOMAIN store.data
                       THEN store.data[key].version + 1
                       ELSE 1,
            timestamp |-> CurrentTime,
            metadata |-> [
                ttl |-> DefaultTTL,
                tags |-> {},
                checksum |-> ComputeChecksum(value)
            ]
        ]
        new_size == IF key \in DOMAIN store.data
                   THEN store.size - SizeOf(store.data[key].value) + SizeOf(value)
                   ELSE store.size + SizeOf(value)
    IN IF new_size <= store.max_size
       THEN [success |-> TRUE,
             store |-> [store EXCEPT
                 !.data[key] = entry,
                 !.size = new_size]]
       ELSE [success |-> FALSE,
             store |-> store]

\* Get operation
Get(store, key) ==
    IF key \in DOMAIN store.data
    THEN LET entry == store.data[key]
         IN IF CurrentTime - entry.timestamp <= entry.metadata.ttl
            THEN [found |-> TRUE, value |-> entry.value, version |-> entry.version]
            ELSE [found |-> FALSE, value |-> Null, version |-> 0]
    ELSE [found |-> FALSE, value |-> Null, version |-> 0]

\* Delete operation
Delete(store, key) ==
    IF key \in DOMAIN store.data
    THEN [success |-> TRUE,
          store |-> [store EXCEPT
              !.data = [k \in DOMAIN @ \ {key} |-> @[k]],
              !.size = @ - SizeOf(store.data[key].value)]]
    ELSE [success |-> FALSE, store |-> store]

\* Compare-and-swap
CompareAndSwap(store, key, expected_version, new_value) ==
    IF key \in DOMAIN store.data /\
       store.data[key].version = expected_version
    THEN Put(store, key, new_value)
    ELSE [success |-> FALSE, store |-> store]

(****************************************************************************)
(* Distributed Storage with Replication                                     *)
(****************************************************************************)

\* Replica state
ReplicaState == [
    replica_id : Node,
    data : KVStore,
    role : {"PRIMARY", "SECONDARY", "TERTIARY"},
    replication_log : Seq([
        operation : STRING,
        key : Key,
        value : Value,
        version : Nat,
        timestamp : Nat
    ]),
    last_applied : Nat,
    replication_lag : Nat
]

\* Replication group
ReplicationGroup == [
    group_id : STRING,
    replicas : SUBSET Node,
    primary : Node,
    replication_factor : Nat,
    consistency_level : {"STRONG", "EVENTUAL", "CAUSAL", "QUORUM"}
]

\* Replicate write
ReplicateWrite(rg, operation, key, value) ==
    LET log_entry == [
            operation |-> operation,
            key |-> key,
            value |-> value,
            version |-> NextVersion(key),
            timestamp |-> CurrentTime
        ]
        
        \* Primary executes write
        primary_result == ExecuteOnPrimary(rg.primary, log_entry)
        
        \* Replicate to secondaries
        replication_result == CASE rg.consistency_level = "STRONG" ->
                                  \* Wait for all replicas
                                  ReplicateToAll(rg.replicas, log_entry)
                             [] rg.consistency_level = "QUORUM" ->
                                  \* Wait for quorum
                                  ReplicateToQuorum(rg.replicas, log_entry)
                             [] rg.consistency_level = "EVENTUAL" ->
                                  \* Asynchronous replication
                                  ReplicateAsync(rg.replicas, log_entry)
                             [] rg.consistency_level = "CAUSAL" ->
                                  \* Causal consistency
                                  ReplicateCausal(rg.replicas, log_entry)
    IN [success |-> primary_result.success /\ replication_result.success,
        version |-> log_entry.version]

\* Read with consistency level
ReplicatedRead(rg, key, consistency_level) ==
    CASE consistency_level = "STRONG" ->
        \* Read from primary
        ReadFromPrimary(rg.primary, key)
    [] consistency_level = "QUORUM" ->
        \* Read from quorum and resolve
        QuorumRead(rg.replicas, key)
    [] consistency_level = "EVENTUAL" ->
        \* Read from any replica
        ReadFromAnyReplica(rg.replicas, key)
    [] consistency_level = "CAUSAL" ->
        \* Read with causal consistency
        CausalRead(rg.replicas, key)

\* Quorum read with conflict resolution
QuorumRead(replicas, key) ==
    LET quorum_size == (Cardinality(replicas) \div 2) + 1
        responses == ReadFromReplicas(replicas, key, quorum_size)
        versions == {r.version : r \in responses}
        max_version == Maximum(versions)
        latest_values == {r \in responses : r.version = max_version}
    IN IF Cardinality(latest_values) = 1
       THEN Head(latest_values)
       ELSE ResolveConflict(latest_values)

(****************************************************************************)
(* Consistency Models                                                       *)
(****************************************************************************)

\* Vector clock for causal consistency
VectorClock == [Node -> Nat]

\* Update vector clock
UpdateVectorClock(vc, node_id) ==
    [vc EXCEPT ![node_id] = @ + 1]

\* Compare vector clocks
CompareVectorClocks(vc1, vc2) ==
    LET vc1_dominates == \A n \in DOMAIN vc1 : vc1[n] >= vc2[n]
        vc2_dominates == \A n \in DOMAIN vc2 : vc2[n] >= vc1[n]
    IN IF vc1_dominates /\ ~vc2_dominates
       THEN "GREATER"
       ELSE IF vc2_dominates /\ ~vc1_dominates
            THEN "LESS"
            ELSE IF vc1 = vc2
                 THEN "EQUAL"
                 ELSE "CONCURRENT"

\* Merge vector clocks
MergeVectorClocks(vc1, vc2) ==
    [n \in (DOMAIN vc1) \union (DOMAIN vc2) |->
        Max(IF n \in DOMAIN vc1 THEN vc1[n] ELSE 0,
            IF n \in DOMAIN vc2 THEN vc2[n] ELSE 0)]

\* Causal consistency write
CausalWrite(replica, key, value, vector_clock) ==
    LET updated_vc == UpdateVectorClock(vector_clock, replica.replica_id)
        entry == [
            key |-> key,
            value |-> value,
            version |-> NextVersion(key),
            timestamp |-> CurrentTime,
            vector_clock |-> updated_vc
        ]
    IN [replica EXCEPT
           !.data = Put(@, key, value).store,
           !.replication_log = Append(@, entry)]

\* Causal consistency read
CausalRead(replica, key, required_vc) ==
    LET entry == Get(replica.data, key)
    IN IF entry.found /\
          CompareVectorClocks(entry.vector_clock, required_vc) \in {"GREATER", "EQUAL"}
       THEN entry
       ELSE [found |-> FALSE, value |-> Null]

(****************************************************************************)
(* Write-Ahead Logging and Recovery                                         *)
(****************************************************************************)

\* WAL entry
WALEntry == [
    sequence_number : Nat,
    operation : {"PUT", "DELETE", "BEGIN_TX", "COMMIT_TX", "ABORT_TX"},
    key : Key,
    value : Value,
    transaction_id : STRING,
    checksum : STRING,
    timestamp : Nat
]

\* Write-ahead log
WriteAheadLog == [
    entries : Seq(WALEntry),
    next_sequence : Nat,
    flush_lsn : Nat,  \* Last flushed log sequence number
    checkpoint_lsn : Nat
]

\* Append to WAL
AppendWAL(wal, operation, key, value, tx_id) ==
    LET entry == [
            sequence_number |-> wal.next_sequence,
            operation |-> operation,
            key |-> key,
            value |-> value,
            transaction_id |-> tx_id,
            checksum |-> ComputeChecksum(<<operation, key, value>>),
            timestamp |-> CurrentTime
        ]
    IN [wal EXCEPT
           !.entries = Append(@, entry),
           !.next_sequence = @ + 1]

\* Flush WAL to disk
FlushWAL(wal, target_lsn) ==
    IF target_lsn <= wal.next_sequence
    THEN [wal EXCEPT !.flush_lsn = target_lsn]
    ELSE wal

\* Replay WAL for recovery
ReplayWAL(store, wal, from_lsn, to_lsn) ==
    LET entries_to_replay == SelectSeq(wal.entries,
            LAMBDA e : e.sequence_number >= from_lsn /\
                      e.sequence_number <= to_lsn)
        
        RECURSIVE ApplyEntries(_,_)
        ApplyEntries(s, entries) ==
            IF entries = <<>>
            THEN s
            ELSE LET entry == Head(entries)
                     updated_store == CASE entry.operation = "PUT" ->
                                          Put(s, entry.key, entry.value).store
                                      [] entry.operation = "DELETE" ->
                                          Delete(s, entry.key).store
                                      [] OTHER -> s
                 IN ApplyEntries(updated_store, Tail(entries))
    IN ApplyEntries(store, entries_to_replay)

\* Checkpoint
CreateCheckpoint(store, wal) ==
    LET checkpoint == [
            store_snapshot |-> store,
            wal_lsn |-> wal.next_sequence - 1,
            timestamp |-> CurrentTime
        ]
    IN [wal EXCEPT !.checkpoint_lsn = checkpoint.wal_lsn]

(****************************************************************************)
(* Data Versioning and Conflict Resolution                                  *)
(****************************************************************************)

\* Multi-version entry
MultiVersionEntry == [
    key : Key,
    versions : Seq([
        value : Value,
        version : Nat,
        timestamp : Nat,
        vector_clock : VectorClock
    ])
]

\* Multi-version concurrency control
MVCCStore == [
    data : [Key -> MultiVersionEntry],
    active_transactions : [STRING -> Nat],  \* tx_id -> snapshot_version
    version_counter : Nat
]

\* MVCC read
MVCCRead(mvcc, key, tx_id) ==
    IF key \in DOMAIN mvcc.data
    THEN LET snapshot_version == mvcc.active_transactions[tx_id]
             entry == mvcc.data[key]
             visible_versions == SelectSeq(entry.versions,
                 LAMBDA v : v.version <= snapshot_version)
         IN IF visible_versions # <<>>
            THEN [found |-> TRUE, value |-> Last(visible_versions).value]
            ELSE [found |-> FALSE, value |-> Null]
    ELSE [found |-> FALSE, value |-> Null]

\* MVCC write
MVCCWrite(mvcc, key, value, tx_id) ==
    LET new_version == [
            value |-> value,
            version |-> mvcc.version_counter,
            timestamp |-> CurrentTime,
            vector_clock |-> InitVectorClock()
        ]
        updated_entry == IF key \in DOMAIN mvcc.data
                        THEN [mvcc.data[key] EXCEPT
                                !.versions = Append(@, new_version)]
                        ELSE [key |-> key,
                              versions |-> <<new_version>>]
    IN [mvcc EXCEPT
           !.data[key] = updated_entry,
           !.version_counter = @ + 1]

\* Conflict resolution strategies
ConflictResolution == [
    strategy : {"LAST_WRITE_WINS", "MERGE", "MANUAL", "VERSION_VECTOR"},
    custom_merger : [Value \X Value -> Value]
]

\* Resolve conflicting versions
ResolveConflict(versions, resolution_strategy) ==
    CASE resolution_strategy = "LAST_WRITE_WINS" ->
        LET latest == CHOOSE v \in versions :
                \A other \in versions : v.timestamp >= other.timestamp
        IN latest.value
    [] resolution_strategy = "VERSION_VECTOR" ->
        LET concurrent == {v \in versions :
                ~\E other \in versions :
                    CompareVectorClocks(other.vector_clock, v.vector_clock) = "GREATER"}
        IN IF Cardinality(concurrent) = 1
           THEN (CHOOSE v \in concurrent : TRUE).value
           ELSE MergeValues({v.value : v \in concurrent})
    [] resolution_strategy = "MERGE" ->
        MergeValues({v.value : v \in versions})

(****************************************************************************)
(* Compaction and Garbage Collection                                        *)
(****************************************************************************)

\* Compaction state
CompactionState == [
    last_compaction : Nat,
    compaction_threshold : Nat,
    deleted_keys : SUBSET Key,
    expired_keys : SUBSET Key
]

\* Identify garbage
IdentifyGarbage(store, compaction_state) ==
    LET expired == {k \in DOMAIN store.data :
            LET entry == store.data[k]
            IN CurrentTime - entry.timestamp > entry.metadata.ttl}
        deleted == compaction_state.deleted_keys
    IN [expired |-> expired, deleted |-> deleted]

\* Compact store
CompactStore(store, garbage) ==
    LET keys_to_remove == garbage.expired \union garbage.deleted
        compacted_data == [k \in (DOMAIN store.data) \ keys_to_remove |->
                          store.data[k]]
        reclaimed_size == Sum({SizeOf(store.data[k].value) : k \in keys_to_remove})
    IN [store EXCEPT
           !.data = compacted_data,
           !.size = @ - reclaimed_size]

\* Compact MVCC versions
CompactMVCCVersions(mvcc, retention_versions) ==
    LET compacted_data == [k \in DOMAIN mvcc.data |->
            LET entry == mvcc.data[k]
                versions_to_keep == IF Len(entry.versions) <= retention_versions
                                   THEN entry.versions
                                   ELSE SubSeq(entry.versions,
                                             Len(entry.versions) - retention_versions + 1,
                                             Len(entry.versions))
            IN [entry EXCEPT !.versions = versions_to_keep]]
    IN [mvcc EXCEPT !.data = compacted_data]

(****************************************************************************)
(* Caching                                                                  *)
(****************************************************************************)

\* Cache entry
CacheEntry == [
    key : Key,
    value : Value,
    access_count : Nat,
    last_access : Nat,
    size : Nat
]

\* Cache
Cache == [
    entries : [Key -> CacheEntry],
    max_size : Nat,
    current_size : Nat,
    eviction_policy : {"LRU", "LFU", "FIFO", "RANDOM"},
    hit_count : Nat,
    miss_count : Nat
]

\* Cache get
CacheGet(cache, key) ==
    IF key \in DOMAIN cache.entries
    THEN LET entry == cache.entries[key]
             updated_entry == [entry EXCEPT
                 !.access_count = @ + 1,
                 !.last_access = CurrentTime]
         IN [hit |-> TRUE,
             value |-> entry.value,
             cache |-> [cache EXCEPT
                 !.entries[key] = updated_entry,
                 !.hit_count = @ + 1]]
    ELSE [hit |-> FALSE,
          value |-> Null,
          cache |-> [cache EXCEPT !.miss_count = @ + 1]]

\* Cache put with eviction
CachePut(cache, key, value) ==
    LET entry == [
            key |-> key,
            value |-> value,
            access_count |-> 1,
            last_access |-> CurrentTime,
            size |-> SizeOf(value)
        ]
        new_size == IF key \in DOMAIN cache.entries
                   THEN cache.current_size - cache.entries[key].size + entry.size
                   ELSE cache.current_size + entry.size
    IN IF new_size <= cache.max_size
       THEN [cache EXCEPT
               !.entries[key] = entry,
               !.current_size = new_size]
       ELSE LET evicted == SelectEvictionCandidate(cache)
                cache_after_eviction == [cache EXCEPT
                    !.entries = [k \in DOMAIN @ \ {evicted} |-> @[k]],
                    !.current_size = @ - cache.entries[evicted].size]
            IN CachePut(cache_after_eviction, key, value)

\* Select eviction candidate
SelectEvictionCandidate(cache) ==
    CASE cache.eviction_policy = "LRU" ->
        CHOOSE k \in DOMAIN cache.entries :
            \A other \in DOMAIN cache.entries :
                cache.entries[k].last_access <= cache.entries[other].last_access
    [] cache.eviction_policy = "LFU" ->
        CHOOSE k \in DOMAIN cache.entries :
            \A other \in DOMAIN cache.entries :
                cache.entries[k].access_count <= cache.entries[other].access_count
    [] cache.eviction_policy = "FIFO" ->
        CHOOSE k \in DOMAIN cache.entries :
            \A other \in DOMAIN cache.entries :
                cache.entries[k].last_access <= cache.entries[other].last_access
    [] cache.eviction_policy = "RANDOM" ->
        CHOOSE k \in DOMAIN cache.entries : TRUE

(****************************************************************************)
(* Transaction Processing                                                   *)
(****************************************************************************)

\* Transaction state
TransactionState == [
    tx_id : STRING,
    state : {"ACTIVE", "PREPARING", "COMMITTED", "ABORTED"},
    read_set : SUBSET Key,
    write_set : [Key -> Value],
    start_time : Nat,
    timeout : Nat
]

\* Two-phase commit coordinator
TwoPhaseCommitCoordinator == [
    active_transactions : [STRING -> TransactionState],
    participants : SUBSET Node,
    prepare_votes : [STRING -> [Node -> BOOLEAN]],
    commit_log : Seq([tx_id : STRING, decision : STRING, timestamp : Nat])
]

\* Begin transaction
BeginTransaction(tpc) ==
    LET tx_id == GenerateTransactionId()
        tx_state == [
            tx_id |-> tx_id,
            state |-> "ACTIVE",
            read_set |-> {},
            write_set |-> [k \in {} |-> Null],
            start_time |-> CurrentTime,
            timeout |-> DefaultTransactionTimeout
        ]
    IN [tpc EXCEPT
           !.active_transactions[tx_id] = tx_state]

\* Prepare phase
Prepare2PC(tpc, tx_id) ==
    LET tx == tpc.active_transactions[tx_id]
        prepare_msgs == [p \in tpc.participants |->
            [type |-> "PREPARE",
             tx_id |-> tx_id,
             write_set |-> tx.write_set]]
    IN [tpc EXCEPT
           !.active_transactions[tx_id].state = "PREPARING"]

\* Collect prepare votes
CollectVotes(tpc, tx_id, participant, vote) ==
    [tpc EXCEPT
        !.prepare_votes[tx_id][participant] = vote]

\* Commit/Abort decision
Decide2PC(tpc, tx_id) ==
    LET votes == tpc.prepare_votes[tx_id]
        all_yes == \A p \in DOMAIN votes : votes[p] = TRUE
        decision == IF all_yes THEN "COMMIT" ELSE "ABORT"
        log_entry == [tx_id |-> tx_id,
                     decision |-> decision,
                     timestamp |-> CurrentTime]
    IN [tpc EXCEPT
           !.active_transactions[tx_id].state = decision ++ "TED",
           !.commit_log = Append(@, log_entry)]

(****************************************************************************)
(* Storage Properties and Invariants                                        *)
(****************************************************************************)

\* Durability
THEOREM Durability ==
    \A tx \in Transactions :
        Committed(tx) =>
            Eventually(PersistentlyStored(tx.write_set))

\* Atomicity
THEOREM Atomicity ==
    \A tx \in Transactions :
        Committed(tx) => AllWritesVisible(tx.write_set) \/
        Aborted(tx) => NoWritesVisible(tx.write_set)

\* Replication consistency
THEOREM ReplicationConsistency ==
    \A rg \in ReplicationGroups, k \in Keys :
        Eventually(\A r1, r2 \in rg.replicas :
            Get(r1.data, k) = Get(r2.data, k))

\* Cache coherence
THEOREM CacheCoherence ==
    \A cache \in Caches, store \in Stores, key \in Keys :
        key \in DOMAIN cache.entries =>
            cache.entries[key].value = Get(store, key).value \/
            Invalidated(cache, key)

====

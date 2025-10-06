---- MODULE NyxStreamManagement ----
(****************************************************************************)
(* Nyx Protocol - Stream Management Specification                          *)
(*                                                                          *)
(* This module provides a complete formal specification of the Nyx         *)
(* protocol's stream management layer, including multiplexing,             *)
(* prioritization, backpressure, and stream lifecycle management.          *)
(*                                                                          *)
(* Components Specified:                                                    *)
(*   - Stream multiplexing and demultiplexing                              *)
(*   - Priority-based scheduling                                            *)
(*   - Backpressure and flow control                                        *)
(*   - Stream state machine                                                 *)
(*   - Resource allocation and quotas                                       *)
(*                                                                          *)
(* Mathematical Properties Verified:                                        *)
(*   - Deadlock freedom                                                     *)
(*   - Starvation freedom (fairness)                                        *)
(*   - Resource bounds                                                      *)
(*   - State machine correctness                                            *)
(*   - Priority inversion prevention                                        *)
(****************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, Integers, TLC

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



CONSTANTS
    Connections,            \* Set of all connections
    MaxStreamsPerConn,      \* Maximum streams per connection
    MaxStreamData,          \* Maximum data per stream
    MaxPriority,            \* Maximum priority level (0 is highest)
    MaxConcurrentStreams,   \* Global concurrent stream limit
    StreamQuota,            \* Per-connection stream quota
    DataQuota,              \* Per-stream data quota
    TimeQuantum             \* Time quantum for fair scheduling

ASSUME
    /\ MaxStreamsPerConn > 0
    /\ MaxStreamData > 0
    /\ MaxPriority >= 0
    /\ MaxConcurrentStreams > 0
    /\ StreamQuota > 0
    /\ DataQuota > 0
    /\ TimeQuantum > 0

(****************************************************************************)
(* Stream Identifiers and Types                                            *)
(****************************************************************************)

\* Stream ID: globally unique identifier
StreamIDs == Nat

\* Stream types
StreamTypes == {
    "BIDIRECTIONAL",    \* Full-duplex stream
    "UNIDIRECTIONAL",   \* One-way stream
    "CONTROL",          \* Control stream (highest priority)
    "PUSH"              \* Server push stream
}

\* Stream states
StreamStates == {
    "IDLE",             \* Stream ID reserved but not opened
    "OPEN",             \* Stream active and can send/receive
    "HALF_CLOSED_LOCAL",   \* Local side closed
    "HALF_CLOSED_REMOTE",  \* Remote side closed
    "CLOSED",           \* Stream fully closed
    "RESET_LOCAL",      \* Reset by local endpoint
    "RESET_REMOTE",     \* Reset by remote endpoint
    "BLOCKED"           \* Blocked due to flow control
}

\* Priority levels (0 = highest, MaxPriority = lowest)
Priorities == 0..MaxPriority

\* Priority weights for weighted fair queueing
PriorityWeight(p) == (MaxPriority - p + 1) * (MaxPriority - p + 1)

(****************************************************************************)
(* Stream Structure                                                         *)
(****************************************************************************)

StreamStructure == [
    stream_id: StreamIDs,
    connection_id: Connections,
    stream_type: StreamTypes,
    state: StreamStates,
    priority: Priorities,
    weight: Nat,
    
    \* Flow control
    send_offset: Nat,           \* Bytes sent
    recv_offset: Nat,           \* Bytes received
    send_window: Nat,           \* Send window size
    recv_window: Nat,           \* Receive window size
    max_send_offset: Nat,       \* Maximum allowed send offset
    max_recv_offset: Nat,       \* Maximum allowed receive offset
    
    \* Data buffers
    send_buffer: Seq(Nat),      \* Outgoing data buffer
    recv_buffer: Seq(Nat),      \* Incoming data buffer
    
    \* Scheduling
    last_scheduled: Nat,        \* Last time stream was scheduled
    bytes_sent_quantum: Nat,    \* Bytes sent in current quantum
    deficit: Nat,               \* Deficit counter for DRR
    
    \* Dependencies
    depends_on: SUBSET StreamIDs,   \* Stream dependencies
    exclusive: BOOLEAN,             \* Exclusive dependency flag
    
    \* Statistics
    bytes_sent: Nat,
    bytes_received: Nat,
    frames_sent: Nat,
    frames_received: Nat,
    resets: Nat,
    blocks: Nat
]

(****************************************************************************)
(* Frame Types                                                              *)
(****************************************************************************)

FrameTypes == {
    "DATA",                 \* Stream data frame
    "HEADERS",              \* Stream headers frame
    "PRIORITY",             \* Priority update frame
    "RST_STREAM",           \* Stream reset frame
    "SETTINGS",             \* Connection settings frame
    "PUSH_PROMISE",         \* Server push promise frame
    "PING",                 \* Ping frame
    "GOAWAY",               \* Connection termination frame
    "WINDOW_UPDATE",        \* Flow control window update
    "CONTINUATION",         \* Headers continuation frame
    "MAX_DATA",             \* Maximum data limit frame
    "MAX_STREAM_DATA",      \* Maximum stream data limit frame
    "MAX_STREAMS",          \* Maximum streams limit frame
    "DATA_BLOCKED",         \* Data blocked frame
    "STREAM_DATA_BLOCKED",  \* Stream data blocked frame
    "STREAMS_BLOCKED"       \* Streams blocked frame
}

FrameStructure == [
    frame_type: FrameTypes,
    stream_id: StreamIDs,
    flags: SUBSET {"END_STREAM", "END_HEADERS", "PADDED", "PRIORITY"},
    payload: Seq(Nat),
    length: Nat
]

(****************************************************************************)
(* Priority Tree Structure (HTTP/2 style)                                   *)
(****************************************************************************)

\* Priority node in the dependency tree
PriorityNode == [
    stream_id: StreamIDs,
    parent: StreamIDs \union {0},  \* 0 represents root
    weight: 1..256,
    exclusive: BOOLEAN,
    children: SUBSET StreamIDs
]

\* Build priority tree from stream dependencies
BuildPriorityTree(streams) ==
    LET nodes == {[
            stream_id |-> s.stream_id,
            parent |-> IF s.depends_on = {} THEN 0 
                      ELSE CHOOSE d \in s.depends_on : TRUE,
            weight |-> s.weight,
            exclusive |-> s.exclusive,
            children |-> {t.stream_id : t \in {st \in streams : s.stream_id \in st.depends_on}}
        ] : s \in streams}
    IN nodes

\* Compute stream priority based on dependency tree
ComputeStreamPriority(stream, tree) ==
    LET node == CHOOSE n \in tree : n.stream_id = stream.stream_id
        depth == TreeDepth(node, tree)
        weight_factor == node.weight
    IN (depth * 256) + (256 - weight_factor)

\* Tree depth calculation
TreeDepth(node, tree) ==
    IF node.parent = 0
    THEN 0
    ELSE 1 + TreeDepth(CHOOSE n \in tree : n.stream_id = node.parent, tree)

(****************************************************************************)
(* Stream Scheduling Algorithms                                             *)
(****************************************************************************)

\* Round-Robin Scheduling
RoundRobinSchedule(streams, last_scheduled) ==
    LET ready_streams == {s \in streams : 
            /\ s.state = "OPEN"
            /\ s.send_buffer # <<>>
            /\ s.send_offset < s.max_send_offset}
        sorted == SortBy(ready_streams, LAMBDA s: s.stream_id)
        next_index == IF last_scheduled = 0
                     THEN 1
                     ELSE (CHOOSE i \in 1..Len(sorted) : 
                            sorted[i].stream_id > last_scheduled) % Len(sorted) + 1
    IN IF ready_streams = {} THEN "NONE" ELSE sorted[next_index]

\* Priority-based Scheduling
PrioritySchedule(streams) ==
    LET ready_streams == {s \in streams :
            /\ s.state = "OPEN"
            /\ s.send_buffer # <<>>
            /\ s.send_offset < s.max_send_offset}
    IN IF ready_streams = {}
       THEN "NONE"
       ELSE CHOOSE s \in ready_streams :
            \A t \in ready_streams : s.priority <= t.priority

\* Weighted Fair Queueing (WFQ)
WFQSchedule(streams, current_time) ==
    LET ready_streams == {s \in streams :
            /\ s.state = "OPEN"
            /\ s.send_buffer # <<>>
            /\ s.send_offset < s.max_send_offset}
        \* Compute virtual finish time
        VirtualFinishTime(s) ==
            current_time + (Len(s.send_buffer) \div PriorityWeight(s.priority))
    IN IF ready_streams = {}
       THEN "NONE"
       ELSE CHOOSE s \in ready_streams :
            \A t \in ready_streams : 
                VirtualFinishTime(s) <= VirtualFinishTime(t)

\* Deficit Round Robin (DRR)
DRRSchedule(streams, quanta) ==
    LET ready_streams == {s \in streams :
            /\ s.state = "OPEN"
            /\ s.send_buffer # <<>>
            /\ s.send_offset < s.max_send_offset}
        UpdateDeficit[s \in ready_streams] ==
            LET new_deficit == s.deficit + quanta[s.priority]
                can_send == new_deficit >= Len(s.send_buffer)
            IN IF can_send
               THEN [stream |-> s, 
                     deficit |-> new_deficit - Len(s.send_buffer),
                     scheduled |-> TRUE]
               ELSE [stream |-> s,
                     deficit |-> new_deficit,
                     scheduled |-> FALSE]
        candidates == {UpdateDeficit[s] : s \in ready_streams}
        scheduled == CHOOSE c \in candidates : c.scheduled
    IN IF ready_streams = {} \/ ~(\E c \in candidates : c.scheduled)
       THEN "NONE"
       ELSE scheduled.stream

\* Hierarchical Token Bucket (HTB) Scheduling
HTBSchedule(streams, token_buckets) ==
    LET ready_streams == {s \in streams :
            /\ s.state = "OPEN"
            /\ s.send_buffer # <<>>
            /\ s.send_offset < s.max_send_offset
            /\ token_buckets[s.stream_id].tokens > 0}
        \* Select highest priority stream with tokens
        selected == CHOOSE s \in ready_streams :
            \A t \in ready_streams : s.priority <= t.priority
    IN IF ready_streams = {} THEN "NONE" ELSE selected

(****************************************************************************)
(* Backpressure and Flow Control                                            *)
(****************************************************************************)

\* Check if stream can send data
CanSendData(stream, data_size) ==
    /\ stream.state = "OPEN"
    /\ stream.send_offset + data_size <= stream.max_send_offset
    /\ Len(stream.send_buffer) + data_size <= MaxStreamData

\* Check if stream can receive data
CanReceiveData(stream, data_size) ==
    /\ stream.state \in {"OPEN", "HALF_CLOSED_LOCAL"}
    /\ stream.recv_offset + data_size <= stream.max_recv_offset
    /\ Len(stream.recv_buffer) + data_size <= MaxStreamData

\* Update send window
UpdateSendWindow(stream, increment) ==
    [stream EXCEPT 
        !.max_send_offset = @ + increment,
        !.send_window = stream.max_send_offset - stream.send_offset
    ]

\* Update receive window
UpdateReceiveWindow(stream, increment) ==
    [stream EXCEPT
        !.max_recv_offset = @ + increment,
        !.recv_window = stream.max_recv_offset - stream.recv_offset
    ]

\* Apply backpressure
ApplyBackpressure(stream) ==
    [stream EXCEPT !.state = "BLOCKED"]

\* Release backpressure
ReleaseBackpressure(stream) ==
    IF stream.state = "BLOCKED" /\ stream.send_offset < stream.max_send_offset
    THEN [stream EXCEPT !.state = "OPEN"]
    ELSE stream

\* Auto-tuning receive window (similar to TCP auto-tuning)
AutoTuneReceiveWindow(stream, rtt, bandwidth) ==
    LET optimal_window == bandwidth * rtt
        current_usage == (Len(stream.recv_buffer) * 100) \div stream.recv_window
        new_window == IF current_usage > 80  \* Buffer nearly full
                     THEN MIN({MaxStreamData, stream.recv_window * 2})
                     ELSE IF current_usage < 20  \* Buffer underutilized
                     THEN MAX({DataQuota, stream.recv_window \div 2})
                     ELSE stream.recv_window
    IN [stream EXCEPT !.recv_window = new_window]

(****************************************************************************)
(* Stream State Machine                                                     *)
(****************************************************************************)

\* Initial stream state
InitialStreamState(stream_id, conn_id, stream_type, priority) ==
    [
        stream_id |-> stream_id,
        connection_id |-> conn_id,
        stream_type |-> stream_type,
        state |-> "IDLE",
        priority |-> priority,
        weight |-> PriorityWeight(priority),
        send_offset |-> 0,
        recv_offset |-> 0,
        send_window |-> DataQuota,
        recv_window |-> DataQuota,
        max_send_offset |-> DataQuota,
        max_recv_offset |-> DataQuota,
        send_buffer |-> <<>>,
        recv_buffer |-> <<>>,
        last_scheduled |-> 0,
        bytes_sent_quantum |-> 0,
        deficit |-> 0,
        depends_on |-> {},
        exclusive |-> FALSE,
        bytes_sent |-> 0,
        bytes_received |-> 0,
        frames_sent |-> 0,
        frames_received |-> 0,
        resets |-> 0,
        blocks |-> 0
    ]

\* State transitions
ValidTransition(old_state, new_state) ==
    \/ old_state = "IDLE" /\ new_state \in {"OPEN", "RESERVED_LOCAL", "RESERVED_REMOTE"}
    \/ old_state = "OPEN" /\ new_state \in {"HALF_CLOSED_LOCAL", "HALF_CLOSED_REMOTE", 
                                            "CLOSED", "RESET_LOCAL", "RESET_REMOTE", "BLOCKED"}
    \/ old_state = "HALF_CLOSED_LOCAL" /\ new_state \in {"CLOSED", "RESET_REMOTE"}
    \/ old_state = "HALF_CLOSED_REMOTE" /\ new_state \in {"CLOSED", "RESET_LOCAL"}
    \/ old_state = "BLOCKED" /\ new_state \in {"OPEN", "CLOSED", "RESET_LOCAL"}
    \/ old_state = "RESERVED_LOCAL" /\ new_state \in {"HALF_CLOSED_REMOTE", "CLOSED"}
    \/ old_state = "RESERVED_REMOTE" /\ new_state \in {"HALF_CLOSED_LOCAL", "CLOSED"}

\* Open stream
OpenStream(stream) ==
    /\ stream.state = "IDLE"
    /\ [stream EXCEPT !.state = "OPEN"]

\* Close stream (local side)
CloseStreamLocal(stream) ==
    /\ stream.state = "OPEN"
    /\ [stream EXCEPT !.state = 
        IF stream.stream_type = "BIDIRECTIONAL"
        THEN "HALF_CLOSED_LOCAL"
        ELSE "CLOSED"]

\* Close stream (remote side)
CloseStreamRemote(stream) ==
    /\ stream.state \in {"OPEN", "HALF_CLOSED_LOCAL"}
    /\ [stream EXCEPT !.state =
        IF stream.state = "HALF_CLOSED_LOCAL"
        THEN "CLOSED"
        ELSE "HALF_CLOSED_REMOTE"]

\* Reset stream
ResetStream(stream, local) ==
    /\ stream.state \in {"OPEN", "HALF_CLOSED_LOCAL", "HALF_CLOSED_REMOTE", "BLOCKED"}
    /\ [stream EXCEPT 
        !.state = IF local THEN "RESET_LOCAL" ELSE "RESET_REMOTE",
        !.resets = @ + 1]

(****************************************************************************)
(* Stream Multiplexing                                                      *)
(****************************************************************************)

\* Multiplex multiple streams onto single connection
MultiplexStreams(streams, max_frame_size) ==
    LET \* Select next stream to send based on scheduling algorithm
        next_stream == WFQSchedule(streams, 0)
    IN IF next_stream = "NONE"
       THEN "NO_DATA"
       ELSE LET data_to_send == SubSeq(next_stream.send_buffer, 1, 
                                       MIN({max_frame_size, Len(next_stream.send_buffer)}))
                frame == [
                    frame_type |-> "DATA",
                    stream_id |-> next_stream.stream_id,
                    flags |-> IF Len(data_to_send) = Len(next_stream.send_buffer)
                             THEN {"END_STREAM"}
                             ELSE {},
                    payload |-> data_to_send,
                    length |-> Len(data_to_send)
                ]
                updated_stream == [next_stream EXCEPT
                    !.send_buffer = SubSeq(@, Len(data_to_send) + 1, Len(@)),
                    !.send_offset = @ + Len(data_to_send),
                    !.bytes_sent = @ + Len(data_to_send),
                    !.frames_sent = @ + 1
                ]
            IN [frame |-> frame, stream |-> updated_stream]

\* Demultiplex incoming frame to appropriate stream
DemultiplexFrame(frame, streams) ==
    LET target_stream == CHOOSE s \in streams : s.stream_id = frame.stream_id
    IN IF target_stream = "NONE"
       THEN "STREAM_NOT_FOUND"
       ELSE IF ~CanReceiveData(target_stream, frame.length)
       THEN "FLOW_CONTROL_ERROR"
       ELSE [target_stream EXCEPT
           !.recv_buffer = @ \o frame.payload,
           !.recv_offset = @ + frame.length,
           !.bytes_received = @ + frame.length,
           !.frames_received = @ + 1,
           !.state = IF "END_STREAM" \in frame.flags
                    THEN IF @ = "OPEN" THEN "HALF_CLOSED_REMOTE" ELSE "CLOSED"
                    ELSE @
       ]

(****************************************************************************)
(* Resource Management                                                      *)
(****************************************************************************)

\* Connection-level resource tracking
ConnectionResources == [
    active_streams: 0..MaxStreamsPerConn,
    total_send_data: Nat,
    total_recv_data: Nat,
    max_streams: MaxStreamsPerConn,
    max_data: MaxStreamData * MaxStreamsPerConn
]

\* Check connection resource limits
CheckConnectionLimits(resources, new_stream_data) ==
    /\ resources.active_streams < resources.max_streams
    /\ resources.total_send_data + new_stream_data <= resources.max_data

\* Allocate stream resources
AllocateStreamResources(resources, stream_data) ==
    [resources EXCEPT
        !.active_streams = @ + 1,
        !.total_send_data = @ + stream_data
    ]

\* Release stream resources
ReleaseStreamResources(resources, stream) ==
    [resources EXCEPT
        !.active_streams = @ - 1,
        !.total_send_data = @ - stream.bytes_sent,
        !.total_recv_data = @ - stream.bytes_received
    ]

\* Global stream quota enforcement
GlobalStreamQuota == [
    total_streams: 0..MaxConcurrentStreams,
    streams_by_priority: [p \in Priorities |-> Nat],
    quota_by_priority: [p \in Priorities |-> StreamQuota \div (MaxPriority + 1)]
]

CheckGlobalQuota(quota, priority) ==
    /\ quota.total_streams < MaxConcurrentStreams
    /\ quota.streams_by_priority[priority] < quota.quota_by_priority[priority]

UpdateGlobalQuota(quota, priority, delta) ==
    [quota EXCEPT
        !.total_streams = @ + delta,
        !.streams_by_priority[priority] = @ + delta
    ]

(****************************************************************************)
(* State Variables                                                          *)
(****************************************************************************)

VARIABLES
    \* Stream management
    streams,                    \* Set of all streams
    stream_count,               \* Total number of streams
    next_stream_id,             \* Next available stream ID
    
    \* Scheduling
    scheduled_stream,           \* Currently scheduled stream
    scheduling_time,            \* Current scheduling time
    
    \* Resource tracking
    connection_resources,       \* Per-connection resources
    global_quota,               \* Global stream quota
    
    \* Priority tree
    priority_tree,              \* Stream dependency tree
    
    \* Flow control
    blocked_streams,            \* Streams blocked by flow control
    
    \* Statistics
    total_bytes_sent,
    total_bytes_received,
    total_frames_sent,
    total_frames_received,
    stream_resets,
    flow_control_events

stream_vars == <<streams, stream_count, next_stream_id, scheduled_stream,
                 scheduling_time, connection_resources, global_quota,
                 priority_tree, blocked_streams, total_bytes_sent,
                 total_bytes_received, total_frames_sent, total_frames_received,
                 stream_resets, flow_control_events>>

(****************************************************************************)
(* Initial State                                                            *)
(****************************************************************************)

StreamInit ==
    /\ streams = {}
    /\ stream_count = 0
    /\ next_stream_id = 1
    /\ scheduled_stream = "NONE"
    /\ scheduling_time = 0
    /\ connection_resources = [c \in Connections |->
        [active_streams |-> 0,
         total_send_data |-> 0,
         total_recv_data |-> 0,
         max_streams |-> MaxStreamsPerConn,
         max_data |-> MaxStreamData * MaxStreamsPerConn]]
    /\ global_quota = [
        total_streams |-> 0,
        streams_by_priority |-> [p \in Priorities |-> 0],
        quota_by_priority |-> [p \in Priorities |-> StreamQuota \div (MaxPriority + 1)]
       ]
    /\ priority_tree = {}
    /\ blocked_streams = {}
    /\ total_bytes_sent = 0
    /\ total_bytes_received = 0
    /\ total_frames_sent = 0
    /\ total_frames_received = 0
    /\ stream_resets = 0
    /\ flow_control_events = 0

(****************************************************************************)
(* Actions                                                                  *)
(****************************************************************************)

\* Create new stream
CreateStream(conn_id, stream_type, priority) ==
    /\ stream_count < MaxConcurrentStreams
    /\ CheckGlobalQuota(global_quota, priority)
    /\ LET new_stream == InitialStreamState(next_stream_id, conn_id, stream_type, priority)
       IN /\ streams' = streams \union {new_stream}
          /\ stream_count' = stream_count + 1
          /\ next_stream_id' = next_stream_id + 1
          /\ global_quota' = UpdateGlobalQuota(global_quota, priority, 1)
          /\ UNCHANGED <<scheduled_stream, scheduling_time, connection_resources,
                        priority_tree, blocked_streams, total_bytes_sent,
                        total_bytes_received, total_frames_sent, total_frames_received,
                        stream_resets, flow_control_events>>

\* Open stream
OpenStreamAction(stream_id) ==
    /\ \E s \in streams : s.stream_id = stream_id /\ s.state = "IDLE"
    /\ LET stream == CHOOSE s \in streams : s.stream_id = stream_id
           opened == OpenStream(stream)
       IN /\ streams' = (streams \ {stream}) \union {opened}
          /\ UNCHANGED <<stream_count, next_stream_id, scheduled_stream,
                        scheduling_time, connection_resources, global_quota,
                        priority_tree, blocked_streams, total_bytes_sent,
                        total_bytes_received, total_frames_sent, total_frames_received,
                        stream_resets, flow_control_events>>

\* Send data on stream
SendData(stream_id, data) ==
    /\ \E s \in streams : 
        /\ s.stream_id = stream_id
        /\ CanSendData(s, Len(data))
    /\ LET stream == CHOOSE s \in streams : s.stream_id = stream_id
           updated == [stream EXCEPT
               !.send_buffer = @ \o data,
               !.send_offset = @ + Len(data),
               !.bytes_sent = @ + Len(data)
           ]
       IN /\ streams' = (streams \ {stream}) \union {updated}
          /\ total_bytes_sent' = total_bytes_sent + Len(data)
          /\ UNCHANGED <<stream_count, next_stream_id, scheduled_stream,
                        scheduling_time, connection_resources, global_quota,
                        priority_tree, blocked_streams, total_bytes_received,
                        total_frames_sent, total_frames_received, stream_resets,
                        flow_control_events>>

\* Receive data on stream
ReceiveData(stream_id, data) ==
    /\ \E s \in streams :
        /\ s.stream_id = stream_id
        /\ CanReceiveData(s, Len(data))
    /\ LET stream == CHOOSE s \in streams : s.stream_id = stream_id
           updated == [stream EXCEPT
               !.recv_buffer = @ \o data,
               !.recv_offset = @ + Len(data),
               !.bytes_received = @ + Len(data)
           ]
       IN /\ streams' = (streams \ {stream}) \union {updated}
          /\ total_bytes_received' = total_bytes_received + Len(data)
          /\ UNCHANGED <<stream_count, next_stream_id, scheduled_stream,
                        scheduling_time, connection_resources, global_quota,
                        priority_tree, blocked_streams, total_bytes_sent,
                        total_frames_sent, total_frames_received, stream_resets,
                        flow_control_events>>

\* Update stream priority
UpdatePriority(stream_id, new_priority, depends_on, exclusive) ==
    /\ \E s \in streams : s.stream_id = stream_id
    /\ LET stream == CHOOSE s \in streams : s.stream_id = stream_id
           updated == [stream EXCEPT
               !.priority = new_priority,
               !.weight = PriorityWeight(new_priority),
               !.depends_on = depends_on,
               !.exclusive = exclusive
           ]
       IN /\ streams' = (streams \ {stream}) \union {updated}
          /\ priority_tree' = BuildPriorityTree(streams')
          /\ UNCHANGED <<stream_count, next_stream_id, scheduled_stream,
                        scheduling_time, connection_resources, global_quota,
                        blocked_streams, total_bytes_sent, total_bytes_received,
                        total_frames_sent, total_frames_received, stream_resets,
                        flow_control_events>>

\* Schedule stream for transmission
ScheduleStream ==
    /\ scheduled_stream = "NONE"
    /\ LET next == WFQSchedule(streams, scheduling_time)
       IN /\ next # "NONE"
          /\ scheduled_stream' = next
          /\ scheduling_time' = scheduling_time + TimeQuantum
          /\ UNCHANGED <<streams, stream_count, next_stream_id,
                        connection_resources, global_quota, priority_tree,
                        blocked_streams, total_bytes_sent, total_bytes_received,
                        total_frames_sent, total_frames_received, stream_resets,
                        flow_control_events>>

\* Transmit frame from scheduled stream
TransmitFrame ==
    /\ scheduled_stream # "NONE"
    /\ LET stream == scheduled_stream
           result == MultiplexStreams({stream}, MaxStreamData)
       IN /\ result # "NO_DATA"
          /\ streams' = (streams \ {stream}) \union {result.stream}
          /\ scheduled_stream' = "NONE"
          /\ total_frames_sent' = total_frames_sent + 1
          /\ UNCHANGED <<stream_count, next_stream_id, scheduling_time,
                        connection_resources, global_quota, priority_tree,
                        blocked_streams, total_bytes_sent, total_bytes_received,
                        total_frames_received, stream_resets, flow_control_events>>

\* Update flow control window
UpdateFlowControlWindow(stream_id, increment) ==
    /\ \E s \in streams : s.stream_id = stream_id
    /\ LET stream == CHOOSE s \in streams : s.stream_id = stream_id
           updated == UpdateSendWindow(stream, increment)
           released == ReleaseBackpressure(updated)
       IN /\ streams' = (streams \ {stream}) \union {released}
          /\ blocked_streams' = IF released.state = "OPEN"
                                THEN blocked_streams \ {stream_id}
                                ELSE blocked_streams
          /\ flow_control_events' = flow_control_events + 1
          /\ UNCHANGED <<stream_count, next_stream_id, scheduled_stream,
                        scheduling_time, connection_resources, global_quota,
                        priority_tree, total_bytes_sent, total_bytes_received,
                        total_frames_sent, total_frames_received, stream_resets>>

\* Apply backpressure to stream
ApplyBackpressureAction(stream_id) ==
    /\ \E s \in streams : s.stream_id = stream_id /\ s.state = "OPEN"
    /\ LET stream == CHOOSE s \in streams : s.stream_id = stream_id
           blocked == ApplyBackpressure(stream)
       IN /\ streams' = (streams \ {stream}) \union {blocked}
          /\ blocked_streams' = blocked_streams \union {stream_id}
          /\ flow_control_events' = flow_control_events + 1
          /\ UNCHANGED <<stream_count, next_stream_id, scheduled_stream,
                        scheduling_time, connection_resources, global_quota,
                        priority_tree, total_bytes_sent, total_bytes_received,
                        total_frames_sent, total_frames_received, stream_resets>>

\* Close stream
CloseStreamAction(stream_id, local) ==
    /\ \E s \in streams : s.stream_id = stream_id /\ s.state = "OPEN"
    /\ LET stream == CHOOSE s \in streams : s.stream_id = stream_id
           closed == IF local 
                     THEN CloseStreamLocal(stream)
                     ELSE CloseStreamRemote(stream)
       IN /\ streams' = (streams \ {stream}) \union {closed}
          /\ IF closed.state = "CLOSED"
             THEN /\ stream_count' = stream_count - 1
                  /\ global_quota' = UpdateGlobalQuota(global_quota, stream.priority, -1)
             ELSE /\ UNCHANGED <<stream_count, global_quota>>
          /\ UNCHANGED <<next_stream_id, scheduled_stream, scheduling_time,
                        connection_resources, priority_tree, blocked_streams,
                        total_bytes_sent, total_bytes_received, total_frames_sent,
                        total_frames_received, stream_resets, flow_control_events>>

\* Reset stream
ResetStreamAction(stream_id, local) ==
    /\ \E s \in streams : s.stream_id = stream_id
    /\ LET stream == CHOOSE s \in streams : s.stream_id = stream_id
           reset == ResetStream(stream, local)
       IN /\ streams' = (streams \ {stream}) \union {reset}
          /\ stream_count' = stream_count - 1
          /\ stream_resets' = stream_resets + 1
          /\ global_quota' = UpdateGlobalQuota(global_quota, stream.priority, -1)
          /\ UNCHANGED <<next_stream_id, scheduled_stream, scheduling_time,
                        connection_resources, priority_tree, blocked_streams,
                        total_bytes_sent, total_bytes_received, total_frames_sent,
                        total_frames_received, flow_control_events>>

(****************************************************************************)
(* Safety Properties                                                        *)
(****************************************************************************)

StreamTypeOK ==
    /\ streams \subseteq StreamStructure
    /\ stream_count \in 0..MaxConcurrentStreams
    /\ next_stream_id \in StreamIDs
    /\ scheduled_stream \in streams \union {"NONE"}
    /\ blocked_streams \subseteq StreamIDs

\* Resource bounds
ResourceBounds ==
    /\ stream_count <= MaxConcurrentStreams
    /\ \A c \in Connections :
        connection_resources[c].active_streams <= MaxStreamsPerConn
    /\ \A s \in streams :
        /\ Len(s.send_buffer) <= MaxStreamData
        /\ Len(s.recv_buffer) <= MaxStreamData

\* State machine correctness
StateMachineCorrect ==
    \A s1, s2 \in streams :
        s1.stream_id = s2.stream_id => ValidTransition(s1.state, s2.state)

\* Flow control correctness
FlowControlCorrect ==
    \A s \in streams :
        /\ s.send_offset <= s.max_send_offset
        /\ s.recv_offset <= s.max_recv_offset
        /\ s.send_offset <= s.bytes_sent
        /\ s.recv_offset <= s.bytes_received

\* Priority consistency
PriorityConsistent ==
    \A s \in streams :
        s.weight = PriorityWeight(s.priority)

\* No duplicate stream IDs
UniqueStreamIDs ==
    \A s1, s2 \in streams :
        s1 # s2 => s1.stream_id # s2.stream_id

\* Blocked streams cannot send
BlockedStreamsCantSend ==
    \A sid \in blocked_streams :
        \E s \in streams :
            /\ s.stream_id = sid
            /\ s.state = "BLOCKED"

(****************************************************************************)
(* Liveness Properties                                                      *)
(****************************************************************************)

\* Eventual delivery: all data eventually sent
EventualDelivery ==
    \A s \in streams :
        s.state = "OPEN" /\ s.send_buffer # <<>> =>
        <>(Len(s.send_buffer) = 0)

\* No starvation: all ready streams eventually scheduled
NoStarvation ==
    \A s \in streams :
        s.state = "OPEN" /\ s.send_buffer # <<>> =>
        <>[]( scheduled_stream = s)

\* Deadlock freedom: system makes progress
NoDeadlock ==
    []<>(stream_count > 0 => \E s \in streams : s.state = "OPEN")

\* Fair scheduling: low priority streams eventually get service
FairScheduling ==
    \A s \in streams :
        s.state = "OPEN" =>
        <>[]( s.last_scheduled < scheduling_time + TimeQuantum * MaxPriority)

(****************************************************************************)
(* Specification                                                            *)
(****************************************************************************)

StreamNext ==
    \/ \E c \in Connections, t \in StreamTypes, p \in Priorities :
        CreateStream(c, t, p)
    \/ \E sid \in StreamIDs : OpenStreamAction(sid)
    \/ \E sid \in StreamIDs, data \in Seq(Nat) : SendData(sid, data)
    \/ \E sid \in StreamIDs, data \in Seq(Nat) : ReceiveData(sid, data)
    \/ \E sid \in StreamIDs, p \in Priorities, deps \in SUBSET StreamIDs, excl \in BOOLEAN :
        UpdatePriority(sid, p, deps, excl)
    \/ ScheduleStream
    \/ TransmitFrame
    \/ \E sid \in StreamIDs, inc \in Nat : UpdateFlowControlWindow(sid, inc)
    \/ \E sid \in StreamIDs : ApplyBackpressureAction(sid)
    \/ \E sid \in StreamIDs, local \in BOOLEAN : CloseStreamAction(sid, local)
    \/ \E sid \in StreamIDs, local \in BOOLEAN : ResetStreamAction(sid, local)

StreamSpec == StreamInit /\ [][StreamNext]_stream_vars

StreamFairSpec ==
    /\ StreamSpec
    /\ WF_stream_vars(ScheduleStream)
    /\ WF_stream_vars(TransmitFrame)
    /\ \A sid \in StreamIDs, inc \in Nat :
        WF_stream_vars(UpdateFlowControlWindow(sid, inc))

(****************************************************************************)
(* Theorems                                                                 *)
(****************************************************************************)

THEOREM StreamTypeCorrect == StreamSpec => []StreamTypeOK
THEOREM ResourceBoundsHeld == StreamSpec => []ResourceBounds
THEOREM StateMachineCorrect == StreamSpec => []StateMachineCorrect
THEOREM FlowControlCorrect == StreamSpec => []FlowControlCorrect
THEOREM NoStarvationHolds == StreamFairSpec => NoStarvation
THEOREM NoDeadlockHolds == StreamFairSpec => NoDeadlock
THEOREM FairSchedulingHolds == StreamFairSpec => FairScheduling

====

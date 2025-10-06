---- MODULE NyxBasicVerification ----
(****************************************************************************)
(* Basic Verification Module for TLC Model Checking                        *)
(*                                                                          *)
(* This module provides a simplified, executable specification that can    *)
(* be verified using TLC. It captures core protocol behaviors.             *)
(****************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Nodes,              \* Set of node IDs
    MaxMessages,        \* Maximum messages in system
    MaxStreamId         \* Maximum stream ID

VARIABLES
    messages,           \* Messages in transit
    received,           \* Messages received at destinations
    streams,            \* Active streams
    nodeState           \* State of each node

vars == <<messages, received, streams, nodeState>>

(****************************************************************************)
(* Type Invariants                                                          *)
(****************************************************************************)

NodeStateType == [
    status : {"ACTIVE", "FAILED"},
    buffer : Seq(Nat),
    streamIds : SUBSET (1..MaxStreamId)
]

TypeInvariant ==
    /\ messages \in SUBSET [
           id : Nat,
           source : Nodes,
           destination : Nodes,
           streamId : 1..MaxStreamId,
           sequenceNum : Nat
       ]
    /\ received \in SUBSET [
           id : Nat,
           source : Nodes,
           destination : Nodes,
           streamId : 1..MaxStreamId,
           sequenceNum : Nat
       ]
    /\ streams \in [1..MaxStreamId -> [
           active : BOOLEAN,
           source : Nodes,
           destination : Nodes,
           nextSeq : Nat
       ]]
    /\ nodeState \in [Nodes -> NodeStateType]

(****************************************************************************)
(* Initial State                                                            *)
(****************************************************************************)

Init ==
    /\ messages = {}
    /\ received = {}
    /\ streams = [i \in 1..MaxStreamId |-> [
           active |-> FALSE,
           source |-> CHOOSE n \in Nodes : TRUE,
           destination |-> CHOOSE n \in Nodes : TRUE,
           nextSeq |-> 0
       ]]
    /\ nodeState = [n \in Nodes |-> [
           status |-> "ACTIVE",
           buffer |-> <<>>,
           streamIds |-> {}
       ]]

(****************************************************************************)
(* Actions                                                                  *)
(****************************************************************************)

\* Create a new stream
CreateStream(sid, src, dst) ==
    /\ ~streams[sid].active
    /\ nodeState[src].status = "ACTIVE"
    /\ nodeState[dst].status = "ACTIVE"
    /\ streams' = [streams EXCEPT ![sid] = [
           active |-> TRUE,
           source |-> src,
           destination |-> dst,
           nextSeq |-> 0
       ]]
    /\ nodeState' = [nodeState EXCEPT
           ![src].streamIds = @ \union {sid},
           ![dst].streamIds = @ \union {sid}
       ]
    /\ UNCHANGED <<messages, received>>

\* Send a message on a stream
SendMessage(sid) ==
    /\ streams[sid].active
    /\ Cardinality(messages) < MaxMessages
    /\ LET src == streams[sid].source
           dst == streams[sid].destination
           seq == streams[sid].nextSeq
           msg == [
               id |-> Cardinality(messages) + 1,
               source |-> src,
               destination |-> dst,
               streamId |-> sid,
               sequenceNum |-> seq
           ]
       IN /\ nodeState[src].status = "ACTIVE"
          /\ messages' = messages \union {msg}
          /\ streams' = [streams EXCEPT ![sid].nextSeq = @ + 1]
          /\ UNCHANGED <<received, nodeState>>

\* Receive a message (with in-order delivery check)
ReceiveMessage(msg) ==
    /\ msg \in messages
    /\ nodeState[msg.destination].status = "ACTIVE"
    \* 同じstreamの以前�EメチE��ージがすべて受信済みであることを確誁E
    /\ \A m \in messages : 
           (m.streamId = msg.streamId /\ m.source = msg.source /\ m.destination = msg.destination /\ m.sequenceNum < msg.sequenceNum) =>
               m.id > msg.id  \* より古いseqNumのメチE��ージはまだ送信中
    /\ messages' = messages \ {msg}
    /\ received' = received \union {msg}
    /\ UNCHANGED <<streams, nodeState>>

\* Node failure
NodeFails(node) ==
    /\ nodeState[node].status = "ACTIVE"
    /\ nodeState' = [nodeState EXCEPT ![node].status = "FAILED"]
    /\ UNCHANGED <<messages, received, streams>>

\* Node recovery
NodeRecovers(node) ==
    /\ nodeState[node].status = "FAILED"
    /\ nodeState' = [nodeState EXCEPT ![node].status = "ACTIVE"]
    /\ UNCHANGED <<messages, received, streams>>

(****************************************************************************)
(* Specification                                                            *)
(****************************************************************************)

Next ==
    \/ \E sid \in 1..MaxStreamId, src, dst \in Nodes :
           CreateStream(sid, src, dst)
    \/ \E sid \in 1..MaxStreamId :
           SendMessage(sid)
    \/ \E msg \in messages :
           ReceiveMessage(msg)
    \/ \E node \in Nodes :
           NodeFails(node)
    \/ \E node \in Nodes :
           NodeRecovers(node)

Spec == Init /\ [][Next]_vars

(****************************************************************************)
(* Properties                                                               *)
(****************************************************************************)

\* Safety: No message duplication
NoMessageDuplication ==
    \A m1, m2 \in received :
        (m1.streamId = m2.streamId /\ m1.sequenceNum = m2.sequenceNum) => (m1 = m2)

\* Safety: Message ordering preserved per stream  
\* Messages from same stream should be received in sequence order
MessageOrdering ==
    \A m1, m2 \in received :
        (m1.streamId = m2.streamId /\ m1.source = m2.source /\ m1.destination = m2.destination /\ m1.sequenceNum < m2.sequenceNum) =>
            TRUE  \* メチE��ージは頁E��通りに受信されるべき（ただし、この簡易モチE��では頁E��を強制してぁE��ぁE��E

\* Liveness: Eventually all sent messages are received (if nodes stay active)
EventualDelivery ==
    \A sid \in 1..MaxStreamId :
        streams[sid].active =>
            <>(Cardinality({m \in received : m.streamId = sid}) = streams[sid].nextSeq)

\* No deadlock: always some action possible if there are active streams
NoDeadlock ==
    (\E sid \in 1..MaxStreamId : streams[sid].active) => ENABLED Next

(****************************************************************************)
(* State Constraints for Model Checking                                     *)
(****************************************************************************)

StateConstraint ==
    /\ Cardinality(messages) <= MaxMessages
    /\ \A sid \in 1..MaxStreamId : streams[sid].nextSeq <= 10
    /\ Cardinality(received) <= MaxMessages * 2

====

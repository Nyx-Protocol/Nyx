---- MODULE NyxConcurrencyModels ----
LOCAL INSTANCE NyxHelpers
(****************************************************************************)
(* Nyx Protocol - Concurrency and Parallelism Models                       *)
(*                                                                          *)
(* This module provides comprehensive models for concurrent operations,    *)
(* race condition analysis, synchronization primitives, and parallel       *)
(* processing patterns in the Nyx protocol.                                *)
(*                                                                          *)
(* Concurrency Aspects:                                                     *)
(*   - Lock-free data structures                                           *)
(*   - Actor model and message passing                                     *)
(*   - Work stealing and load balancing                                    *)
(*   - Barrier synchronization                                             *)
(*   - Atomic operations and memory ordering                               *)
(*   - Deadlock detection and prevention                                   *)
(****************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, Integers, TLC

(****************************************************************************)
(* Thread and Process Models                                                *)
(****************************************************************************)

\* Thread identifier
ThreadId == Nat

\* Thread states
ThreadState == {"CREATED", "READY", "RUNNING", "BLOCKED", "TERMINATED"}

\* Thread priority levels
ThreadPriority == 0..10

\* Thread descriptor
Thread == [
    id : ThreadId,
    state : ThreadState,
    priority : ThreadPriority,
    stack_size : Nat,
    cpu_affinity : SUBSET Nat,  \* CPU cores
    task_queue : Seq(Task)
]

\* Task definition
Task == [
    id : Nat,
    work : STRING,
    input : Any,
    output : Any,
    dependencies : SUBSET Nat,
    completion_time : Nat
]

\* Process context
ProcessContext == [
    pid : Nat,
    threads : [ThreadId -> Thread],
    shared_memory : [Nat -> Any],
    file_descriptors : SUBSET Nat,
    resource_limits : ResourceLimits
]

\* Resource limits
ResourceLimits == [
    max_threads : Nat,
    max_memory : Nat,
    max_file_descriptors : Nat,
    max_cpu_time : Nat
]

(****************************************************************************)
(* Synchronization Primitives                                               *)
(****************************************************************************)

\* Mutex lock
Mutex == [
    locked : BOOLEAN,
    owner : ThreadId,
    waiting_threads : Seq(ThreadId)
]

\* Read-write lock
RWLock == [
    readers : SUBSET ThreadId,
    writer : ThreadId,
    waiting_readers : Seq(ThreadId),
    waiting_writers : Seq(ThreadId)
]

\* Semaphore
Semaphore == [
    count : Int,
    max_count : Nat,
    waiting_threads : Seq(ThreadId)
]

\* Condition variable
ConditionVariable == [
    waiting_threads : Seq(ThreadId),
    associated_mutex : Mutex
]

\* Barrier
Barrier == [
    required_threads : Nat,
    arrived_threads : SUBSET ThreadId,
    generation : Nat
]

\* Atomic variable
AtomicVar == [
    value : Any,
    memory_order : {"RELAXED", "ACQUIRE", "RELEASE", "ACQ_REL", "SEQ_CST"}
]

(****************************************************************************)
(* Lock Operations                                                          *)
(****************************************************************************)

\* Acquire mutex
AcquireMutex(mutex, thread_id) ==
    IF mutex.locked = FALSE
    THEN [mutex EXCEPT !.locked = TRUE, !.owner = thread_id]
    ELSE [mutex EXCEPT !.waiting_threads = Append(@, thread_id)]

\* Release mutex
ReleaseMutex(mutex) ==
    IF mutex.waiting_threads = <<>>
    THEN [mutex EXCEPT !.locked = FALSE, !.owner = 0]
    ELSE LET next_thread == Head(mutex.waiting_threads)
         IN [mutex EXCEPT 
                !.owner = next_thread,
                !.waiting_threads = Tail(@)]

\* Try acquire mutex (non-blocking)
TryAcquireMutex(mutex, thread_id) ==
    IF mutex.locked = FALSE
    THEN [success |-> TRUE, 
          mutex |-> [mutex EXCEPT !.locked = TRUE, !.owner = thread_id]]
    ELSE [success |-> FALSE, mutex |-> mutex]

\* Read lock
AcquireReadLock(rwlock, thread_id) ==
    IF rwlock.writer = 0
    THEN [rwlock EXCEPT !.readers = @ \union {thread_id}]
    ELSE [rwlock EXCEPT !.waiting_readers = Append(@, thread_id)]

\* Write lock
AcquireWriteLock(rwlock, thread_id) ==
    IF rwlock.writer = 0 /\ rwlock.readers = {}
    THEN [rwlock EXCEPT !.writer = thread_id]
    ELSE [rwlock EXCEPT !.waiting_writers = Append(@, thread_id)]

\* Release read lock
ReleaseReadLock(rwlock, thread_id) ==
    LET new_readers == rwlock.readers \ {thread_id}
    IN IF new_readers = {} /\ rwlock.waiting_writers # <<>>
       THEN LET next_writer == Head(rwlock.waiting_writers)
            IN [rwlock EXCEPT 
                   !.readers = {},
                   !.writer = next_writer,
                   !.waiting_writers = Tail(@)]
       ELSE [rwlock EXCEPT !.readers = new_readers]

\* Release write lock
ReleaseWriteLock(rwlock) ==
    IF rwlock.waiting_writers # <<>>
    THEN LET next_writer == Head(rwlock.waiting_writers)
         IN [rwlock EXCEPT 
                !.writer = next_writer,
                !.waiting_writers = Tail(@)]
    ELSE IF rwlock.waiting_readers # <<>>
         THEN [rwlock EXCEPT 
                  !.writer = 0,
                  !.readers = {t : t \in {1..Len(rwlock.waiting_readers)}},
                  !.waiting_readers = <<>>]
         ELSE [rwlock EXCEPT !.writer = 0]

\* Semaphore wait
SemaphoreWait(sem, thread_id) ==
    IF sem.count > 0
    THEN [sem EXCEPT !.count = @ - 1]
    ELSE [sem EXCEPT !.waiting_threads = Append(@, thread_id)]

\* Semaphore signal
SemaphoreSignal(sem) ==
    IF sem.waiting_threads = <<>>
    THEN [sem EXCEPT !.count = Min(@ + 1, sem.max_count)]
    ELSE LET next_thread == Head(sem.waiting_threads)
         IN [sem EXCEPT !.waiting_threads = Tail(@)]

\* Barrier wait
BarrierWait(barrier, thread_id) ==
    LET new_arrived == barrier.arrived_threads \union {thread_id}
    IN IF Cardinality(new_arrived) = barrier.required_threads
       THEN [barrier EXCEPT 
                !.arrived_threads = {},
                !.generation = @ + 1]
       ELSE [barrier EXCEPT !.arrived_threads = new_arrived]

(****************************************************************************)
(* Lock-Free Data Structures                                                *)
(****************************************************************************)

\* Lock-free stack
LockFreeStack == [
    top : Nat,  \* Index
    data : Seq(Any),
    version : Nat  \* ABA problem prevention
]

\* Lock-free stack push
LockFreeStackPush(stack, value) ==
    LET old_top == stack.top
        new_top == old_top + 1
        new_data == Append(stack.data, value)
        new_version == stack.version + 1
    IN [stack EXCEPT 
           !.top = new_top,
           !.data = new_data,
           !.version = new_version]

\* Lock-free stack pop
LockFreeStackPop(stack) ==
    IF stack.top = 0
    THEN [success |-> FALSE, value |-> 0, stack |-> stack]
    ELSE LET old_top == stack.top
             value == stack.data[old_top]
             new_top == old_top - 1
             new_version == stack.version + 1
         IN [success |-> TRUE,
             value |-> value,
             stack |-> [stack EXCEPT 
                           !.top = new_top,
                           !.version = new_version]]

\* Lock-free queue
LockFreeQueue == [
    head : Nat,
    tail : Nat,
    data : [Nat -> Any],
    capacity : Nat,
    version : Nat
]

\* Lock-free queue enqueue
LockFreeQueueEnqueue(queue, value) ==
    LET old_tail == queue.tail
        new_tail == (old_tail + 1) % queue.capacity
    IN IF new_tail = queue.head  \* Queue full
       THEN [success |-> FALSE, queue |-> queue]
       ELSE [success |-> TRUE,
             queue |-> [queue EXCEPT 
                           !.tail = new_tail,
                           !.data[old_tail] = value,
                           !.version = @ + 1]]

\* Lock-free queue dequeue
LockFreeQueueDequeue(queue) ==
    IF queue.head = queue.tail  \* Queue empty
    THEN [success |-> FALSE, value |-> 0, queue |-> queue]
    ELSE LET old_head == queue.head
             value == queue.data[old_head]
             new_head == (old_head + 1) % queue.capacity
         IN [success |-> TRUE,
             value |-> value,
             queue |-> [queue EXCEPT 
                           !.head = new_head,
                           !.version = @ + 1]]

(****************************************************************************)
(* Actor Model                                                               *)
(****************************************************************************)

\* Actor identifier
ActorId == Nat

\* Actor state
Actor == [
    id : ActorId,
    state : Any,
    mailbox : Seq(Message),
    behavior : [Message -> Any]
]

\* Actor message
Message == [
    sender : ActorId,
    receiver : ActorId,
    content : Any,
    timestamp : Nat
]

\* Actor system
ActorSystem == [
    actors : [ActorId -> Actor],
    message_queue : Seq(Message),
    dispatcher_threads : Nat
]

\* Send message to actor
SendMessage(system, sender, receiver, content) ==
    LET msg == [sender |-> sender,
                receiver |-> receiver,
                content |-> content,
                timestamp |-> SystemTime]
    IN [system EXCEPT 
           !.actors[receiver].mailbox = Append(@, msg)]

\* Process actor message
ProcessActorMessage(actor) ==
    IF actor.mailbox = <<>>
    THEN actor
    ELSE LET msg == Head(actor.mailbox)
             new_state == actor.behavior[msg]
         IN [actor EXCEPT 
                !.state = new_state,
                !.mailbox = Tail(@)]

(****************************************************************************)
(* Work Stealing                                                             *)
(****************************************************************************)

\* Work stealing deque
WorkStealingDeque == [
    owner : ThreadId,
    tasks : Seq(Task),
    top : Nat,    \* Owner side
    bottom : Nat  \* Stealer side
]

\* Push task (owner side)
PushTask(deque, task) ==
    [deque EXCEPT 
        !.tasks = Append(@, task),
        !.top = @ + 1]

\* Pop task (owner side)
PopTask(deque) ==
    IF deque.top <= deque.bottom
    THEN [success |-> FALSE, task |-> 0, deque |-> deque]
    ELSE LET new_top == deque.top - 1
             task == deque.tasks[new_top]
         IN [success |-> TRUE,
             task |-> task,
             deque |-> [deque EXCEPT !.top = new_top]]

\* Steal task (thief side)
StealTask(deque) ==
    IF deque.bottom >= deque.top
    THEN [success |-> FALSE, task |-> 0, deque |-> deque]
    ELSE LET old_bottom == deque.bottom
             task == deque.tasks[old_bottom]
             new_bottom == old_bottom + 1
         IN [success |-> TRUE,
             task |-> task,
             deque |-> [deque EXCEPT !.bottom = new_bottom]]

\* Work stealing scheduler
WorkStealingScheduler == [
    thread_count : Nat,
    deques : [ThreadId -> WorkStealingDeque],
    global_queue : Seq(Task)
]

\* Schedule task
ScheduleTask(scheduler, thread_id, task) ==
    [scheduler EXCEPT 
        !.deques[thread_id] = PushTask(@, task)]

\* Balance load across threads
BalanceLoad(scheduler) ==
    LET avg_load == CHOOSE l : l = 
            (CHOOSE sum : sum = Sum({Len(scheduler.deques[t].tasks) : 
                                     t \in DOMAIN scheduler.deques})) / scheduler.thread_count
        overloaded == {t \in DOMAIN scheduler.deques : 
                       Len(scheduler.deques[t].tasks) > (avg_load * 12) \div 10}
        underloaded == {t \in DOMAIN scheduler.deques :
                        Len(scheduler.deques[t].tasks) < (avg_load * 8) \div 10}
    IN scheduler  \* Simplified load balancing

(****************************************************************************)
(* Parallel Patterns                                                        *)
(****************************************************************************)

\* Map-Reduce pattern
MapReduce(data, map_fn, reduce_fn, num_threads) ==
    LET chunk_size == Len(data) \div num_threads
        chunks == [i \in 1..num_threads |->
                   SubSeq(data, (i-1) * chunk_size + 1,
                          IF i = num_threads 
                          THEN Len(data) 
                          ELSE i * chunk_size)]
        mapped == [i \in 1..num_threads |->
                   [j \in DOMAIN chunks[i] |-> map_fn[chunks[i][j]]]]
        reduced == CHOOSE r : r = FoldSeq(reduce_fn, 0, 
                                          CHOOSE s : s = ConcatSeqs(mapped))
    IN reduced

\* Pipeline pattern
Pipeline == [
    stages : Seq([
        stage_id : Nat,
        function : [Any -> Any],
        input_queue : Seq(Any),
        output_queue : Seq(Any),
        thread_id : ThreadId
    ])
]

\* Execute pipeline stage
ExecutePipelineStage(stage) ==
    IF stage.input_queue = <<>>
    THEN stage
    ELSE LET input == Head(stage.input_queue)
             output == stage.function[input]
         IN [stage EXCEPT 
                !.input_queue = Tail(@),
                !.output_queue = Append(@, output)]

\* Fork-Join pattern
ForkJoin(tasks, join_function) ==
    LET results == {ExecuteTask(t) : t \in tasks}
    IN join_function[results]

(****************************************************************************)
(* Deadlock Detection                                                       *)
(****************************************************************************)

\* Resource allocation graph
ResourceGraph == [
    threads : SUBSET ThreadId,
    resources : SUBSET Nat,
    allocation : [ThreadId -> SUBSET Nat],  \* Resources held
    request : [ThreadId -> SUBSET Nat]      \* Resources requested
]

\* Detect cycle in resource graph
DetectDeadlock(graph) ==
    \E cycle \in Seq(ThreadId) :
        /\ Len(cycle) > 1
        /\ \A i \in 1..(Len(cycle)-1) :
             \E r \in Nat :
                /\ r \in graph.allocation[cycle[i]]
                /\ r \in graph.request[cycle[i+1]]
        /\ \E r \in Nat :
             /\ r \in graph.allocation[cycle[Len(cycle)]]
             /\ r \in graph.request[cycle[1]]

\* Wait-for graph
WaitForGraph == [
    nodes : SUBSET ThreadId,
    edges : SUBSET (ThreadId \X ThreadId)
]

\* Build wait-for graph
BuildWaitForGraph(threads, locks) ==
    LET edges == {<<t1, t2>> : t1, t2 \in threads,
                               \E lock \in locks :
                                   /\ lock.owner = t2
                                   /\ t1 \in DOMAIN lock.waiting_threads}
    IN [nodes |-> threads, edges |-> edges]

\* Check for cycle in wait-for graph
HasCycle(graph) ==
    \E path \in Seq(graph.nodes) :
        /\ Len(path) > 1
        /\ \A i \in 1..(Len(path)-1) :
             <<path[i], path[i+1]>> \in graph.edges
        /\ <<path[Len(path)], path[1]>> \in graph.edges

(****************************************************************************)
(* Memory Ordering and Atomics                                              *)
(****************************************************************************)

\* Memory operation
MemoryOp == [
    operation : {"LOAD", "STORE", "RMW"},  \* Read-Modify-Write
    address : Nat,
    value : Any,
    memory_order : {"RELAXED", "ACQUIRE", "RELEASE", "ACQ_REL", "SEQ_CST"},
    thread_id : ThreadId,
    timestamp : Nat
]

\* Memory model state
MemoryModel == [
    memory : [Nat -> Any],
    history : Seq(MemoryOp),
    happens_before : SUBSET (MemoryOp \X MemoryOp),
    synchronizes_with : SUBSET (MemoryOp \X MemoryOp)
]

\* Atomic load
AtomicLoad(mem, address, order, thread_id) ==
    LET op == [operation |-> "LOAD",
               address |-> address,
               value |-> mem.memory[address],
               memory_order |-> order,
               thread_id |-> thread_id,
               timestamp |-> Len(mem.history)]
    IN [value |-> mem.memory[address],
        mem |-> [mem EXCEPT 
                    !.history = Append(@, op)]]

\* Atomic store
AtomicStore(mem, address, value, order, thread_id) ==
    LET op == [operation |-> "STORE",
               address |-> address,
               value |-> value,
               memory_order |-> order,
               thread_id |-> thread_id,
               timestamp |-> Len(mem.history)]
    IN [mem EXCEPT 
           !.memory[address] = value,
           !.history = Append(@, op)]

\* Atomic compare-and-swap
AtomicCAS(mem, address, expected, desired, order, thread_id) ==
    LET current == mem.memory[address]
        success == (current = expected)
        op == [operation |-> "RMW",
               address |-> address,
               value |-> IF success THEN desired ELSE current,
               memory_order |-> order,
               thread_id |-> thread_id,
               timestamp |-> Len(mem.history)]
    IN [success |-> success,
        value |-> current,
        mem |-> IF success
                THEN [mem EXCEPT 
                         !.memory[address] = desired,
                         !.history = Append(@, op)]
                ELSE [mem EXCEPT 
                         !.history = Append(@, op)]]

\* Atomic fetch-and-add
AtomicFetchAdd(mem, address, delta, order, thread_id) ==
    LET current == mem.memory[address]
        new_value == current + delta
        op == [operation |-> "RMW",
               address |-> address,
               value |-> new_value,
               memory_order |-> order,
               thread_id |-> thread_id,
               timestamp |-> Len(mem.history)]
    IN [value |-> current,
        mem |-> [mem EXCEPT 
                    !.memory[address] = new_value,
                    !.history = Append(@, op)]]

(****************************************************************************)
(* Thread Pool                                                               *)
(****************************************************************************)

\* Thread pool
ThreadPool == [
    threads : [ThreadId -> Thread],
    task_queue : Seq(Task),
    active_tasks : [ThreadId -> Task],
    min_threads : Nat,
    max_threads : Nat,
    idle_timeout : Nat
]

\* Submit task to pool
SubmitTask(pool, task) ==
    [pool EXCEPT 
        !.task_queue = Append(@, task)]

\* Worker thread execution
WorkerThreadExecute(pool, thread_id) ==
    IF pool.task_queue = <<>>
    THEN pool  \* Thread idles
    ELSE LET task == Head(pool.task_queue)
         IN [pool EXCEPT 
                !.task_queue = Tail(@),
                !.active_tasks[thread_id] = task]

\* Complete task
CompleteTask(pool, thread_id) ==
    [pool EXCEPT 
        !.active_tasks[thread_id] = 0]

(****************************************************************************)
(* Concurrency Patterns                                                      *)
(****************************************************************************)

\* Producer-Consumer pattern
ProducerConsumer == [
    buffer : Seq(Any),
    capacity : Nat,
    mutex : Mutex,
    not_full : ConditionVariable,
    not_empty : ConditionVariable
]

\* Double-checked locking pattern
DoubleCheckedLocking(shared_var, mutex, init_fn) ==
    IF shared_var # 0  \* First check (no lock)
    THEN shared_var
    ELSE LET locked == AcquireMutex(mutex, CurrentThread)
         IN IF shared_var # 0  \* Second check (with lock)
            THEN LET released == ReleaseMutex(locked)
                 IN shared_var
            ELSE LET initialized == init_fn[]
                     released == ReleaseMutex(locked)
                 IN initialized

\* Read-Copy-Update pattern
RCU == [
    data : Any,
    readers : SUBSET ThreadId,
    grace_period : Nat
]

\* RCU read
RCURead(rcu, thread_id) ==
    [rcu EXCEPT 
        !.readers = @ \union {thread_id}]

\* RCU update
RCUUpdate(rcu, new_data) ==
    [rcu EXCEPT 
        !.data = new_data,
        !.grace_period = @ + 1]

====

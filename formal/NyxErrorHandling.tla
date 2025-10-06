---- MODULE NyxErrorHandling ----
(****************************************************************************)
(* Nyx Protocol - Comprehensive Error Handling and Recovery                *)
(*                                                                          *)
(* This module provides formal specifications for error detection,         *)
(* classification, recovery strategies, and fault injection testing.       *)
(*                                                                          *)
(* Error Handling Components:                                               *)
(*   - Error taxonomy and classification                                   *)
(*   - Error detection mechanisms                                          *)
(*   - Error recovery strategies                                           *)
(*   - Retry policies and exponential backoff                              *)
(*   - Error propagation and containment                                   *)
(*   - Graceful degradation strategies                                     *)
(*   - Fault injection testing                                             *)
(*   - Error logging and diagnostics                                       *)
(****************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, Integers, TLC,
        NyxNetworkLayer, NyxStreamManagement, NyxFaultTolerance

(****************************************************************************)
(* Error Classification                                                     *)
(****************************************************************************)

\* Error severity levels
ErrorSeverity == {
    "DEBUG",          \* Development/debugging information
    "INFO",           \* Informational messages
    "WARNING",        \* Warning conditions
    "ERROR",          \* Error conditions
    "CRITICAL",       \* Critical conditions
    "FATAL"           \* Fatal errors requiring restart
}

\* Error categories
ErrorCategory == {
    "NETWORK_ERROR",       \* Network connectivity issues
    "PROTOCOL_ERROR",      \* Protocol violations
    "CRYPTO_ERROR",        \* Cryptographic failures
    "RESOURCE_ERROR",      \* Resource exhaustion
    "TIMEOUT_ERROR",       \* Operation timeouts
    "AUTHENTICATION_ERROR",\* Authentication failures
    "AUTHORIZATION_ERROR", \* Authorization failures
    "DATA_ERROR",          \* Data corruption/validation
    "CONFIGURATION_ERROR", \* Configuration problems
    "INTERNAL_ERROR",      \* Internal logic errors
    "EXTERNAL_ERROR"       \* External system errors
}

\* Error subcategories
NetworkErrorType == {
    "CONNECTION_REFUSED",
    "CONNECTION_RESET",
    "CONNECTION_TIMEOUT",
    "DNS_RESOLUTION_FAILED",
    "HOST_UNREACHABLE",
    "NETWORK_UNREACHABLE",
    "PACKET_LOSS",
    "PATH_MTU_EXCEEDED"
}

ProtocolErrorType == {
    "INVALID_MESSAGE_FORMAT",
    "UNEXPECTED_MESSAGE_TYPE",
    "PROTOCOL_VERSION_MISMATCH",
    "SEQUENCE_NUMBER_ERROR",
    "CHECKSUM_MISMATCH",
    "FLOW_CONTROL_VIOLATION",
    "CONGESTION_COLLAPSE",
    "DUPLICATE_MESSAGE"
}

CryptoErrorType == {
    "KEY_EXCHANGE_FAILED",
    "ENCRYPTION_FAILED",
    "DECRYPTION_FAILED",
    "SIGNATURE_VERIFICATION_FAILED",
    "CERTIFICATE_INVALID",
    "CERTIFICATE_EXPIRED",
    "NONCE_REUSE",
    "AUTHENTICATION_TAG_MISMATCH"
}

ResourceErrorType == {
    "OUT_OF_MEMORY",
    "OUT_OF_DISK_SPACE",
    "FILE_DESCRIPTOR_LIMIT",
    "THREAD_POOL_EXHAUSTED",
    "BUFFER_OVERFLOW",
    "QUEUE_FULL",
    "BANDWIDTH_EXCEEDED",
    "CONNECTION_LIMIT_REACHED"
}

(****************************************************************************)
(* Error Descriptor                                                         *)
(****************************************************************************)

\* Comprehensive error descriptor
Error == [
    error_id : Nat,
    timestamp : Nat,
    severity : ErrorSeverity,
    category : ErrorCategory,
    subcategory : STRING,
    message : STRING,
    source_component : STRING,
    source_node : Node,
    affected_nodes : SUBSET Node,
    affected_streams : SUBSET Nat,
    stack_trace : Seq(STRING),
    context : [STRING -> Any],
    retryable : BOOLEAN,
    recoverable : BOOLEAN,
    recovery_actions : Seq(STRING)
]

\* Error event
ErrorEvent == [
    error : Error,
    detection_time : Nat,
    detection_method : STRING,
    propagation_path : Seq(Node)
]

\* Error statistics
ErrorStatistics == [
    total_errors : Nat,
    errors_by_severity : [ErrorSeverity -> Nat],
    errors_by_category : [ErrorCategory -> Nat],
    errors_per_component : [STRING -> Nat],
    mean_time_between_errors : Nat,
    error_rate : Nat,  \* Errors per time unit
    recovery_success_rate : 0..100
]

(****************************************************************************)
(* Error Detection                                                          *)
(****************************************************************************)

\* Error detector
ErrorDetector == [
    detection_rules : Seq([
        condition : [STATE -> BOOLEAN],
        error_type : ErrorCategory,
        severity : ErrorSeverity,
        action : STRING
    ]),
    monitored_metrics : [STRING -> Nat],
    thresholds : [STRING -> Nat],
    detection_history : Seq(ErrorEvent)
]

\* Detect error from system state
DetectError(detector, system_state) ==
    LET triggered_rules == {r \in DOMAIN detector.detection_rules :
                            detector.detection_rules[r].condition[system_state]}
    IN IF triggered_rules = {}
       THEN [error_detected |-> FALSE, errors |-> <<>>]
       ELSE [error_detected |-> TRUE,
             errors |-> [r \in triggered_rules |->
                 CreateError(detector.detection_rules[r], system_state)]]

\* Create error descriptor
CreateError(rule, system_state) ==
    [
        error_id |-> NextErrorId,
        timestamp |-> CurrentTime,
        severity |-> rule.severity,
        category |-> rule.error_type,
        subcategory |-> "",
        message |-> rule.action,
        source_component |-> "ErrorDetector",
        source_node |-> CurrentNode,
        affected_nodes |-> {},
        affected_streams |-> {},
        stack_trace |-> <<>>,
        context |-> [state |-> system_state],
        retryable |-> DetermineRetryable(rule.error_type),
        recoverable |-> DetermineRecoverable(rule.error_type),
        recovery_actions |-> DetermineRecoveryActions(rule.error_type)
    ]

\* Determine if error is retryable
DetermineRetryable(error_type) ==
    error_type \in {
        "NETWORK_ERROR",
        "TIMEOUT_ERROR",
        "RESOURCE_ERROR"
    }

\* Determine if error is recoverable
DetermineRecoverable(error_type) ==
    error_type \notin {
        "FATAL",
        "CONFIGURATION_ERROR"
    }

\* Determine recovery actions
DetermineRecoveryActions(error_type) ==
    CASE error_type = "NETWORK_ERROR" ->
           <<"retry_connection", "switch_path", "use_backup">>
      [] error_type = "TIMEOUT_ERROR" ->
           <<"retry_operation", "increase_timeout", "check_connectivity">>
      [] error_type = "RESOURCE_ERROR" ->
           <<"free_resources", "scale_up", "throttle_requests">>
      [] error_type = "CRYPTO_ERROR" ->
           <<"renegotiate_keys", "verify_certificates", "rollback_crypto">>
      [] error_type = "PROTOCOL_ERROR" ->
           <<"reset_connection", "resync_state", "fallback_protocol">>
      [] OTHER ->
           <<"log_error", "alert_operator", "restart_component">>

(****************************************************************************)
(* Error Recovery Strategies                                                *)
(****************************************************************************)

\* Recovery strategy
RecoveryStrategy == {
    "RETRY",              \* Retry the operation
    "FALLBACK",           \* Use fallback mechanism
    "FAILOVER",           \* Switch to backup
    "CIRCUIT_BREAKER",    \* Open circuit breaker
    "GRACEFUL_DEGRADATION", \* Reduce functionality
    "ISOLATION",          \* Isolate faulty component
    "RESTART",            \* Restart component
    "ROLLBACK",           \* Rollback to previous state
    "IGNORE"              \* Log and continue
}

\* Recovery action
RecoveryAction == [
    strategy : RecoveryStrategy,
    error : Error,
    attempts : Nat,
    max_attempts : Nat,
    backoff_policy : STRING,
    timeout : Nat,
    fallback_available : BOOLEAN,
    success : BOOLEAN
]

\* Execute recovery action
ExecuteRecovery(action, system_state) ==
    CASE action.strategy = "RETRY" ->
           RetryOperation(action, system_state)
      [] action.strategy = "FALLBACK" ->
           UseFallback(action, system_state)
      [] action.strategy = "FAILOVER" ->
           PerformFailover(action, system_state)
      [] action.strategy = "CIRCUIT_BREAKER" ->
           OpenCircuitBreaker(action, system_state)
      [] action.strategy = "GRACEFUL_DEGRADATION" ->
           DegradeService(action, system_state)
      [] action.strategy = "ISOLATION" ->
           IsolateComponent(action, system_state)
      [] action.strategy = "RESTART" ->
           RestartComponent(action, system_state)
      [] action.strategy = "ROLLBACK" ->
           RollbackState(action, system_state)
      [] action.strategy = "IGNORE" ->
           LogAndContinue(action, system_state)
      [] OTHER ->
           system_state

\* Retry operation with backoff
RetryOperation(action, system_state) ==
    IF action.attempts < action.max_attempts
    THEN LET backoff_time == ComputeBackoff(action.backoff_policy, action.attempts)
         IN [system_state EXCEPT
                !.retry_scheduled = TRUE,
                !.retry_time = CurrentTime + backoff_time,
                !.retry_action = action]
    ELSE [system_state EXCEPT
             !.recovery_failed = TRUE,
             !.failed_action = action]

\* Compute backoff time
ComputeBackoff(policy, attempt) ==
    CASE policy = "LINEAR" ->
           attempt * 1000  \* Linear backoff: 1s, 2s, 3s, ...
      [] policy = "EXPONENTIAL" ->
           (2 ^ attempt) * 1000  \* Exponential: 2s, 4s, 8s, 16s, ...
      [] policy = "FIBONACCI" ->
           Fibonacci(attempt) * 1000
      [] policy = "DECORRELATED_JITTER" ->
           RandomInt(1000, attempt * 3000)
      [] OTHER ->
           1000

\* Use fallback mechanism
UseFallback(action, system_state) ==
    IF action.fallback_available
    THEN [system_state EXCEPT
             !.fallback_active = TRUE,
             !.primary_failed = TRUE]
    ELSE ExecuteRecovery([action EXCEPT !.strategy = "FAILOVER"], system_state)

\* Perform failover
PerformFailover(action, system_state) ==
    [system_state EXCEPT
        !.active_path = BackupPath,
        !.failover_time = CurrentTime]

\* Open circuit breaker
OpenCircuitBreaker(action, system_state) ==
    [system_state EXCEPT
        !.circuit_breaker_state = "OPEN",
        !.circuit_breaker_open_time = CurrentTime]

\* Degrade service
DegradeService(action, system_state) ==
    [system_state EXCEPT
        !.service_level = "DEGRADED",
        !.reduced_capacity = TRUE]

\* Isolate faulty component
IsolateComponent(action, system_state) ==
    [system_state EXCEPT
        !.isolated_components = @ \union {action.error.source_component}]

\* Restart component
RestartComponent(action, system_state) ==
    [system_state EXCEPT
        !.component_state[action.error.source_component] = "RESTARTING"]

\* Rollback to previous state
RollbackState(action, system_state) ==
    [system_state EXCEPT
        !.current_state = LastCheckpoint,
        !.rollback_time = CurrentTime]

\* Log error and continue
LogAndContinue(action, system_state) ==
    [system_state EXCEPT
        !.error_log = Append(@, action.error)]

(****************************************************************************)
(* Retry Policies                                                           *)
(****************************************************************************)

\* Retry policy configuration
RetryPolicy == [
    policy_name : STRING,
    max_attempts : Nat,
    initial_delay : Nat,
    max_delay : Nat,
    backoff_multiplier : Nat,
    jitter : BOOLEAN,
    retry_on_errors : SUBSET ErrorCategory,
    timeout : Nat
]

\* Standard retry policies
ExponentialBackoffPolicy ==
    [
        policy_name |-> "ExponentialBackoff",
        max_attempts |-> 5,
        initial_delay |-> 1000,
        max_delay |-> 60000,
        backoff_multiplier |-> 2,
        jitter |-> TRUE,
        retry_on_errors |-> {"NETWORK_ERROR", "TIMEOUT_ERROR"},
        timeout |-> 300000
    ]

LinearBackoffPolicy ==
    [
        policy_name |-> "LinearBackoff",
        max_attempts |-> 3,
        initial_delay |-> 1000,
        max_delay |-> 10000,
        backoff_multiplier |-> 1,
        jitter |-> FALSE,
        retry_on_errors |-> {"NETWORK_ERROR"},
        timeout |-> 60000
    ]

ImmediateRetryPolicy ==
    [
        policy_name |-> "ImmediateRetry",
        max_attempts |-> 10,
        initial_delay |-> 0,
        max_delay |-> 0,
        backoff_multiplier |-> 1,
        jitter |-> FALSE,
        retry_on_errors |-> {"RESOURCE_ERROR"},
        timeout |-> 10000
    ]

\* Compute next retry delay
NextRetryDelay(policy, attempt) ==
    LET base_delay == Min(policy.initial_delay * (policy.backoff_multiplier ^ attempt),
                          policy.max_delay)
        jitter_amount == IF policy.jitter
                        THEN RandomInt(-base_delay \div 10, base_delay \div 10)
                        ELSE 0
    IN Max(0, base_delay + jitter_amount)

\* Should retry error
ShouldRetry(policy, error, attempt) ==
    /\ attempt < policy.max_attempts
    /\ error.category \in policy.retry_on_errors
    /\ error.retryable = TRUE
    /\ (CurrentTime - error.timestamp) < policy.timeout

(****************************************************************************)
(* Error Propagation                                                        *)
(****************************************************************************)

\* Error propagation mode
PropagationMode == {
    "IMMEDIATE",      \* Propagate immediately
    "BUFFERED",       \* Buffer and batch
    "FILTERED",       \* Filter based on rules
    "SUPPRESSED"      \* Suppress propagation
}

\* Error propagation rules
PropagationRule == [
    error_categories : SUBSET ErrorCategory,
    min_severity : ErrorSeverity,
    propagation_mode : PropagationMode,
    destinations : SUBSET Node,
    rate_limit : Nat,
    aggregation_window : Nat
]

\* Propagate error
PropagateError(error, rules, destinations) ==
    LET applicable_rules == {r \in rules : 
                             /\ error.category \in r.error_categories
                             /\ SeverityLevel(error.severity) >= 
                                SeverityLevel(r.min_severity)}
    IN IF applicable_rules = {}
       THEN [propagated |-> FALSE]
       ELSE LET rule == CHOOSE r \in applicable_rules : TRUE
            IN CASE rule.propagation_mode = "IMMEDIATE" ->
                      [propagated |-> TRUE, destinations |-> rule.destinations]
                 [] rule.propagation_mode = "BUFFERED" ->
                      [propagated |-> FALSE, buffered |-> TRUE]
                 [] rule.propagation_mode = "FILTERED" ->
                      [propagated |-> FilterError(error), 
                       destinations |-> rule.destinations]
                 [] rule.propagation_mode = "SUPPRESSED" ->
                      [propagated |-> FALSE]

\* Severity level for comparison
SeverityLevel(severity) ==
    CASE severity = "DEBUG" -> 0
      [] severity = "INFO" -> 1
      [] severity = "WARNING" -> 2
      [] severity = "ERROR" -> 3
      [] severity = "CRITICAL" -> 4
      [] severity = "FATAL" -> 5

(****************************************************************************)
(* Error Containment                                                        *)
(****************************************************************************)

\* Containment strategy
ContainmentStrategy == [
    strategy_name : STRING,
    isolation_level : {"THREAD", "COMPONENT", "SERVICE", "NODE"},
    timeout : Nat,
    escalation_threshold : Nat,
    recovery_timeout : Nat
]

\* Contain error
ContainError(error, strategy) ==
    CASE strategy.isolation_level = "THREAD" ->
           IsolateThread(error)
      [] strategy.isolation_level = "COMPONENT" ->
           IsolateComponent(error, CurrentState)
      [] strategy.isolation_level = "SERVICE" ->
           IsolateService(error)
      [] strategy.isolation_level = "NODE" ->
           IsolateNode(error)

\* Isolate thread
IsolateThread(error) ==
    [isolated_threads |-> {ThreadId}]

\* Isolate service
IsolateService(error) ==
    [isolated_services |-> {error.source_component}]

\* Isolate node
IsolateNode(error) ==
    [isolated_nodes |-> {error.source_node}]

(****************************************************************************)
(* Fault Injection                                                          *)
(****************************************************************************)

\* Fault injection specification
FaultInjection == [
    fault_type : ErrorCategory,
    target_component : STRING,
    target_node : Node,
    injection_probability : 0..100,
    duration : Nat,
    enabled : BOOLEAN
]

\* Inject fault
InjectFault(injection, system_state) ==
    IF injection.enabled /\ RandomInt(1, 100) <= injection.injection_probability
    THEN [system_state EXCEPT
             !.injected_faults = Append(@, injection),
             !.fault_active = TRUE]
    ELSE system_state

\* Common fault injection scenarios
NetworkPartitionFault ==
    [
        fault_type |-> "NETWORK_ERROR",
        target_component |-> "NetworkLayer",
        target_node |-> n1,
        injection_probability |-> 10,
        duration |-> 60000,
        enabled |-> TRUE
    ]

PacketLossFault ==
    [
        fault_type |-> "NETWORK_ERROR",
        target_component |-> "NetworkLayer",
        target_node |-> n1,
        injection_probability |-> 5,
        duration |-> 30000,
        enabled |-> TRUE
    ]

ResourceExhaustionFault ==
    [
        fault_type |-> "RESOURCE_ERROR",
        target_component |-> "MemoryManager",
        target_node |-> n1,
        injection_probability |-> 1,
        duration |-> 10000,
        enabled |-> TRUE
    ]

CryptoFailureFault ==
    [
        fault_type |-> "CRYPTO_ERROR",
        target_component |-> "CryptoEngine",
        target_node |-> n1,
        injection_probability |-> 2,
        duration |-> 5000,
        enabled |-> TRUE
    ]

(****************************************************************************)
(* Error Logging and Diagnostics                                            *)
(****************************************************************************)

\* Error log entry
LogEntry == [
    timestamp : Nat,
    log_level : ErrorSeverity,
    component : STRING,
    message : STRING,
    error : Error,
    correlation_id : Nat,
    thread_id : Nat,
    stack_trace : Seq(STRING),
    metadata : [STRING -> Any]
]

\* Error logger
ErrorLogger == [
    log_buffer : Seq(LogEntry),
    log_file : STRING,
    max_buffer_size : Nat,
    flush_interval : Nat,
    log_rotation_size : Nat,
    retention_period : Nat
]

\* Log error
LogError(logger, error, message) ==
    LET entry == [
            timestamp |-> CurrentTime,
            log_level |-> error.severity,
            component |-> error.source_component,
            message |-> message,
            error |-> error,
            correlation_id |-> error.error_id,
            thread_id |-> CurrentThreadId,
            stack_trace |-> error.stack_trace,
            metadata |-> error.context
        ]
    IN [logger EXCEPT 
           !.log_buffer = Append(@, entry)]

\* Flush log buffer
FlushLogBuffer(logger) ==
    IF Len(logger.log_buffer) >= logger.max_buffer_size
    THEN [logger EXCEPT 
             !.log_buffer = <<>>,
             !.log_file = WriteToFile(@, logger.log_buffer)]
    ELSE logger

\* Generate diagnostic report
GenerateDiagnosticReport(errors, statistics) ==
    [
        report_time |-> CurrentTime,
        total_errors |-> statistics.total_errors,
        critical_errors |-> statistics.errors_by_severity["CRITICAL"],
        error_distribution |-> statistics.errors_by_category,
        top_error_components |-> TopErrorComponents(statistics, 10),
        error_timeline |-> ErrorTimeline(errors),
        recommendations |-> GenerateRecommendations(errors, statistics)
    ]

\* Top error components
TopErrorComponents(statistics, n) ==
    LET sorted == SortBy(statistics.errors_per_component, 
                        LAMBDA x, y : x.count >= y.count)
    IN Take(sorted, n)

\* Error timeline
ErrorTimeline(errors) ==
    GroupBy(errors, LAMBDA e : e.timestamp \div 60000)  \* Group by minute

\* Generate recommendations
GenerateRecommendations(errors, statistics) ==
    LET high_frequency_errors == {e \in errors : 
                                  statistics.errors_per_component[e.source_component] > 10}
    IN [e \in high_frequency_errors |-> 
           "Investigate " \o e.source_component \o " - high error rate"]

====

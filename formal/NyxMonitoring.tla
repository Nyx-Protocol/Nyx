---- MODULE NyxMonitoring ----
(****************************************************************************)
(* Nyx Protocol - Comprehensive Monitoring and Observability               *)
(*                                                                          *)
(* This module provides formal specifications for monitoring, metrics      *)
(* collection, observability, alerting, and telemetry systems.             *)
(*                                                                          *)
(* Monitoring Components:                                                   *)
(*   - Metrics collection and aggregation                                  *)
(*   - Distributed tracing                                                 *)
(*   - Logging and audit trails                                            *)
(*   - Health checks and liveness probes                                   *)
(*   - Performance profiling                                               *)
(*   - Alerting and notification systems                                   *)
(*   - Dashboards and visualization                                        *)
(*   - SLI/SLO tracking                                                    *)
(****************************************************************************)
(****************************************************************************)
(* Metrics Definitions                                                      *)
(****************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, Integers, Reals, TLC
LOCAL INSTANCE NyxHelpers

\* Metric types
MetricType == {
    "COUNTER",       \* Monotonically increasing counter
    "GAUGE",         \* Value that can go up and down
    "HISTOGRAM",     \* Distribution of values
    "SUMMARY",       \* Summary statistics
    "TIMER"          \* Timing measurements
}

\* Metric descriptor
Metric == [
    name : STRING,
    type : MetricType,
    value : Any,
    timestamp : Nat,
    labels : [STRING -> STRING],
    unit : STRING,
    description : STRING
]

\* Counter metric
Counter == [
    name : STRING,
    value : Nat,
    rate : Nat,  \* Per second
    total : Nat
]

\* Gauge metric
Gauge == [
    name : STRING,
    value : Int,
    min : Int,
    max : Int,
    avg : Int
]

\* Histogram metric
Histogram == [
    name : STRING,
    buckets : [Nat -> Nat],  \* Bucket upper bound -> count
    count : Nat,
    sum : Nat,
    min : Nat,
    max : Nat
]

\* Summary metric
Summary == [
    name : STRING,
    count : Nat,
    sum : Nat,
    quantiles : [Nat -> Nat]  \* Percentile -> value
]

\* Timer metric
Timer == [
    name : STRING,
    total_time : Nat,
    count : Nat,
    mean : Nat,
    max : Nat,
    min : Nat,
    stddev : Nat
]


\* Connection metrics
ConnectionMetrics == [
    active_connections : Nat,
    total_connections : Nat,
    connection_rate : Nat,
    connection_errors : Nat,
    avg_connection_duration : Nat,
    connections_per_node : [Node -> Nat]
]

\* Stream metrics
StreamMetrics == [
    active_streams : Nat,
    total_streams : Nat,
    stream_creation_rate : Nat,
    stream_errors : Nat,
    avg_stream_duration : Nat,
    streams_per_priority : [Nat -> Nat]
]

\* Traffic metrics
TrafficMetrics == [
    bytes_sent : Nat,
    bytes_received : Nat,
    packets_sent : Nat,
    packets_received : Nat,
    packets_dropped : Nat,
    send_rate_mbps : Nat,
    receive_rate_mbps : Nat
]

\* Latency metrics
LatencyMetrics == [
    mean_latency : Nat,
    p50_latency : Nat,
    p95_latency : Nat,
    p99_latency : Nat,
    p999_latency : Nat,
    max_latency : Nat,
    min_latency : Nat
]

\* Resource metrics
ResourceMetrics == [
    cpu_usage_percent : 0..100,
    memory_usage_mb : Nat,
    memory_usage_percent : 0..100,
    disk_usage_mb : Nat,
    disk_usage_percent : 0..100,
    network_bandwidth_usage_percent : 0..100,
    file_descriptors_used : Nat,
    thread_count : Nat
]

\* Throughput metrics
ThroughputMetrics == [
    messages_per_second : Nat,
    bytes_per_second : Nat,
    transactions_per_second : Nat,
    requests_per_second : Nat,
    avg_message_size : Nat
]

\* Error metrics
ErrorMetrics == [
    total_errors : Nat,
    error_rate : Nat,
    errors_by_type : [STRING -> Nat],
    errors_by_component : [STRING -> Nat],
    critical_errors : Nat,
    recoverable_errors : Nat
]


\* Metrics collector
MetricsCollector == [
    metrics : [STRING -> Metric],
    collection_interval : Nat,
    retention_period : Nat,
    aggregation_window : Nat,
    export_targets : SUBSET STRING
]

\* Collect metric
CollectMetric(collector, metric_name, value, labels) ==
    LET metric == [
            name |-> metric_name,
            type |-> "GAUGE",
            value |-> value,
            timestamp |-> CurrentTime,
            labels |-> labels,
            unit |-> "",
            description |-> ""
        ]
    IN [collector EXCEPT 
           !.metrics[metric_name] = metric]

\* Update counter
UpdateCounter(collector, counter_name, increment) ==
    LET current == IF counter_name \in DOMAIN collector.metrics
                   THEN collector.metrics[counter_name].value
                   ELSE 0
    IN [collector EXCEPT
           !.metrics[counter_name].value = current + increment]

\* Record histogram value
RecordHistogram(collector, histogram_name, value) ==
    LET histogram == IF histogram_name \in DOMAIN collector.metrics
                     THEN collector.metrics[histogram_name]
                     ELSE InitHistogram(histogram_name)
        bucket == CHOOSE b \in DOMAIN histogram.buckets : value <= b
    IN [collector EXCEPT
           !.metrics[histogram_name].buckets[bucket] = @ + 1,
           !.metrics[histogram_name].count = @ + 1,
           !.metrics[histogram_name].sum = @ + value]

\* Initialize histogram
InitHistogram(name) ==
    [
        name |-> name,
        buckets |-> [b \in {10, 25, 50, 100, 250, 500, 1000, 2500, 5000, 10000} |-> 0],
        count |-> 0,
        sum |-> 0,
        min |-> MaxInt,
        max |-> 0
    ]

\* Start timer
StartTimer(collector, timer_name) ==
    [collector EXCEPT
        !.active_timers[timer_name] = CurrentTime]

\* Stop timer
StopTimer(collector, timer_name) ==
    LET start_time == collector.active_timers[timer_name]
        duration == CurrentTime - start_time
        timer == IF timer_name \in DOMAIN collector.metrics
                THEN collector.metrics[timer_name]
                ELSE InitTimer(timer_name)
    IN [collector EXCEPT
           !.metrics[timer_name].total_time = @ + duration,
           !.metrics[timer_name].count = @ + 1,
           !.active_timers[timer_name] = 0]

\* Initialize timer
InitTimer(name) ==
    [
        name |-> name,
        total_time |-> 0,
        count |-> 0,
        mean |-> 0,
        max |-> 0,
        min |-> MaxInt,
        stddev |-> 0
    ]


\* Trace context
TraceContext == [
    trace_id : STRING,
    span_id : STRING,
    parent_span_id : STRING,
    sampled : BOOLEAN,
    baggage : [STRING -> STRING]
]

\* Span
Span == [
    trace_id : STRING,
    span_id : STRING,
    parent_span_id : STRING,
    operation_name : STRING,
    start_time : Nat,
    end_time : Nat,
    duration : Nat,
    tags : [STRING -> STRING],
    logs : Seq([
        timestamp : Nat,
        fields : [STRING -> STRING]
    ]),
    references : Seq([
        ref_type : {"CHILD_OF", "FOLLOWS_FROM"},
        trace_id : STRING,
        span_id : STRING
    ])
]

\* Tracer
Tracer == [
    service_name : STRING,
    active_spans : [STRING -> Span],
    completed_spans : Seq(Span),
    sampling_rate : 0..100,
    export_endpoint : STRING
]

\* Start span
StartSpan(tracer, operation_name, parent_span_id) ==
    LET span_id == GenerateSpanId
        trace_id == IF parent_span_id = ""
                   THEN GenerateTraceId
                   ELSE tracer.active_spans[parent_span_id].trace_id
        span == [
            trace_id |-> trace_id,
            span_id |-> span_id,
            parent_span_id |-> parent_span_id,
            operation_name |-> operation_name,
            start_time |-> CurrentTime,
            end_time |-> 0,
            duration |-> 0,
            tags |-> [x \in {} |-> 0],
            logs |-> <<>>,
            references |-> <<>>
        ]
    IN [tracer EXCEPT !.active_spans = [tracer.active_spans EXCEPT ![span_id] = span]]

\* Finish span
FinishSpan(tracer, span_id) ==
    LET span == tracer.active_spans[span_id]
        finished_span == [span EXCEPT
                             !.end_time = CurrentTime,
                             !.duration = CurrentTime - span.start_time]
    IN [tracer EXCEPT
           !.active_spans[span_id] = 0,
           !.completed_spans = Append(@, finished_span)]

\* Add span tag
AddSpanTag(tracer, span_id, key, value) ==
    [tracer EXCEPT
        !.active_spans[span_id].tags[key] = value]

\* Log to span
LogToSpan(tracer, span_id, fields) ==
    LET log_entry == [
            timestamp |-> CurrentTime,
            fields |-> fields
        ]
    IN [tracer EXCEPT
           !.active_spans[span_id].logs = Append(@, log_entry)]

\* Generate trace ID
GenerateTraceId ==
    "trace-" \o ToString(RandomInt(1, 1000000000))

\* Generate span ID
GenerateSpanId ==
    "span-" \o ToString(RandomInt(1, 1000000000))


\* Health check result
HealthCheckResult == {
    "HEALTHY",
    "DEGRADED",
    "UNHEALTHY",
    "UNKNOWN"
}

\* Health check
HealthCheck == [
    name : STRING,
    check_function : [State -> BOOLEAN],
    timeout : Nat,
    interval : Nat,
    failure_threshold : Nat,
    success_threshold : Nat,
    current_failures : Nat,
    current_successes : Nat,
    status : HealthCheckResult,
    last_check_time : Nat,
    last_success_time : Nat,
    last_failure_time : Nat,
    message : STRING
]

\* Health monitor
HealthMonitor == [
    checks : [STRING -> HealthCheck],
    overall_status : HealthCheckResult,
    unhealthy_threshold : Nat
]

\* Execute health check
ExecuteHealthCheck(monitor, check_name) ==
    LET check == monitor.checks[check_name]
        result == check.check_function[CurrentState]
        new_check == IF result
                    THEN [check EXCEPT
                             !.current_successes = @ + 1,
                             !.current_failures = 0,
                             !.last_success_time = CurrentTime,
                             !.status = IF @.current_successes >= @.success_threshold
                                       THEN "HEALTHY"
                                       ELSE @.status]
                    ELSE [check EXCEPT
                             !.current_failures = @ + 1,
                             !.current_successes = 0,
                             !.last_failure_time = CurrentTime,
                             !.status = IF @.current_failures >= @.failure_threshold
                                       THEN "UNHEALTHY"
                                       ELSE "DEGRADED"]
    IN [monitor EXCEPT
           !.checks[check_name] = new_check]

\* Update overall health status
UpdateOverallHealth(monitor) ==
    LET unhealthy_count == Cardinality({c \in DOMAIN monitor.checks : 
                                        monitor.checks[c].status = "UNHEALTHY"})
        degraded_count == Cardinality({c \in DOMAIN monitor.checks :
                                      monitor.checks[c].status = "DEGRADED"})
        overall == IF unhealthy_count > 0
                  THEN "UNHEALTHY"
                  ELSE IF degraded_count >= monitor.unhealthy_threshold
                  THEN "DEGRADED"
                  ELSE "HEALTHY"
    IN [monitor EXCEPT !.overall_status = overall]

\* Common health checks
ConnectionPoolHealthCheck ==
    [
        name |-> "ConnectionPool",
        check_function |-> [s \in State |->
            s.connection_pool.active < (s.connection_pool.max * 9) \div 10],
        timeout |-> 5000,
        interval |-> 10000,
        failure_threshold |-> 3,
        success_threshold |-> 2,
        current_failures |-> 0,
        current_successes |-> 0,
        status |-> "UNKNOWN",
        last_check_time |-> 0,
        last_success_time |-> 0,
        last_failure_time |-> 0,
        message |-> ""
    ]

MemoryHealthCheck ==
    [
        name |-> "Memory",
        check_function |-> [s \in State |->
            s.memory_usage < (s.memory_limit * 85) \div 100],
        timeout |-> 1000,
        interval |-> 5000,
        failure_threshold |-> 5,
        success_threshold |-> 1,
        current_failures |-> 0,
        current_successes |-> 0,
        status |-> "UNKNOWN",
        last_check_time |-> 0,
        last_success_time |-> 0,
        last_failure_time |-> 0,
        message |-> ""
    ]

NetworkConnectivityHealthCheck ==
    [
        name |-> "NetworkConnectivity",
        check_function |-> [s \in State |->
            Cardinality(s.reachable_nodes) >= s.min_reachable_nodes],
        timeout |-> 10000,
        interval |-> 30000,
        failure_threshold |-> 2,
        success_threshold |-> 1,
        current_failures |-> 0,
        current_successes |-> 0,
        status |-> "UNKNOWN",
        last_check_time |-> 0,
        last_success_time |-> 0,
        last_failure_time |-> 0,
        message |-> ""
    ]


\* Alert severity
AlertSeverity == {
    "INFO",
    "WARNING",
    "ERROR",
    "CRITICAL"
}

\* Alert state
AlertState == {
    "PENDING",
    "FIRING",
    "RESOLVED"
}

\* Alert
Alert == [
    alert_id : Nat,
    name : STRING,
    severity : AlertSeverity,
    state : AlertState,
    condition : [State -> BOOLEAN],
    threshold : Nat,
    duration : Nat,
    firing_time : Nat,
    resolved_time : Nat,
    message : STRING,
    labels : [STRING -> STRING],
    annotations : [STRING -> STRING]
]

\* Alert manager
AlertManager == [
    alerts : [Nat -> Alert],
    firing_alerts : SUBSET Nat,
    alert_rules : Seq(Alert),
    notification_channels : SUBSET STRING,
    grouping_interval : Nat,
    repeat_interval : Nat
]

\* Evaluate alert rule
EvaluateAlert(manager, alert_id) ==
    LET alert == manager.alerts[alert_id]
        condition_met == alert.condition[CurrentState]
        duration_exceeded == (CurrentTime - alert.firing_time) >= alert.duration
    IN CASE alert.state = "PENDING" /\ condition_met ->
              [manager EXCEPT
                  !.alerts[alert_id].state = "FIRING",
                  !.alerts[alert_id].firing_time = CurrentTime,
                  !.firing_alerts = @ \union {alert_id}]
         [] alert.state = "FIRING" /\ ~condition_met ->
              [manager EXCEPT
                  !.alerts[alert_id].state = "RESOLVED",
                  !.alerts[alert_id].resolved_time = CurrentTime,
                  !.firing_alerts = @ \ {alert_id}]
         [] alert.state = "FIRING" /\ condition_met /\ duration_exceeded ->
              SendNotification(manager, alert_id)
         [] OTHER ->
              manager

\* Send alert notification
SendNotification(manager, alert_id) ==
    LET alert == manager.alerts[alert_id]
    IN [manager EXCEPT
           !.notification_sent[alert_id] = CurrentTime]

\* Common alert rules
HighLatencyAlert ==
    [
        alert_id |-> 1,
        name |-> "HighLatency",
        severity |-> "WARNING",
        state |-> "PENDING",
        condition |-> [s \in State |-> s.avg_latency > 1000],
        threshold |-> 1000,
        duration |-> 60000,
        firing_time |-> 0,
        resolved_time |-> 0,
        message |-> "Average latency exceeds 1000ms",
        labels |-> [alertname |-> "HighLatency", severity |-> "warning"],
        annotations |-> [description |-> "Network latency is above threshold"]
    ]

HighErrorRateAlert ==
    [
        alert_id |-> 2,
        name |-> "HighErrorRate",
        severity |-> "CRITICAL",
        state |-> "PENDING",
        condition |-> [s \in State |-> s.error_rate > 100],
        threshold |-> 100,
        duration |-> 30000,
        firing_time |-> 0,
        resolved_time |-> 0,
        message |-> "Error rate exceeds 100 errors/minute",
        labels |-> [alertname |-> "HighErrorRate", severity |-> "critical"],
        annotations |-> [description |-> "System experiencing high error rate"]
    ]

ResourceExhaustionAlert ==
    [
        alert_id |-> 3,
        name |-> "ResourceExhaustion",
        severity |-> "CRITICAL",
        state |-> "PENDING",
        condition |-> [s \in State |-> 
            s.memory_usage_percent > 90 \/ s.cpu_usage_percent > 90],
        threshold |-> 90,
        duration |-> 120000,
        firing_time |-> 0,
        resolved_time |-> 0,
        message |-> "Resource usage critical",
        labels |-> [alertname |-> "ResourceExhaustion", severity |-> "critical"],
        annotations |-> [description |-> "CPU or memory usage above 90%"]
    ]


\* SLI definition
SLI == [
    name : STRING,
    description : STRING,
    metric : Metric,
    good_events : Nat,
    total_events : Nat,
    measurement_window : Nat
]

\* Service Level Objective (SLO)
SLO == [
    name : STRING,
    sli : SLI,
    target_percent : 0..100,
    window : Nat,
    current_percent : 0..100,
    error_budget : Int,
    error_budget_consumed : 0..100
]

\* Compute SLI
ComputeSLI(sli) ==
    IF sli.total_events = 0
    THEN 100
    ELSE (sli.good_events * 100) / sli.total_events

\* Check SLO compliance
CheckSLOCompliance(slo) ==
    slo.current_percent >= slo.target_percent

\* Update error budget
UpdateErrorBudget(slo) ==
    LET total_budget == ((100 - slo.target_percent) * slo.sli.total_events) / 100
        consumed == slo.sli.total_events - slo.sli.good_events
        consumed_percent == IF total_budget = 0 THEN 0 ELSE (consumed * 100) / total_budget
    IN [slo EXCEPT 
           !.error_budget = total_budget - consumed,
           !.error_budget_consumed = consumed_percent]

\* Common SLIs/SLOs
AvailabilitySLO ==
    [
        name |-> "Availability",
        sli |-> [
            name |-> "request_success_rate",
            description |-> "Percentage of successful requests",
            metric |-> SuccessRateMetric,
            good_events |-> SuccessfulRequests,
            total_events |-> TotalRequests,
            measurement_window |-> 2592000  \* 30 days
        ],
        target_percent |-> 9999 \div 100,  \* 99.99%
        window |-> 2592000,
        current_percent |-> 0,
        error_budget |-> 0,
        error_budget_consumed |-> 0
    ]

LatencySLO ==
    [
        name |-> "Latency",
        sli |-> [
            name |-> "request_latency_p99",
            description |-> "99th percentile request latency",
            metric |-> LatencyMetric,
            good_events |-> RequestsUnder100ms,
            total_events |-> TotalRequests,
            measurement_window |-> 2592000
        ],
        target_percent |-> 95,
        window |-> 2592000,
        current_percent |-> 0,
        error_budget |-> 0,
        error_budget_consumed |-> 0
    ]

ThroughputSLO ==
    [
        name |-> "Throughput",
        sli |-> [
            name |-> "throughput",
            description |-> "Requests processed per second",
            metric |-> ThroughputMetric,
            good_events |-> RequestsAboveThreshold,
            total_events |-> MeasurementWindows,
            measurement_window |-> 2592000
        ],
        target_percent |-> 98,
        window |-> 2592000,
        current_percent |-> 0,
        error_budget |-> 0,
        error_budget_consumed |-> 0
    ]


\* Profile sample
ProfileSample == [
    timestamp : Nat,
    thread_id : Nat,
    stack_trace : Seq(STRING),
    cpu_time : Nat,
    wall_time : Nat,
    memory_allocated : Nat,
    locks_held : Seq(STRING)
]

\* Profiler
Profiler == [
    enabled : BOOLEAN,
    sampling_rate : Nat,  \* Samples per second
    samples : Seq(ProfileSample),
    hot_paths : Seq([
        path : Seq(STRING),
        count : Nat,
        total_time : Nat
    ])
]

\* Capture profile sample
CaptureProfileSample(profiler) ==
    IF profiler.enabled
    THEN LET sample == [
             timestamp |-> CurrentTime,
             thread_id |-> CurrentThreadId,
             stack_trace |-> GetStackTrace,
             cpu_time |-> GetCPUTime,
             wall_time |-> GetWallTime,
             memory_allocated |-> GetMemoryAllocated,
             locks_held |-> GetLocksHeld
         ]
         IN [profiler EXCEPT
                !.samples = Append(@, sample)]
    ELSE profiler

\* Analyze profile
AnalyzeProfile(profiler) ==
    LET hot_paths == FindHotPaths(profiler.samples)
        top_allocators == FindTopAllocators(profiler.samples)
        contention_points == FindContentionPoints(profiler.samples)
    IN [
        hot_paths |-> hot_paths,
        top_allocators |-> top_allocators,
        contention_points |-> contention_points
    ]

====

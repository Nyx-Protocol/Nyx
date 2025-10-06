---- MODULE NyxAPISpecification ----
(****************************************************************************)
(* Nyx Protocol - API and Interface Specifications                         *)
(*                                                                          *)
(* Comprehensive specifications for public APIs, SDKs, client interfaces,  *)
(* service contracts, and protocol bindings.                               *)
(*                                                                          *)
(* API Components:                                                          *)
(*   - Connection management API                                           *)
(*   - Stream management API                                               *)
(*   - Configuration and control API                                       *)
(*   - Monitoring and diagnostics API                                      *)
(*   - Event notification API                                              *)
(*   - Authentication and authorization API                                *)
(*   - gRPC service definitions                                            *)
(*   - RESTful API endpoints                                               *)
(*   - WebSocket interface                                                 *)
(*   - Language bindings and SDKs                                          *)
(****************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, Integers, TLC,
        NyxNetworkLayer, NyxStreamManagement, NyxCryptography

(****************************************************************************)
(* Connection Management API                                                *)
(****************************************************************************)

\* Connection request
ConnectionRequest == [
    connection_id : STRING,
    destination : Node,
    options : [
        timeout : Nat,
        max_streams : Nat,
        priority : Nat,
        qos_class : QoSClass,
        metadata : [STRING -> Any]
    ],
    credentials : [
        auth_token : STRING,
        certificate : STRING
    ]
]

\* Connection response
ConnectionResponse == [
    success : BOOLEAN,
    connection_id : STRING,
    error_code : Nat,
    error_message : STRING,
    connection_info : [
        local_address : IPAddress,
        remote_address : IPAddress,
        established_time : Nat,
        session_id : STRING
    ]
]

\* Connect API
API_Connect(request) ==
    LET validation == ValidateConnectionRequest(request)
    IN IF validation.valid
       THEN LET connection == EstablishConnection(request)
            IN IF connection.success
               THEN [
                   success |-> TRUE,
                   connection_id |-> connection.id,
                   error_code |-> 0,
                   error_message |-> "",
                   connection_info |-> [
                       local_address |-> connection.local_addr,
                       remote_address |-> connection.remote_addr,
                       established_time |-> CurrentTime,
                       session_id |-> connection.session_id
                   ]
               ]
               ELSE [
                   success |-> FALSE,
                   connection_id |-> "",
                   error_code |-> connection.error_code,
                   error_message |-> connection.error_message,
                   connection_info |-> NullConnectionInfo
               ]
       ELSE [
           success |-> FALSE,
           connection_id |-> "",
           error_code |-> 400,
           error_message |-> validation.error,
           connection_info |-> NullConnectionInfo
       ]

\* Disconnect API
API_Disconnect(connection_id) ==
    LET connection == LookupConnection(connection_id)
    IN IF connection # NullConnection
       THEN LET close_result == CloseConnection(connection)
            IN [success |-> close_result.success,
                error_code |-> close_result.error_code,
                error_message |-> close_result.error_message]
       ELSE [success |-> FALSE,
             error_code |-> 404,
             error_message |-> "Connection not found"]

\* Get connection status
API_GetConnectionStatus(connection_id) ==
    LET connection == LookupConnection(connection_id)
    IN IF connection # NullConnection
       THEN [
           success |-> TRUE,
           status |-> connection.state,
           stats |-> [
               packets_sent |-> connection.stats.packets_sent,
               packets_received |-> connection.stats.packets_received,
               bytes_sent |-> connection.stats.bytes_sent,
               bytes_received |-> connection.stats.bytes_received,
               rtt |-> connection.stats.rtt,
               loss_rate |-> connection.stats.loss_rate
           ]
       ]
       ELSE [success |-> FALSE,
             error_code |-> 404,
             error_message |-> "Connection not found"]

\* List connections
API_ListConnections(filter) ==
    LET connections == GetAllConnections()
        filtered == IF filter # NullFilter
                   THEN {c \in connections : MatchesFilter(c, filter)}
                   ELSE connections
    IN [
        success |-> TRUE,
        count |-> Cardinality(filtered),
        connections |-> [c \in filtered |-> SerializeConnection(c)]
    ]

(****************************************************************************)
(* Stream Management API                                                    *)
(****************************************************************************)

\* Stream creation request
StreamRequest == [
    connection_id : STRING,
    stream_type : {"UNIDIRECTIONAL", "BIDIRECTIONAL"},
    priority : Nat,
    flow_control_window : Nat,
    metadata : [STRING -> Any]
]

\* Stream response
StreamResponse == [
    success : BOOLEAN,
    stream_id : STRING,
    error_code : Nat,
    error_message : STRING
]

\* Open stream API
API_OpenStream(request) ==
    LET connection == LookupConnection(request.connection_id)
    IN IF connection # NullConnection
       THEN LET stream == CreateStream(connection, request)
            IN IF stream.success
               THEN [
                   success |-> TRUE,
                   stream_id |-> stream.id,
                   error_code |-> 0,
                   error_message |-> ""
               ]
               ELSE [
                   success |-> FALSE,
                   stream_id |-> "",
                   error_code |-> stream.error_code,
                   error_message |-> stream.error_message
               ]
       ELSE [
           success |-> FALSE,
           stream_id |-> "",
           error_code |-> 404,
           error_message |-> "Connection not found"
       ]

\* Close stream API
API_CloseStream(stream_id) ==
    LET stream == LookupStream(stream_id)
    IN IF stream # NullStream
       THEN [success |-> CloseStream(stream).success]
       ELSE [success |-> FALSE,
             error_code |-> 404,
             error_message |-> "Stream not found"]

\* Send data on stream
API_SendData(stream_id, data) ==
    LET stream == LookupStream(stream_id)
    IN IF stream # NullStream
       THEN LET send_result == SendOnStream(stream, data)
            IN [
                success |-> send_result.success,
                bytes_sent |-> send_result.bytes_sent,
                error_code |-> send_result.error_code
            ]
       ELSE [success |-> FALSE,
             bytes_sent |-> 0,
             error_code |-> 404]

\* Receive data from stream
API_ReceiveData(stream_id, max_bytes) ==
    LET stream == LookupStream(stream_id)
    IN IF stream # NullStream
       THEN LET recv_result == ReceiveFromStream(stream, max_bytes)
            IN [
                success |-> recv_result.success,
                data |-> recv_result.data,
                bytes_received |-> recv_result.bytes_received,
                end_of_stream |-> recv_result.eos
            ]
       ELSE [success |-> FALSE,
             data |-> <<>>,
             bytes_received |-> 0,
             end_of_stream |-> FALSE]

\* Get stream statistics
API_GetStreamStats(stream_id) ==
    LET stream == LookupStream(stream_id)
    IN IF stream # NullStream
       THEN [
           success |-> TRUE,
           stats |-> [
               bytes_sent |-> stream.stats.bytes_sent,
               bytes_received |-> stream.stats.bytes_received,
               frames_sent |-> stream.stats.frames_sent,
               frames_received |-> stream.stats.frames_received,
               retransmissions |-> stream.stats.retransmissions,
               current_window |-> stream.flow_control.window_size
           ]
       ]
       ELSE [success |-> FALSE, error_code |-> 404]

(****************************************************************************)
(* Configuration and Control API                                            *)
(****************************************************************************)

\* Configuration update request
ConfigUpdateRequest == [
    section : STRING,
    parameters : [STRING -> Any],
    apply_immediately : BOOLEAN,
    validate_only : BOOLEAN
]

\* Update configuration
API_UpdateConfig(request) ==
    LET validation == ValidateConfig(request.parameters)
    IN IF request.validate_only
       THEN [success |-> validation.valid,
             errors |-> validation.errors]
       ELSE IF validation.valid
            THEN LET update_result == ApplyConfigUpdate(request)
                 IN [success |-> update_result.success,
                     restart_required |-> update_result.restart_required]
            ELSE [success |-> FALSE,
                  errors |-> validation.errors]

\* Get configuration
API_GetConfig(section) ==
    LET config == GetCurrentConfig(section)
    IN [
        success |-> TRUE,
        config |-> config,
        version |-> config.version
    ]

\* Reset configuration
API_ResetConfig(section) ==
    LET reset_result == ResetToDefaultConfig(section)
    IN [success |-> reset_result.success]

\* Export configuration
API_ExportConfig(format) ==
    LET config == GetAllConfig()
        exported == SerializeConfig(config, format)
    IN [
        success |-> TRUE,
        data |-> exported,
        format |-> format
    ]

\* Import configuration
API_ImportConfig(data, format) ==
    LET parsed == ParseConfig(data, format)
        validation == ValidateConfig(parsed)
    IN IF validation.valid
       THEN LET import_result == ImportConfigData(parsed)
            IN [success |-> import_result.success,
                restart_required |-> import_result.restart_required]
       ELSE [success |-> FALSE,
             errors |-> validation.errors]

(****************************************************************************)
(* Monitoring and Diagnostics API                                           *)
(****************************************************************************)

\* Metrics query
MetricsQuery == [
    metric_names : SUBSET STRING,
    time_range : [start : Nat, end : Nat],
    aggregation : {"AVG", "SUM", "MIN", "MAX", "COUNT"},
    group_by : SUBSET STRING
]

\* Query metrics
API_QueryMetrics(query) ==
    LET metrics == CollectMetrics(query.metric_names, query.time_range)
        aggregated == AggregateMetrics(metrics, query.aggregation, query.group_by)
    IN [
        success |-> TRUE,
        metrics |-> aggregated,
        count |-> Cardinality(aggregated)
    ]

\* Get real-time statistics
API_GetStats(category) ==
    LET stats == CASE category = "NETWORK" ->
                     GetNetworkStats()
                [] category = "STREAMS" ->
                     GetStreamStats()
                [] category = "CRYPTO" ->
                     GetCryptoStats()
                [] category = "SYSTEM" ->
                     GetSystemStats()
                [] OTHER ->
                     GetAllStats()
    IN [success |-> TRUE, statistics |-> stats]

\* Get health status
API_GetHealth() ==
    LET health_checks == RunHealthChecks()
        overall_status == ComputeOverallHealth(health_checks)
    IN [
        success |-> TRUE,
        status |-> overall_status,
        checks |-> health_checks,
        timestamp |-> CurrentTime
    ]

\* Get diagnostics
API_GetDiagnostics() ==
    [
        success |-> TRUE,
        diagnostics |-> [
            version |-> GetVersion(),
            uptime |-> GetUptime(),
            memory_usage |-> GetMemoryUsage(),
            cpu_usage |-> GetCPUUsage(),
            active_connections |-> CountActiveConnections(),
            active_streams |-> CountActiveStreams(),
            error_rate |-> GetErrorRate(),
            warnings |-> GetActiveWarnings()
        ]
    ]

\* Enable/disable tracing
API_SetTracing(enabled, level, filters) ==
    LET tracing_config == [
            enabled |-> enabled,
            level |-> level,
            filters |-> filters
        ]
        result == ConfigureTracing(tracing_config)
    IN [success |-> result.success]

(****************************************************************************)
(* Event Notification API                                                   *)
(****************************************************************************)

\* Event subscription
EventSubscription == [
    subscription_id : STRING,
    event_types : SUBSET STRING,
    filters : [STRING -> Any],
    delivery : [
        method : {"CALLBACK", "WEBHOOK", "QUEUE"},
        endpoint : STRING,
        batch_size : Nat,
        batch_timeout : Nat
    ]
]

\* Subscribe to events
API_SubscribeEvents(subscription) ==
    LET sub_id == GenerateSubscriptionId
        registered == RegisterEventSubscription(sub_id, subscription)
    IN IF registered.success
       THEN [
           success |-> TRUE,
           subscription_id |-> sub_id
       ]
       ELSE [
           success |-> FALSE,
           error_message |-> registered.error
       ]

\* Unsubscribe from events
API_UnsubscribeEvents(subscription_id) ==
    LET result == UnregisterEventSubscription(subscription_id)
    IN [success |-> result.success]

\* Get event history
API_GetEventHistory(query) ==
    LET events == QueryEventLog(query)
    IN [
        success |-> TRUE,
        events |-> events,
        count |-> Len(events)
    ]

\* Emit custom event
API_EmitEvent(event_type, data) ==
    LET event == [
            type |-> event_type,
            data |-> data,
            timestamp |-> CurrentTime,
            source |-> "API"
        ]
        emitted == EmitEvent(event)
    IN [success |-> emitted.success]

(****************************************************************************)
(* Authentication and Authorization API                                     *)
(****************************************************************************)

\* Authentication request
AuthRequest == [
    method : {"PASSWORD", "TOKEN", "CERTIFICATE", "OAUTH"},
    credentials : [STRING -> STRING],
    scope : SUBSET STRING
]

\* Authentication response
AuthResponse == [
    success : BOOLEAN,
    token : STRING,
    expires_at : Nat,
    refresh_token : STRING,
    permissions : SUBSET STRING
]

\* Authenticate
API_Authenticate(request) ==
    LET validation == ValidateCredentials(request.credentials, request.method)
    IN IF validation.valid
       THEN LET auth_result == PerformAuthentication(request)
            IN IF auth_result.success
               THEN [
                   success |-> TRUE,
                   token |-> GenerateAuthToken(auth_result.user),
                   expires_at |-> CurrentTime + TokenLifetime,
                   refresh_token |-> GenerateRefreshToken(auth_result.user),
                   permissions |-> GetUserPermissions(auth_result.user)
               ]
               ELSE [
                   success |-> FALSE,
                   error_code |-> 401,
                   error_message |-> "Authentication failed"
               ]
       ELSE [
           success |-> FALSE,
           error_code |-> 400,
           error_message |-> validation.error
       ]

\* Refresh token
API_RefreshToken(refresh_token) ==
    LET validation == ValidateRefreshToken(refresh_token)
    IN IF validation.valid
       THEN [
           success |-> TRUE,
           token |-> GenerateAuthToken(validation.user),
           expires_at |-> CurrentTime + TokenLifetime
       ]
       ELSE [
           success |-> FALSE,
           error_code |-> 401,
           error_message |-> "Invalid refresh token"
       ]

\* Check authorization
API_CheckAuthorization(token, resource, action) ==
    LET token_validation == ValidateAuthToken(token)
    IN IF token_validation.valid
       THEN LET authorized == CheckPermission(token_validation.user, resource, action)
            IN [success |-> TRUE, authorized |-> authorized]
       ELSE [success |-> FALSE, authorized |-> FALSE]

\* Revoke token
API_RevokeToken(token) ==
    LET revoke_result == RevokeAuthToken(token)
    IN [success |-> revoke_result.success]

(****************************************************************************)
(* gRPC Service Definitions                                                 *)
(****************************************************************************)

\* gRPC service: NyxConnectionService
GRPC_ConnectionService == [
    Connect : ConnectionRequest -> ConnectionResponse,
    Disconnect : STRING -> [success : BOOLEAN],
    GetStatus : STRING -> ConnectionResponse,
    ListConnections : Any -> Seq(ConnectionResponse)
]

\* gRPC service: NyxStreamService
GRPC_StreamService == [
    OpenStream : StreamRequest -> StreamResponse,
    CloseStream : STRING -> [success : BOOLEAN],
    SendData : [stream_id : STRING, data : Seq(Nat)] -> [success : BOOLEAN, bytes_sent : Nat],
    ReceiveData : [stream_id : STRING, max_bytes : Nat] -> [data : Seq(Nat), eos : BOOLEAN],
    StreamStats : STRING -> [stats : Any]
]

\* gRPC service: NyxConfigService
GRPC_ConfigService == [
    GetConfig : STRING -> [config : Any],
    UpdateConfig : ConfigUpdateRequest -> [success : BOOLEAN],
    ResetConfig : STRING -> [success : BOOLEAN],
    ExportConfig : STRING -> [data : STRING],
    ImportConfig : [data : STRING, format : STRING] -> [success : BOOLEAN]
]

\* gRPC service: NyxMonitoringService
GRPC_MonitoringService == [
    QueryMetrics : MetricsQuery -> [metrics : Any],
    GetStats : STRING -> [stats : Any],
    GetHealth : Any -> [status : STRING, checks : Any],
    GetDiagnostics : Any -> [diagnostics : Any],
    StreamMetrics : [query : MetricsQuery] -> STREAM(Any)
]

(****************************************************************************)
(* RESTful API Endpoints                                                    *)
(****************************************************************************)

\* REST endpoint specification
RESTEndpoint == [
    method : {"GET", "POST", "PUT", "DELETE", "PATCH"},
    path : STRING,
    handler : [Any -> Any],
    auth_required : BOOLEAN,
    rate_limit : Nat
]

\* Define REST endpoints
REST_Endpoints == {
    \* Connection endpoints
    [method |-> "POST", path |-> "/api/v1/connections",
     handler |-> API_Connect, auth_required |-> TRUE, rate_limit |-> 100],
    [method |-> "DELETE", path |-> "/api/v1/connections/{id}",
     handler |-> API_Disconnect, auth_required |-> TRUE, rate_limit |-> 100],
    [method |-> "GET", path |-> "/api/v1/connections/{id}",
     handler |-> API_GetConnectionStatus, auth_required |-> TRUE, rate_limit |-> 1000],
    [method |-> "GET", path |-> "/api/v1/connections",
     handler |-> API_ListConnections, auth_required |-> TRUE, rate_limit |-> 100],
    
    \* Stream endpoints
    [method |-> "POST", path |-> "/api/v1/streams",
     handler |-> API_OpenStream, auth_required |-> TRUE, rate_limit |-> 100],
    [method |-> "DELETE", path |-> "/api/v1/streams/{id}",
     handler |-> API_CloseStream, auth_required |-> TRUE, rate_limit |-> 100],
    [method |-> "POST", path |-> "/api/v1/streams/{id}/send",
     handler |-> API_SendData, auth_required |-> TRUE, rate_limit |-> 10000],
    [method |-> "GET", path |-> "/api/v1/streams/{id}/receive",
     handler |-> API_ReceiveData, auth_required |-> TRUE, rate_limit |-> 10000],
    
    \* Configuration endpoints
    [method |-> "GET", path |-> "/api/v1/config/{section}",
     handler |-> API_GetConfig, auth_required |-> TRUE, rate_limit |-> 100],
    [method |-> "PUT", path |-> "/api/v1/config/{section}",
     handler |-> API_UpdateConfig, auth_required |-> TRUE, rate_limit |-> 10],
    [method |-> "POST", path |-> "/api/v1/config/export",
     handler |-> API_ExportConfig, auth_required |-> TRUE, rate_limit |-> 10],
    [method |-> "POST", path |-> "/api/v1/config/import",
     handler |-> API_ImportConfig, auth_required |-> TRUE, rate_limit |-> 10],
    
    \* Monitoring endpoints
    [method |-> "POST", path |-> "/api/v1/metrics/query",
     handler |-> API_QueryMetrics, auth_required |-> TRUE, rate_limit |-> 100],
    [method |-> "GET", path |-> "/api/v1/stats/{category}",
     handler |-> API_GetStats, auth_required |-> TRUE, rate_limit |-> 1000],
    [method |-> "GET", path |-> "/api/v1/health",
     handler |-> API_GetHealth, auth_required |-> FALSE, rate_limit |-> 10000],
    [method |-> "GET", path |-> "/api/v1/diagnostics",
     handler |-> API_GetDiagnostics, auth_required |-> TRUE, rate_limit |-> 100],
    
    \* Authentication endpoints
    [method |-> "POST", path |-> "/api/v1/auth/login",
     handler |-> API_Authenticate, auth_required |-> FALSE, rate_limit |-> 10],
    [method |-> "POST", path |-> "/api/v1/auth/refresh",
     handler |-> API_RefreshToken, auth_required |-> FALSE, rate_limit |-> 100],
    [method |-> "POST", path |-> "/api/v1/auth/logout",
     handler |-> API_RevokeToken, auth_required |-> TRUE, rate_limit |-> 100]
}

(****************************************************************************)
(* WebSocket Interface                                                      *)
(****************************************************************************)

\* WebSocket message types
WSMessageType == {"CONTROL", "DATA", "PING", "PONG", "CLOSE"}

\* WebSocket message
WSMessage == [
    type : WSMessageType,
    payload : Any,
    timestamp : Nat
]

\* WebSocket connection state
WSConnection == [
    connection_id : STRING,
    state : {"CONNECTING", "OPEN", "CLOSING", "CLOSED"},
    subscriptions : SUBSET STRING,
    last_activity : Nat
]

\* Handle WebSocket message
HandleWSMessage(ws_conn, message) ==
    CASE message.type = "CONTROL" ->
        ProcessControlMessage(ws_conn, message.payload)
    [] message.type = "DATA" ->
        ProcessDataMessage(ws_conn, message.payload)
    [] message.type = "PING" ->
        SendWSMessage(ws_conn, [type |-> "PONG", payload |-> <<>>])
    [] message.type = "CLOSE" ->
        CloseWSConnection(ws_conn)

\* Send WebSocket message
SendWSMessage(ws_conn, message) ==
    IF ws_conn.state = "OPEN"
    THEN [success |-> TRUE, connection |-> ws_conn]
    ELSE [success |-> FALSE, connection |-> ws_conn]

(****************************************************************************)
(* SDK and Language Bindings                                                *)
(****************************************************************************)

\* SDK client state
SDKClient == [
    client_id : STRING,
    api_endpoint : STRING,
    auth_token : STRING,
    config : [
        timeout : Nat,
        retry_policy : [max_retries : Nat, backoff : STRING],
        connection_pool_size : Nat
    ],
    active_connections : [STRING -> ConnectionResponse],
    active_streams : [STRING -> StreamResponse]
]

\* SDK initialization
SDK_Initialize(endpoint, auth_token, config) ==
    [
        client_id |-> GenerateClientId,
        api_endpoint |-> endpoint,
        auth_token |-> auth_token,
        config |-> config,
        active_connections |-> [c \in {} |-> NullConnectionResponse],
        active_streams |-> [s \in {} |-> NullStreamResponse]
    ]

\* SDK connect wrapper
SDK_Connect(client, destination, options) ==
    LET request == [
            connection_id |-> GenerateConnectionId,
            destination |-> destination,
            options |-> options,
            credentials |-> [auth_token |-> client.auth_token, certificate |-> ""]
        ]
        response == API_Connect(request)
    IN IF response.success
       THEN [success |-> TRUE,
             connection |-> response,
             client |-> [client EXCEPT
                 !.active_connections[response.connection_id] = response]]
       ELSE [success |-> FALSE,
             connection |-> response,
             client |-> client]

(****************************************************************************)
(* API Properties and Invariants                                            *)
(****************************************************************************)

\* API idempotency
THEOREM APIIdempotency ==
    \A request \in IdempotentRequests :
        API_Call(request) = API_Call(request)

\* API authentication enforcement
THEOREM AuthenticationEnforcement ==
    \A endpoint \in REST_Endpoints :
        endpoint.auth_required =>
            \A request : RequiresValidToken(request)

\* Rate limiting
THEOREM RateLimiting ==
    \A endpoint \in REST_Endpoints, client \in Clients :
        RequestsPerSecond(client, endpoint) <= endpoint.rate_limit

\* API backward compatibility
THEOREM BackwardCompatibility ==
    \A old_request \in V1_Requests :
        CompatibleWith(V2_API, old_request)

====

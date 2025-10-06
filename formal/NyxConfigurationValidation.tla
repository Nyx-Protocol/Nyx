---- MODULE NyxConfigurationValidation ----
(****************************************************************************)
(* Nyx Protocol - Configuration Validation and Policy Management           *)
(*                                                                          *)
(* Comprehensive specifications for configuration management, validation,  *)
(* policy enforcement, constraint checking, and automated remediation.     *)
(*                                                                          *)
(* Configuration Components:                                                *)
(*   - Configuration schema and validation                                 *)
(*   - Policy definition and enforcement                                   *)
(*   - Constraint checking and conflict detection                          *)
(*   - Configuration versioning and rollback                               *)
(*   - Template-based configuration                                        *)
(*   - Dynamic reconfiguration                                             *)
(*   - Configuration drift detection                                       *)
(*   - Compliance validation                                               *)
(*   - Intent-based configuration                                          *)
(*   - Automated remediation                                               *)
(****************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets, Integers, TLC

(****************************************************************************)
(* Configuration Schema and Data Model                                      *)
(****************************************************************************)

\* Configuration value types
ConfigValueType == {
    "STRING", "INTEGER", "REAL", "BOOLEAN", "ENUM",
    "IPV4_ADDRESS", "IPV6_ADDRESS", "MAC_ADDRESS",
    "PORT_NUMBER", "DURATION", "BANDWIDTH",
    "ARRAY", "OBJECT", "REFERENCE"
}

\* Configuration parameter definition
ConfigParameterDef == [
    param_name : STRING,
    param_type : ConfigValueType,
    
    \* Validation rules
    required : BOOLEAN,
    default_value : Any,
    
    \* Constraints
    constraints : Seq([
        constraint_type : {"RANGE", "LENGTH", "REGEX", "ENUM_VALUES",
                          "DEPENDENCY", "EXCLUSION", "CUSTOM"},
        constraint_value : Any
    ]),
    
    \* Documentation
    description : STRING,
    examples : Seq(Any),
    
    \* Metadata
    mutable : BOOLEAN,
    requires_restart : BOOLEAN,
    sensitivity : {"PUBLIC", "INTERNAL", "CONFIDENTIAL", "SECRET"}
]

\* Configuration schema
ConfigSchema == [
    schema_id : STRING,
    version : STRING,
    
    \* Parameters
    parameters : [STRING -> ConfigParameterDef],
    
    \* Sections
    sections : [STRING -> Seq(STRING)],  \* Section name to parameter names
    
    \* Global constraints
    global_constraints : Seq([
        constraint_id : STRING,
        description : STRING,
        condition : [Configuration -> BOOLEAN]
    ])
]

\* Configuration instance
Configuration == [
    config_id : STRING,
    schema_id : STRING,
    version : Nat,
    
    \* Values
    values : [STRING -> Any],
    
    \* Metadata
    created_at : Nat,
    modified_at : Nat,
    created_by : STRING,
    modified_by : STRING,
    
    \* Status
    status : {"DRAFT", "VALIDATING", "VALID", "INVALID", "ACTIVE", "ARCHIVED"},
    validation_errors : Seq([
        param_name : STRING,
        error_type : STRING,
        error_message : STRING
    ]),
    
    \* History
    parent_version : Nat,
    change_description : STRING
]

(****************************************************************************)
(* Configuration Validation                                                 *)
(****************************************************************************)

\* Validate configuration against schema
ValidateConfiguration(config, schema) ==
    LET 
        \* Check all required parameters
        required_params == {p \in DOMAIN schema.parameters :
            schema.parameters[p].required}
        missing_params == required_params \ DOMAIN config.values
        
        missing_errors == [p \in missing_params |->
            [param_name |-> p,
             error_type |-> "MISSING_REQUIRED",
             error_message |-> "Required parameter is missing"]]
        
        \* Validate each parameter
        param_errors == UNION {ValidateParameter(
                                   p,
                                   config.values[p],
                                   schema.parameters[p]) :
                               p \in DOMAIN config.values}
        
        \* Check global constraints
        constraint_errors == {c \in schema.global_constraints :
            TRUE}
        
        all_errors == missing_errors \union param_errors \union constraint_errors
    IN [
        valid |-> all_errors = {},
        errors |-> all_errors
    ]

\* Validate individual parameter
ValidateParameter(param_name, value, param_def) ==
    LET 
        \* Type check
        type_valid == CheckType(value, param_def.param_type)
        type_error == IF ~type_valid
                     THEN {[param_name |-> param_name,
                            error_type |-> "TYPE_MISMATCH",
                            error_message |-> "Value type does not match definition"]}
                     ELSE {}
        
        \* Constraint checks
        RECURSIVE CheckConstraints(_)
        CheckConstraints(remaining_constraints) ==
            IF remaining_constraints = <<>>
            THEN {}
            ELSE LET constraint == Head(remaining_constraints)
                     satisfied == EvaluateConstraint(value, constraint)
                     error == IF ~satisfied
                             THEN {[param_name |-> param_name,
                                    error_type |-> constraint.constraint_type,
                                    error_message |-> FormatConstraintError(constraint)]}
                             ELSE {}
                 IN error \union CheckConstraints(Tail(remaining_constraints))
        
        constraint_errors == CheckConstraints(param_def.constraints)
    IN type_error \union constraint_errors

\* Evaluate constraint
EvaluateConstraint(value, constraint) ==
    CASE constraint.constraint_type = "RANGE" ->
        value >= constraint.constraint_value.min /\
        value <= constraint.constraint_value.max
    [] constraint.constraint_type = "LENGTH" ->
        Len(value) >= constraint.constraint_value.min /\
        Len(value) <= constraint.constraint_value.max
    [] constraint.constraint_type = "REGEX" ->
        MatchesRegex(value, constraint.constraint_value.pattern)
    [] constraint.constraint_type = "ENUM_VALUES" ->
        value \in constraint.constraint_value.allowed_values
    [] OTHER -> TRUE

(****************************************************************************)
(* Policy Definition and Enforcement                                        *)
(****************************************************************************)

\* Policy types
PolicyType == {
    "SECURITY", "QOS", "ROUTING", "ACCESS_CONTROL",
    "RESOURCE_ALLOCATION", "COMPLIANCE", "OPERATIONAL"
}

\* Policy rule
PolicyRule == [
    rule_id : STRING,
    policy_id : STRING,
    priority : Nat,
    
    \* Condition
    condition : [
        type : {"AND", "OR", "NOT", "COMPARISON"},
        operands : Seq([
            attribute : STRING,
            operator : {"EQ", "NEQ", "LT", "LTE", "GT", "GTE", "IN", "MATCHES"},
            value : Any
        ])
    ],
    
    \* Action
    action : [
        action_type : {"ALLOW", "DENY", "MODIFY", "ALERT", "LOG", "REDIRECT"},
        parameters : [STRING -> Any]
    ],
    
    \* Metadata
    enabled : BOOLEAN,
    description : STRING
]

\* Policy
Policy == [
    policy_id : STRING,
    policy_name : STRING,
    policy_type : PolicyType,
    
    \* Rules
    rules : Seq(PolicyRule),
    
    \* Scope
    scope : [
        applies_to : SUBSET STRING,  \* Resource IDs
        exclude : SUBSET STRING
    ],
    
    \* Enforcement
    enforcement_mode : {"ENFORCING", "PERMISSIVE", "DISABLED"},
    conflict_resolution : {"FIRST_MATCH", "MOST_SPECIFIC", "HIGHEST_PRIORITY"},
    
    \* Lifecycle
    version : Nat,
    status : {"DRAFT", "ACTIVE", "DEPRECATED", "ARCHIVED"},
    effective_from : Nat,
    effective_until : Nat
]

\* Evaluate policy
EvaluatePolicy(policy, context) ==
    LET 
        \* Filter applicable rules
        applicable_rules == {r \in policy.rules :
            r.enabled /\
            context.resource_id \in policy.scope.applies_to /\
            context.resource_id \notin policy.scope.exclude}
        
        \* Evaluate each rule
        rule_results == [r \in applicable_rules |->
            [rule |-> r,
             matches |-> EvaluateCondition(r.condition, context),
             action |-> r.action]]
        
        \* Find matching rules
        matching_results == {rr \in rule_results : rr.matches}
        
        \* Apply conflict resolution
        final_action == IF matching_results = {}
                       THEN [action_type |-> "ALLOW", parameters |-> {}]
                       ELSE CASE policy.conflict_resolution = "FIRST_MATCH" ->
                               (CHOOSE rr \in matching_results : TRUE).action
                            [] policy.conflict_resolution = "HIGHEST_PRIORITY" ->
                               (CHOOSE rr \in matching_results :
                                   \A other \in matching_results :
                                       rr.rule.priority >= other.rule.priority).action
                            [] OTHER -> (CHOOSE rr \in matching_results : TRUE).action
    IN [
        policy_id |-> policy.policy_id,
        matched |-> matching_results # {},
        action |-> final_action,
        matched_rules |-> {rr.rule.rule_id : rr \in matching_results}
    ]

\* Evaluate condition
EvaluateCondition(condition, context) ==
    CASE condition.type = "AND" ->
        \A op \in condition.operands : EvaluateOperand(op, context)
    [] condition.type = "OR" ->
        \E op \in condition.operands : EvaluateOperand(op, context)
    [] condition.type = "NOT" ->
        ~EvaluateOperand(condition.operands[1], context)
    [] condition.type = "COMPARISON" ->
        EvaluateOperand(condition.operands[1], context)

\* Evaluate operand
EvaluateOperand(operand, context) ==
    LET attr_value == GetContextAttribute(context, operand.attribute)
    IN CASE operand.operator = "EQ" -> attr_value = operand.value
       [] operand.operator = "NEQ" -> attr_value # operand.value
       [] operand.operator = "LT" -> attr_value < operand.value
       [] operand.operator = "LTE" -> attr_value <= operand.value
       [] operand.operator = "GT" -> attr_value > operand.value
       [] operand.operator = "GTE" -> attr_value >= operand.value
       [] operand.operator = "IN" -> attr_value \in operand.value
       [] operand.operator = "MATCHES" -> MatchesPattern(attr_value, operand.value)

(****************************************************************************)
(* Constraint Checking and Conflict Detection                               *)
(****************************************************************************)

\* Constraint types
ConstraintType == {
    "RESOURCE_LIMIT", "DEPENDENCY", "MUTUAL_EXCLUSION",
    "ORDERING", "CARDINALITY", "CONSISTENCY"
}

\* Constraint
Constraint == [
    constraint_id : STRING,
    constraint_type : ConstraintType,
    
    \* Affected parameters
    parameters : SUBSET STRING,
    
    \* Constraint expression (removed for model checking simplicity)
    \* expression : [Configuration -> BOOLEAN],
    
    \* Severity
    severity : {"ERROR", "WARNING", "INFO"},
    
    \* Metadata
    description : STRING,
    remediation_hint : STRING
]

\* Check constraints
CheckConstraints(config, constraints) ==
    LET violations == {c \in constraints :
            TRUE}
        
        errors == {v \in violations : v.severity = "ERROR"}
        warnings == {v \in violations : v.severity = "WARNING"}
    IN [
        has_errors |-> errors # {},
        has_warnings |-> warnings # {},
        errors |-> errors,
        warnings |-> warnings
    ]

\* Detect configuration conflicts
DetectConfigurationConflicts(config1, config2) ==
    LET common_params == DOMAIN config1.values \intersect DOMAIN config2.values
        
        conflicts == {p \in common_params :
            config1.values[p] # config2.values[p] /\
            ~CanCoexist(p, config1.values[p], config2.values[p])}
        
        conflict_details == [c \in conflicts |->
            [parameter |-> c,
             value1 |-> config1.values[c],
             value2 |-> config2.values[c],
             resolution |-> SuggestConflictResolution(c, config1.values[c], config2.values[c])]]
    IN [
        has_conflicts |-> conflicts # {},
        conflicts |-> conflict_details
    ]

\* Dependency analysis
AnalyzeDependencies(config, schema) ==
    LET 
        \* Build dependency graph
        dependencies == UNION {{[from |-> p, to |-> d] :
            d \in c.constraint_value.depends_on} :
            p \in DOMAIN schema.parameters,
            c \in {x \in schema.parameters[p].constraints : x.constraint_type = "DEPENDENCY"}}
        
        \* Check for missing dependencies
        missing_deps == {dep \in dependencies :
            dep.from \in DOMAIN config.values /\
            dep.to \notin DOMAIN config.values}
        
        \* Check for circular dependencies
        circular_deps == DetectCircularDependencies(dependencies)
    IN [
        missing_dependencies |-> missing_deps,
        circular_dependencies |-> circular_deps,
        dependency_order |-> TopologicalSort(dependencies)
    ]

\* Detect circular dependencies
DetectCircularDependencies(dependencies) ==
    LET 
        RECURSIVE FindCycles(_, _, _)
        FindCycles(node, visited, path) ==
            IF node \in visited
            THEN IF node \in path
                 THEN {path \o <<node>>}
                 ELSE {}
            ELSE LET neighbors == {dep.to : dep \in {d \in dependencies : d.from = node}}
                     new_visited == visited \union {node}
                     new_path == path \o <<node>>
                 IN UNION {FindCycles(n, new_visited, new_path) : n \in neighbors}
        
        all_nodes == {dep.from : dep \in dependencies} \union
                    {dep.to : dep \in dependencies}
        
        cycles == UNION {FindCycles(n, {}, <<>>) : n \in all_nodes}
    IN cycles

(****************************************************************************)
(* Configuration Versioning and Rollback                                    *)
(****************************************************************************)

\* Configuration version history
ConfigurationHistory == [
    config_id : STRING,
    versions : Seq([
        version_number : Nat,
        configuration : Configuration,
        timestamp : Nat,
        author : STRING,
        change_type : {"CREATE", "UPDATE", "DELETE", "ROLLBACK"},
        change_description : STRING,
        diff : Seq([
            operation : {"ADD", "MODIFY", "REMOVE"},
            path : STRING,
            old_value : Any,
            new_value : Any
        ])
    ]),
    current_version : Nat
]

\* Create new version
CreateNewVersion(history, updated_config, author, description) ==
    LET new_version_number == history.current_version + 1
        current_config == history.versions[history.current_version].configuration
        
        \* Compute diff
        diff == ComputeConfigDiff(current_config, updated_config)
        
        new_version == [
            version_number |-> new_version_number,
            configuration |-> updated_config,
            timestamp |-> CurrentTime,
            author |-> author,
            change_type |-> "UPDATE",
            change_description |-> description,
            diff |-> diff
        ]
    IN [history EXCEPT
           !.versions = Append(@, new_version),
           !.current_version = new_version_number]

\* Compute configuration diff
ComputeConfigDiff(old_config, new_config) ==
    LET old_params == DOMAIN old_config.values
        new_params == DOMAIN new_config.values
        
        \* Added parameters
        added == new_params \ old_params
        added_diffs == [p \in added |->
            [operation |-> "ADD",
             path |-> p,
             old_value |-> Null,
             new_value |-> new_config.values[p]]]
        
        \* Removed parameters
        removed == old_params \ new_params
        removed_diffs == [p \in removed |->
            [operation |-> "REMOVE",
             path |-> p,
             old_value |-> old_config.values[p],
             new_value |-> Null]]
        
        \* Modified parameters
        common == old_params \intersect new_params
        modified == {p \in common : old_config.values[p] # new_config.values[p]}
        modified_diffs == [p \in modified |->
            [operation |-> "MODIFY",
             path |-> p,
             old_value |-> old_config.values[p],
             new_value |-> new_config.values[p]]]
    IN added_diffs \union removed_diffs \union modified_diffs

\* Rollback to previous version
RollbackConfiguration(history, target_version) ==
    IF target_version <= Len(history.versions)
    THEN LET target_config == history.versions[target_version].configuration
             rollback_version == [
                 version_number |-> history.current_version + 1,
                 configuration |-> target_config,
                 timestamp |-> CurrentTime,
                 author |-> "SYSTEM",
                 change_type |-> "ROLLBACK",
                 change_description |-> "Rollback to version " \o ToString(target_version),
                 diff |-> ComputeConfigDiff(
                     history.versions[history.current_version].configuration,
                     target_config)
             ]
         IN [history EXCEPT
                !.versions = Append(@, rollback_version),
                !.current_version = @ + 1]
    ELSE history

(****************************************************************************)
(* Template-Based Configuration                                             *)
(****************************************************************************)

\* Configuration template
ConfigTemplate == [
    template_id : STRING,
    template_name : STRING,
    schema_id : STRING,
    
    \* Base configuration
    base_values : [STRING -> Any],
    
    \* Template variables
    variables : [STRING -> [
        variable_type : ConfigValueType,
        default_value : Any,
        description : STRING
    ]],
    
    \* Template expressions
    expressions : [STRING -> [
        expression_type : {"VALUE", "FUNCTION", "REFERENCE"},
        expression : Any
    ]],
    
    \* Metadata
    category : STRING,
    tags : SUBSET STRING
]

\* Instantiate template
InstantiateTemplate(template, variable_values) ==
    LET 
        \* Merge base values with variable values
        RECURSIVE EvaluateExpressions(_, _)
        EvaluateExpressions(remaining_params, accumulated) ==
            IF remaining_params = {}
            THEN accumulated
            ELSE LET param == CHOOSE p \in remaining_params : TRUE
                     expr == template.expressions[param]
                     value == EvaluateExpression(expr, variable_values, accumulated)
                 IN EvaluateExpressions(
                        remaining_params \ {param},
                        accumulated @@ (param :> value))
        
        base_with_vars == template.base_values @@ variable_values
        final_values == EvaluateExpressions(DOMAIN template.expressions, base_with_vars)
    IN [
        config_id |-> GenerateConfigId,
        schema_id |-> template.schema_id,
        version |-> 1,
        values |-> final_values,
        created_at |-> CurrentTime,
        modified_at |-> CurrentTime,
        created_by |-> "TEMPLATE",
        modified_by |-> "TEMPLATE",
        status |-> "DRAFT",
        validation_errors |-> <<>>,
        parent_version |-> 0,
        change_description |-> "Instantiated from template " \o template.template_name
    ]

\* Evaluate template expression
EvaluateExpression(expr, variables, context) ==
    CASE expr.expression_type = "VALUE" ->
        expr.expression
    [] expr.expression_type = "REFERENCE" ->
        variables[expr.expression.variable_name]
    [] expr.expression_type = "FUNCTION" ->
        ApplyFunction(expr.expression.function_name,
                     expr.expression.arguments,
                     variables,
                     context)

(****************************************************************************)
(* Dynamic Reconfiguration                                                  *)
(****************************************************************************)

\* Reconfiguration strategy
ReconfigurationStrategy == [
    strategy_type : {"IMMEDIATE", "GRACEFUL", "PHASED", "BLUE_GREEN", "CANARY"},
    
    \* Validation
    pre_validation : BOOLEAN,
    post_validation : BOOLEAN,
    
    \* Rollback
    auto_rollback : BOOLEAN,
    rollback_threshold : [
        error_rate : Real,
        latency_increase : Real
    ],
    
    \* Phases (for PHASED strategy)
    phases : Seq([
        phase_name : STRING,
        duration : Nat,
        affected_components : SUBSET STRING,
        health_checks : Seq(STRING)
    ])
]

\* Apply dynamic reconfiguration
ApplyDynamicReconfiguration(current_config, new_config, strategy) ==
    LET 
        \* Pre-validation
        pre_valid == IF strategy.pre_validation
                    THEN ValidateConfiguration(new_config, schema).valid
                    ELSE TRUE
    IN IF ~pre_valid
       THEN [success |-> FALSE, error |-> "Pre-validation failed"]
       ELSE CASE strategy.strategy_type = "IMMEDIATE" ->
               ApplyImmediate(current_config, new_config)
            [] strategy.strategy_type = "GRACEFUL" ->
               ApplyGraceful(current_config, new_config)
            [] strategy.strategy_type = "PHASED" ->
               ApplyPhased(current_config, new_config, strategy.phases)
            [] strategy.strategy_type = "BLUE_GREEN" ->
               ApplyBlueGreen(current_config, new_config)
            [] strategy.strategy_type = "CANARY" ->
               ApplyCanary(current_config, new_config)

\* Apply immediate reconfiguration
ApplyImmediate(current_config, new_config) ==
    [
        success |-> TRUE,
        new_configuration |-> new_config,
        rollback_point |-> current_config
    ]

\* Apply graceful reconfiguration
ApplyGraceful(current_config, new_config) ==
    LET 
        \* Identify hot-reloadable parameters
        hot_reload_params == {p \in DOMAIN new_config.values :
            ~schema.parameters[p].requires_restart}
        
        \* Apply hot-reloadable changes first
        intermediate_config == [current_config EXCEPT
            !.values = [p \in DOMAIN @ |->
                IF p \in hot_reload_params
                THEN new_config.values[p]
                ELSE @[p]]]
        
        \* Schedule restart for remaining changes
        requires_restart == DOMAIN new_config.values \ hot_reload_params # {}
    IN [
        success |-> TRUE,
        new_configuration |-> intermediate_config,
        requires_restart |-> requires_restart,
        pending_changes |-> IF requires_restart
                           THEN {p \in DOMAIN new_config.values :
                                   p \notin hot_reload_params}
                           ELSE {}
    ]

(****************************************************************************)
(* Configuration Drift Detection                                            *)
(****************************************************************************)

\* Detect configuration drift
DetectConfigurationDrift(expected_config, actual_config) ==
    LET diff == ComputeConfigDiff(expected_config, actual_config)
        
        \* Categorize drifts
        critical_drifts == {d \in diff :
            schema.parameters[d.path].sensitivity = "SECRET" \/
            schema.parameters[d.path].required}
        
        non_critical_drifts == diff \ critical_drifts
    IN [
        has_drift |-> diff # {},
        drift_count |-> Cardinality(diff),
        critical_drifts |-> critical_drifts,
        non_critical_drifts |-> non_critical_drifts,
        drift_score |-> ComputeDriftScore(diff)
    ]

\* Compute drift score
ComputeDriftScore(drifts) ==
    LET weights == [
            "ADD" |-> 1.0,
            "REMOVE" |-> 2.0,
            "MODIFY" |-> 0.5
        ]
        
        weighted_sum == Sum({weights[d.operation] : d \in drifts})
        max_score == Cardinality(drifts) * 2.0
    IN IF max_score = 0
       THEN 0.0
       ELSE (weighted_sum / max_score) * 100.0

(****************************************************************************)
(* Automated Remediation                                                    *)
(****************************************************************************)

\* Remediation action
RemediationAction == [
    action_id : STRING,
    action_type : {"APPLY_DEFAULT", "APPLY_TEMPLATE", "NOTIFY", "ROLLBACK", "CUSTOM"},
    
    \* Trigger conditions
    triggers : Seq([
        condition_type : {"VALIDATION_ERROR", "DRIFT_DETECTED",
                         "POLICY_VIOLATION", "THRESHOLD_EXCEEDED"},
        condition_parameters : [STRING -> Any]
    ]),
    
    \* Action parameters
    parameters : [STRING -> Any],
    
    \* Safety
    require_approval : BOOLEAN,
    dry_run_first : BOOLEAN
]

\* Execute automated remediation
ExecuteAutomatedRemediation(config, violation, remediation_action) ==
    IF remediation_action.require_approval
    THEN [
        success |-> FALSE,
        requires_approval |-> TRUE,
        proposed_action |-> remediation_action
    ]
    ELSE LET 
            result == CASE remediation_action.action_type = "APPLY_DEFAULT" ->
                         ApplyDefaultValues(config, violation)
                      [] remediation_action.action_type = "APPLY_TEMPLATE" ->
                         ApplyRemediationTemplate(config, remediation_action.parameters)
                      [] remediation_action.action_type = "ROLLBACK" ->
                         RollbackToLastValid(config)
                      [] OTHER -> [success |-> FALSE, error |-> "Unknown action type"]
         IN result

(****************************************************************************)
(* Configuration Management Properties and Invariants                       *)
(****************************************************************************)

\* Configuration validity
THEOREM ConfigurationValidity ==
    \A config \in ActiveConfigurations :
        config.status = "ACTIVE" =>
            ValidateConfiguration(config, schema).valid

\* Policy consistency
THEOREM PolicyConsistency ==
    \A p1, p2 \in Policies :
        (p1 # p2 /\ p1.status = "ACTIVE" /\ p2.status = "ACTIVE") =>
            ~HasPolicyConflict(p1, p2)

\* Rollback safety
THEOREM RollbackSafety ==
    \A history \in ConfigurationHistories, version \in Nat :
        (version <= Len(history.versions)) =>
            ValidConfiguration(history.versions[version].configuration)

\* Drift remediation
THEOREM DriftRemediation ==
    \A config \in Configurations :
        HasDrift(config) /\ AutoRemediationEnabled =>
            EventuallyConverges(config, expected_config)

====

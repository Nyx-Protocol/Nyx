#!/bin/bash
# Batch fix common TLA+ errors

cd "$(dirname "$0")"

echo "======================================"
echo "Batch Fixing TLA+ Modules"
echo "======================================"

# List of modules to fix (excluding already working ones)
MODULES=(
    "NyxAPISpecification"
    "NyxAdvancedOptimization"
    "NyxAdvancedRouting"
    "NyxConcurrencyModels"
    "NyxConfigurationValidation"
    "NyxControlPlane"
    "NyxCryptography"
    "NyxDataPlane"
    "NyxDeployment"
    "NyxDetailedProofs"
    "NyxDistributedConsensus"
    "NyxEdgeComputing"
    "NyxErrorHandling"
    "NyxFaultTolerance"
    "NyxMasterProofs"
    "NyxMobilityManagement"
    "NyxMonitoring"
    "NyxNFVAndSDN"
    "NyxPerformanceModels"
    "NyxProtocolIntegration"
    "NyxQoSManagement"
    "NyxSecurityAudit"
    "NyxSecurityProperties"
    "NyxSimulation"
    "NyxStorageLayer"
    "NyxStreamManagement"
    "NyxTestingFramework"
    "NyxTimeSensitiveNetworking"
)

for module in "${MODULES[@]}"; do
    file="${module}.tla"
    
    if [ ! -f "$file" ]; then
        continue
    fi
    
    echo "Fixing $file..."
    
    # Add NyxHelpers instance if not present
    if ! grep -q "INSTANCE NyxHelpers" "$file"; then
        # Find line after module declaration
        sed -i '/^----.*MODULE.*----$/a LOCAL INSTANCE NyxHelpers' "$file"
    fi
    
done

echo ""
echo "======================================"
echo "Batch fix complete!"
echo "======================================"

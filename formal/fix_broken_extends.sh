#!/bin/bash
# Fix broken EXTENDS lines in modified modules

cd "$(dirname "$0")"

echo "Fixing broken EXTENDS lines..."

# NyxDistributedConsensus
if [ -f "NyxDistributedConsensus.tla" ]; then
    echo "  Fixing NyxDistributedConsensus.tla..."
    sed -i '/^EXTENDS.*TLC,$/,/^[[:space:]]*Nyx/ {
        /^EXTENDS/ { s/,$/  /; b }
        /^LOCAL INSTANCE/ b
        d
    }' NyxDistributedConsensus.tla
fi

# NyxEdgeComputing
if [ -f "NyxEdgeComputing.tla" ]; then
    echo "  Fixing NyxEdgeComputing.tla..."
    sed -i '/^EXTENDS.*TLC,$/,/^[[:space:]]*Nyx/ {
        /^EXTENDS/ { s/,$/  /; b }
        /^LOCAL INSTANCE/ b
        d
    }' NyxEdgeComputing.tla
fi

# NyxFaultTolerance
if [ -f "NyxFaultTolerance.tla" ]; then
    echo "  Fixing NyxFaultTolerance.tla..."
    sed -i '/^EXTENDS.*TLC,$/,/^[[:space:]]*Nyx/ {
        /^EXTENDS/ { s/,$/  /; b }
        /^LOCAL INSTANCE/ b
        d
    }' NyxFaultTolerance.tla
fi

# NyxMobilityManagement
if [ -f "NyxMobilityManagement.tla" ]; then
    echo "  Fixing NyxMobilityManagement.tla..."
    sed -i '/^EXTENDS.*TLC,$/,/^[[:space:]]*Nyx/ {
        /^EXTENDS/ { s/,$/  /; b }
        /^LOCAL INSTANCE/ b
        d
    }' NyxMobilityManagement.tla
fi

# NyxMonitoring
if [ -f "NyxMonitoring.tla" ]; then
    echo "  Fixing NyxMonitoring.tla..."
    sed -i '/^EXTENDS.*TLC,$/,/^[[:space:]]*Nyx/ {
        /^EXTENDS/ { s/,$/  /; b }
        /^LOCAL INSTANCE/ b
        d
    }' NyxMonitoring.tla
fi

# NyxPerformanceModels
if [ -f "NyxPerformanceModels.tla" ]; then
    echo "  Fixing NyxPerformanceModels.tla..."
    sed -i '/^EXTENDS.*TLC,$/,/^[[:space:]]*Nyx/ {
        /^EXTENDS/ { s/,$/  /; b }
        /^LOCAL INSTANCE/ b
        d
    }' NyxPerformanceModels.tla
fi

# NyxQoSManagement
if [ -f "NyxQoSManagement.tla" ]; then
    echo "  Fixing NyxQoSManagement.tla..."
    sed -i '/^EXTENDS.*TLC,$/,/^[[:space:]]*Nyx/ {
        /^EXTENDS/ { s/,$/  /; b }
        /^LOCAL INSTANCE/ b
        d
    }' NyxQoSManagement.tla
fi

# NyxSecurityAudit
if [ -f "NyxSecurityAudit.tla" ]; then
    echo "  Fixing NyxSecurityAudit.tla..."
    sed -i '/^EXTENDS.*TLC,$/,/^[[:space:]]*Nyx/ {
        /^EXTENDS/ { s/,$/  /; b }
        /^LOCAL INSTANCE/ b
        d
    }' NyxSecurityAudit.tla
fi

# NyxTestingFramework
if [ -f "NyxTestingFramework.tla" ]; then
    echo "  Fixing NyxTestingFramework.tla..."
    sed -i '/^EXTENDS.*TLC,$/,/^[[:space:]]*Nyx/ {
        /^EXTENDS/ { s/,$/  /; b }
        /^LOCAL INSTANCE/ b
        d
    }' NyxTestingFramework.tla
fi

echo "Done!"

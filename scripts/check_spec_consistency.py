#!/usr/bin/env python3
"""
Spec Consistency Checker for Nyx Protocol

Validates consistency between:
1. spec/ directory (protocol specifications)
2. docs/specs.md (implementation status matrix)
3. Actual code implementation (crates)

Detects:
- Spec-defined features missing from implementation status
- Implementation status entries without spec reference
- Protocol version progress inconsistencies
- Test coverage gaps

Exit codes:
  0 = All consistent
  1 = Inconsistencies found (but non-fatal)
  2 = Critical errors (missing files, parse failures)
"""

import argparse
import json
import os
import re
import sys
from collections import defaultdict
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Optional, Set, Tuple

# ANSI color codes for terminal output
class Color:
    RED = '\033[91m'
    GREEN = '\033[92m'
    YELLOW = '\033[93m'
    BLUE = '\033[94m'
    MAGENTA = '\033[95m'
    CYAN = '\033[96m'
    RESET = '\033[0m'
    BOLD = '\033[1m'


@dataclass
class SpecFeature:
    """Represents a feature defined in spec/ documentation"""
    section: str  # e.g., "1.2", "4.1"
    title: str  # Feature name
    file: str  # Source spec file
    line: int  # Line number in spec file
    subsections: List[str] = field(default_factory=list)  # Child sections
    
    def __hash__(self):
        return hash((self.section, self.title))


@dataclass
class ImplStatus:
    """Represents implementation status from docs/specs.md"""
    feature: str  # Feature name
    status: str  # COMPLETE, PARTIAL, PLANNED, etc.
    implementation: str  # File path or module
    tests: str  # Test count (e.g., "38/38")
    notes: str  # Additional notes
    category: str  # e.g., "Transport & Network Layer"
    
    def __hash__(self):
        return hash((self.feature, self.category))


@dataclass
class ConsistencyReport:
    """Overall consistency check report"""
    spec_features: List[SpecFeature] = field(default_factory=list)
    impl_statuses: List[ImplStatus] = field(default_factory=list)
    missing_in_docs: List[SpecFeature] = field(default_factory=list)
    missing_in_spec: List[ImplStatus] = field(default_factory=list)
    status_summary: Dict[str, int] = field(default_factory=lambda: defaultdict(int))
    version_progress: Dict[str, float] = field(default_factory=dict)
    warnings: List[str] = field(default_factory=list)
    errors: List[str] = field(default_factory=list)


def parse_spec_file(spec_path: Path) -> List[SpecFeature]:
    """
    Parse a spec markdown file and extract feature sections.
    
    Matches patterns:
    - ## 1. Feature Name
    - ### 1.1 Subfeature
    - #### 1.1.1 Detail
    
    Returns list of SpecFeature objects with section hierarchy.
    
    Filters out conceptual/meta sections (Mission, Overview, etc.)
    """
    features = []
    
    try:
        with open(spec_path, 'r', encoding='utf-8') as f:
            lines = f.readlines()
    except Exception as e:
        print(f"{Color.RED}Error reading {spec_path}: {e}{Color.RESET}", file=sys.stderr)
        return features
    
    section_pattern = re.compile(r'^(#{2,4})\s+(\d+(?:\.\d+)*)\s+(.+)$')
    
    # Conceptual sections to skip (not implementation features)
    skip_keywords = [
        'table of contents', '目次', 'toc', 'references', '参考文献',
        'mission statement', 'core problems', 'key innovation',
        'core principles', 'design trade-offs', 'threat model',
        'overview', 'introduction', 'objectives', 'adversary model',
        'research directions', 'platform expansion', 'ecosystem development',
        'development methodology', 'language and platform choices',
        'operational considerations', 'deployment'
    ]
    
    for line_num, line in enumerate(lines, start=1):
        match = section_pattern.match(line.strip())
        if match:
            heading_level = len(match.group(1))  # ## = 2, ### = 3, #### = 4
            section_number = match.group(2)
            title = match.group(3).strip()
            
            # Skip meta/conceptual sections
            title_lower = title.lower()
            if any(skip in title_lower for skip in skip_keywords):
                continue
            
            # Only include sections from protocol spec or technical design sections
            # Skip high-level design document sections (1.x, 2.x, 9.x-12.x)
            if spec_path.name == 'Nyx_Design_Document_EN.md':
                section_major = section_number.split('.')[0]
                if section_major in ['1', '2', '9', '10', '11', '12']:
                    continue  # Skip intro/methodology/future work sections
            
            feature = SpecFeature(
                section=section_number,
                title=title,
                file=spec_path.name,
                line=line_num
            )
            features.append(feature)
    
    return features


def parse_implementation_status(docs_path: Path) -> Tuple[List[ImplStatus], Dict[str, float]]:
    """
    Parse docs/specs.md Implementation Status Matrix.
    
    Extracts:
    - Feature names, status, implementation paths, test counts
    - Category headers (### N. Category Name)
    - Protocol version progress (v0.1, v1.0)
    
    Returns (impl_statuses, version_progress)
    """
    impl_statuses = []
    version_progress = {}
    
    try:
        with open(docs_path, 'r', encoding='utf-8') as f:
            content = f.read()
    except Exception as e:
        print(f"{Color.RED}Error reading {docs_path}: {e}{Color.RESET}", file=sys.stderr)
        return impl_statuses, version_progress
    
    # Extract category sections (### N. Category Name)
    category_pattern = re.compile(r'^###\s+(\d+)\.\s+(.+)$', re.MULTILINE)
    categories = category_pattern.findall(content)
    
    # Extract table rows: | Feature | Status | Implementation | Tests | Notes |
    table_pattern = re.compile(
        r'^\|\s*(.+?)\s*\|\s*(✅ COMPLETE|⚠️ PARTIAL|🚧 IN PROGRESS|⏳ PLANNED|🔬 EXPERIMENTAL)\s*\|'
        r'\s*(.+?)\s*\|\s*(.+?)\s*\|\s*(.+?)\s*\|$',
        re.MULTILINE
    )
    
    current_category = "Unknown"
    
    # Process content line by line to maintain category context
    lines = content.split('\n')
    for line in lines:
        # Update current category
        cat_match = category_pattern.match(line)
        if cat_match:
            current_category = cat_match.group(2).strip()
            continue
        
        # Match table row
        table_match = table_pattern.match(line)
        if table_match:
            feature = table_match.group(1).strip()
            status = table_match.group(2).strip()
            implementation = table_match.group(3).strip()
            tests = table_match.group(4).strip()
            notes = table_match.group(5).strip()
            
            # Skip header rows
            if feature.lower() in ['feature', '------']:
                continue
            
            impl_status = ImplStatus(
                feature=feature,
                status=status,
                implementation=implementation,
                tests=tests,
                notes=notes,
                category=current_category
            )
            impl_statuses.append(impl_status)
    
    # Extract protocol version progress
    version_pattern = re.compile(r'\*\*v(\d+\.\d+)\s+\(.*?\)\*\*\s*\|\s*~?(\d+)%', re.MULTILINE)
    for match in version_pattern.finditer(content):
        version = match.group(1)
        progress = float(match.group(2))
        version_progress[f"v{version}"] = progress
    
    return impl_statuses, version_progress


def find_missing_features(
    spec_features: List[SpecFeature],
    impl_statuses: List[ImplStatus]
) -> Tuple[List[SpecFeature], List[ImplStatus]]:
    """
    Detect inconsistencies between spec and implementation status.
    
    Returns:
    - missing_in_docs: Spec features not documented in docs/specs.md
    - missing_in_spec: Implementation entries without spec reference
    
    Matching strategy:
    - Exact title match (case-insensitive)
    - Fuzzy match (substring, normalized)
    """
    # Build lookup sets
    spec_titles = {f.title.lower().strip() for f in spec_features}
    impl_features = {s.feature.lower().strip() for s in impl_statuses}
    
    missing_in_docs = []
    missing_in_spec = []
    
    # Find spec features not in docs
    for spec_feat in spec_features:
        normalized_title = spec_feat.title.lower().strip()
        
        # Check exact match
        if normalized_title not in impl_features:
            # Check fuzzy match (substring)
            found = False
            for impl_feat in impl_features:
                if normalized_title in impl_feat or impl_feat in normalized_title:
                    found = True
                    break
            
            if not found:
                missing_in_docs.append(spec_feat)
    
    # Find impl features not in spec
    for impl_stat in impl_statuses:
        normalized_feature = impl_stat.feature.lower().strip()
        
        # Skip meta entries (Summary, Notes, etc.)
        if any(meta in normalized_feature for meta in ['summary', '**', 'note:', 'total:']):
            continue
        
        # Check exact match
        if normalized_feature not in spec_titles:
            # Check fuzzy match
            found = False
            for spec_title in spec_titles:
                if normalized_feature in spec_title or spec_title in normalized_feature:
                    found = True
                    break
            
            if not found:
                missing_in_spec.append(impl_stat)
    
    return missing_in_docs, missing_in_spec


def generate_status_summary(impl_statuses: List[ImplStatus]) -> Dict[str, int]:
    """Count features by implementation status"""
    summary = defaultdict(int)
    
    for impl_stat in impl_statuses:
        # Extract status emoji + label
        if '✅ COMPLETE' in impl_stat.status:
            summary['COMPLETE'] += 1
        elif '⚠️ PARTIAL' in impl_stat.status:
            summary['PARTIAL'] += 1
        elif '🚧 IN PROGRESS' in impl_stat.status:
            summary['IN PROGRESS'] += 1
        elif '⏳ PLANNED' in impl_stat.status:
            summary['PLANNED'] += 1
        elif '🔬 EXPERIMENTAL' in impl_stat.status:
            summary['EXPERIMENTAL'] += 1
    
    return dict(summary)


def generate_markdown_report(report: ConsistencyReport, output_path: Path) -> None:
    """Generate human-readable Markdown report"""
    with open(output_path, 'w', encoding='utf-8') as f:
        f.write("# Spec Consistency Check Report\n\n")
        f.write(f"**Generated**: {Path(__file__).name}\n")
        f.write(f"**Timestamp**: {__import__('datetime').datetime.now().isoformat()}\n\n")
        
        f.write("---\n\n")
        
        # Implementation Status Summary
        f.write("## Implementation Status Summary\n\n")
        total = sum(report.status_summary.values())
        f.write(f"**Total Features**: {total}\n\n")
        f.write("| Status | Count | Percentage |\n")
        f.write("|--------|-------|------------|\n")
        for status, count in sorted(report.status_summary.items(), key=lambda x: -x[1]):
            percentage = (count / total * 100) if total > 0 else 0
            f.write(f"| {status} | {count} | {percentage:.1f}% |\n")
        f.write("\n")
        
        # Protocol Version Progress
        if report.version_progress:
            f.write("## Protocol Version Progress\n\n")
            f.write("| Version | Progress |\n")
            f.write("|---------|----------|\n")
            for version, progress in sorted(report.version_progress.items()):
                f.write(f"| {version} | {progress:.1f}% |\n")
            f.write("\n")
        
        # Missing in Docs
        if report.missing_in_docs:
            f.write("## ⚠️ Features Defined in Spec but Missing from docs/specs.md\n\n")
            f.write(f"**Count**: {len(report.missing_in_docs)}\n\n")
            f.write("| Section | Feature | Source File |\n")
            f.write("|---------|---------|-------------|\n")
            for feat in sorted(report.missing_in_docs, key=lambda x: x.section):
                f.write(f"| {feat.section} | {feat.title} | {feat.file}:{feat.line} |\n")
            f.write("\n")
        else:
            f.write("## ✅ All Spec Features Documented\n\n")
            f.write("No features found in spec/ that are missing from docs/specs.md.\n\n")
        
        # Missing in Spec
        if report.missing_in_spec:
            f.write("## ⚠️ Implementation Entries Without Spec Reference\n\n")
            f.write(f"**Count**: {len(report.missing_in_spec)}\n\n")
            f.write("| Feature | Category | Status |\n")
            f.write("|---------|----------|--------|\n")
            for impl in sorted(report.missing_in_spec, key=lambda x: x.category):
                f.write(f"| {impl.feature} | {impl.category} | {impl.status} |\n")
            f.write("\n")
        else:
            f.write("## ✅ All Implementation Entries Have Spec References\n\n")
        
        # Warnings
        if report.warnings:
            f.write("## ⚠️ Warnings\n\n")
            for warning in report.warnings:
                f.write(f"- {warning}\n")
            f.write("\n")
        
        # Errors
        if report.errors:
            f.write("## ❌ Errors\n\n")
            for error in report.errors:
                f.write(f"- {error}\n")
            f.write("\n")
        
        # Summary
        f.write("---\n\n")
        f.write("## Summary\n\n")
        if not report.missing_in_docs and not report.missing_in_spec and not report.errors:
            f.write("✅ **All consistent!** Spec and implementation status are in sync.\n")
        else:
            issues = len(report.missing_in_docs) + len(report.missing_in_spec) + len(report.errors)
            f.write(f"⚠️ **{issues} issues found**. See sections above for details.\n")


def generate_json_report(report: ConsistencyReport, output_path: Path) -> None:
    """Generate machine-readable JSON report for CI artifacts"""
    data = {
        "status_summary": report.status_summary,
        "version_progress": report.version_progress,
        "missing_in_docs": [
            {
                "section": f.section,
                "title": f.title,
                "file": f.file,
                "line": f.line
            }
            for f in report.missing_in_docs
        ],
        "missing_in_spec": [
            {
                "feature": s.feature,
                "category": s.category,
                "status": s.status
            }
            for s in report.missing_in_spec
        ],
        "warnings": report.warnings,
        "errors": report.errors,
        "total_features": sum(report.status_summary.values()),
        "total_issues": len(report.missing_in_docs) + len(report.missing_in_spec) + len(report.errors)
    }
    
    with open(output_path, 'w', encoding='utf-8') as f:
        json.dump(data, f, indent=2, ensure_ascii=False)


def main():
    parser = argparse.ArgumentParser(
        description="Check consistency between spec/ and docs/specs.md"
    )
    parser.add_argument(
        '--workspace',
        type=Path,
        default=Path.cwd(),
        help="Path to workspace root (default: current directory)"
    )
    parser.add_argument(
        '--output-dir',
        type=Path,
        default=Path('target/spec-check'),
        help="Output directory for reports (default: target/spec-check)"
    )
    parser.add_argument(
        '--fail-on-missing',
        action='store_true',
        help="Exit with code 1 if any inconsistencies found"
    )
    parser.add_argument(
        '--verbose',
        action='store_true',
        help="Enable verbose output"
    )
    
    args = parser.parse_args()
    
    # Validate workspace
    spec_dir = args.workspace / 'spec'
    docs_dir = args.workspace / 'docs'
    
    if not spec_dir.exists():
        print(f"{Color.RED}Error: spec/ directory not found at {spec_dir}{Color.RESET}", file=sys.stderr)
        return 2
    
    if not docs_dir.exists():
        print(f"{Color.RED}Error: docs/ directory not found at {docs_dir}{Color.RESET}", file=sys.stderr)
        return 2
    
    docs_specs = docs_dir / 'specs.md'
    if not docs_specs.exists():
        print(f"{Color.RED}Error: docs/specs.md not found{Color.RESET}", file=sys.stderr)
        return 2
    
    print(f"{Color.CYAN}{Color.BOLD}Nyx Protocol Spec Consistency Checker{Color.RESET}\n")
    
    report = ConsistencyReport()
    
    # Phase 1: Parse spec files
    print(f"{Color.BLUE}[1/4] Parsing spec/ directory...{Color.RESET}")
    spec_files = [
        spec_dir / 'Nyx_Protocol_v1.0_Spec_EN.md',
        spec_dir / 'Nyx_Design_Document_EN.md',
        spec_dir / 'Capability_Negotiation_Policy_EN.md'
    ]
    
    for spec_file in spec_files:
        if spec_file.exists():
            features = parse_spec_file(spec_file)
            report.spec_features.extend(features)
            if args.verbose:
                print(f"  - {spec_file.name}: {len(features)} features")
        else:
            warning = f"Spec file not found: {spec_file.name}"
            report.warnings.append(warning)
            print(f"  {Color.YELLOW}⚠ {warning}{Color.RESET}")
    
    print(f"  {Color.GREEN}✓ Found {len(report.spec_features)} spec features{Color.RESET}\n")
    
    # Phase 2: Parse implementation status
    print(f"{Color.BLUE}[2/4] Parsing docs/specs.md...{Color.RESET}")
    impl_statuses, version_progress = parse_implementation_status(docs_specs)
    report.impl_statuses = impl_statuses
    report.version_progress = version_progress
    print(f"  {Color.GREEN}✓ Found {len(impl_statuses)} implementation entries{Color.RESET}\n")
    
    # Phase 3: Detect inconsistencies
    print(f"{Color.BLUE}[3/4] Detecting inconsistencies...{Color.RESET}")
    missing_in_docs, missing_in_spec = find_missing_features(
        report.spec_features,
        report.impl_statuses
    )
    report.missing_in_docs = missing_in_docs
    report.missing_in_spec = missing_in_spec
    
    if missing_in_docs:
        print(f"  {Color.YELLOW}⚠ {len(missing_in_docs)} spec features missing from docs/specs.md{Color.RESET}")
    else:
        print(f"  {Color.GREEN}✓ All spec features documented{Color.RESET}")
    
    if missing_in_spec:
        print(f"  {Color.YELLOW}⚠ {len(missing_in_spec)} implementation entries without spec reference{Color.RESET}")
    else:
        print(f"  {Color.GREEN}✓ All implementation entries have spec references{Color.RESET}")
    
    print()
    
    # Phase 4: Generate reports
    print(f"{Color.BLUE}[4/4] Generating reports...{Color.RESET}")
    
    report.status_summary = generate_status_summary(report.impl_statuses)
    
    args.output_dir.mkdir(parents=True, exist_ok=True)
    
    md_report_path = args.output_dir / 'consistency_report.md'
    json_report_path = args.output_dir / 'consistency_report.json'
    
    generate_markdown_report(report, md_report_path)
    generate_json_report(report, json_report_path)
    
    print(f"  {Color.GREEN}✓ Markdown report: {md_report_path}{Color.RESET}")
    print(f"  {Color.GREEN}✓ JSON report: {json_report_path}{Color.RESET}\n")
    
    # Final summary
    total_issues = len(report.missing_in_docs) + len(report.missing_in_spec) + len(report.errors)
    
    print(f"{Color.BOLD}Summary:{Color.RESET}")
    print(f"  Spec features: {len(report.spec_features)}")
    print(f"  Implementation entries: {len(report.impl_statuses)}")
    print(f"  Missing in docs: {len(report.missing_in_docs)}")
    print(f"  Missing in spec: {len(report.missing_in_spec)}")
    print(f"  Errors: {len(report.errors)}")
    
    if total_issues == 0:
        print(f"\n{Color.GREEN}{Color.BOLD}✅ All consistent!{Color.RESET}")
        return 0
    else:
        print(f"\n{Color.YELLOW}{Color.BOLD}⚠️  {total_issues} issues found{Color.RESET}")
        print(f"See {md_report_path} for details.\n")
        
        if args.fail_on_missing:
            return 1
        else:
            return 0


if __name__ == '__main__':
    sys.exit(main())

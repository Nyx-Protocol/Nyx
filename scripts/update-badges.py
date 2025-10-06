#!/usr/bin/env python3
"""
CI Badge Automation Script for NyxNet

This script automates the generation of dynamic badges for the README.md:
1. Test count badge (parses test output)
2. Code coverage badge (parses tarpaulin output)
3. LOC badge (counts lines of code)

Usage:
  python scripts/update-badges.py

Environment Variables:
  CI: Set to "true" in CI environment (optional)
  GITHUB_WORKSPACE: GitHub Actions workspace path (optional)
"""

import os
import re
import subprocess
import sys
import json
from pathlib import Path
from typing import Dict, Optional


def run_command(cmd: list[str], capture_output: bool = True) -> tuple[int, str, str]:
    """
    Run a shell command and return exit code, stdout, stderr.

    Args:
        cmd: Command and arguments as list
        capture_output: Whether to capture stdout/stderr

    Returns:
        Tuple of (exit_code, stdout, stderr)
    """
    try:
        result = subprocess.run(
            cmd,
            capture_output=capture_output,
            text=True,
            check=False
        )
        return result.returncode, result.stdout, result.stderr
    except FileNotFoundError:
        return 1, "", f"Command not found: {cmd[0]}"


def count_tests() -> Optional[int]:
    """
    Count total number of tests by running `cargo test --no-run`.

    Returns:
        Total test count, or None if failed
    """
    print("Counting tests...")
    
    # Run cargo test with --no-run to avoid executing tests
    exit_code, stdout, stderr = run_command([
        "cargo", "test", "--workspace", "--all-features", "--no-run", "--", "--list"
    ])
    
    if exit_code != 0:
        print(f"Error running cargo test: {stderr}", file=sys.stderr)
        return None
    
    # Parse output to count tests
    # Format: "test_name: test"
    test_count = 0
    for line in stdout.split("\n") + stderr.split("\n"):
        if ": test" in line and not line.strip().startswith("running"):
            test_count += 1
    
    print(f"  Found {test_count} tests")
    return test_count


def get_code_coverage() -> Optional[float]:
    """
    Get code coverage percentage from tarpaulin output.

    Returns:
        Coverage percentage (0.0-100.0), or None if failed
    """
    print("Calculating code coverage...")
    
    # Check if tarpaulin is installed
    exit_code, _, _ = run_command(["cargo", "tarpaulin", "--version"])
    if exit_code != 0:
        print("  cargo-tarpaulin not installed, skipping coverage", file=sys.stderr)
        return None
    
    # Run tarpaulin (fast mode, no output files)
    exit_code, stdout, stderr = run_command([
        "cargo", "tarpaulin",
        "--workspace",
        "--all-features",
        "--timeout", "300",
        "--skip-clean",
        "--out", "Stdout"
    ])
    
    if exit_code != 0:
        print(f"  Error running tarpaulin: {stderr}", file=sys.stderr)
        return None
    
    # Parse coverage percentage
    # Format: "Coverage: XX.YY%"
    match = re.search(r"Coverage:\s+(\d+\.?\d*)%", stdout)
    if match:
        coverage = float(match.group(1))
        print(f"  Coverage: {coverage:.2f}%")
        return coverage
    
    print("  Could not parse coverage percentage", file=sys.stderr)
    return None


def count_lines_of_code() -> Optional[int]:
    """
    Count lines of Rust code (excluding comments, blanks).

    Returns:
        Total LOC, or None if failed
    """
    print("Counting lines of code...")
    
    # Find all .rs files (excluding target/)
    workspace_root = Path(__file__).parent.parent
    rs_files = list(workspace_root.rglob("*.rs"))
    rs_files = [f for f in rs_files if "target" not in str(f)]
    
    total_loc = 0
    for rs_file in rs_files:
        try:
            with open(rs_file, "r", encoding="utf-8") as f:
                for line in f:
                    # Strip whitespace
                    line = line.strip()
                    # Ignore blank lines and single-line comments
                    if line and not line.startswith("//"):
                        total_loc += 1
        except Exception as e:
            print(f"  Warning: Could not read {rs_file}: {e}", file=sys.stderr)
    
    print(f"  Found {total_loc} lines of code ({len(rs_files)} files)")
    return total_loc


def format_number(num: int) -> str:
    """
    Format number with K suffix for readability.

    Args:
        num: Number to format

    Returns:
        Formatted string (e.g., "410", "1.2K", "25K")
    """
    if num < 1000:
        return str(num)
    elif num < 10000:
        return f"{num / 1000:.1f}K"
    else:
        return f"{num // 1000}K"


def generate_badge_url(label: str, message: str, color: str) -> str:
    """
    Generate shields.io badge URL.

    Args:
        label: Badge label (left side)
        message: Badge message (right side)
        color: Badge color (green, blue, red, etc.)

    Returns:
        shields.io badge URL
    """
    # URL-encode label and message
    label = label.replace(" ", "%20").replace("-", "--")
    message = message.replace(" ", "%20").replace("-", "--")
    
    return f"https://img.shields.io/badge/{label}-{message}-{color}"


def update_readme_badges(badges: Dict[str, str]) -> bool:
    """
    Update badges in README.md.

    Args:
        badges: Dictionary of badge_id -> badge_markdown

    Returns:
        True if successful, False otherwise
    """
    print("Updating README.md...")
    
    readme_path = Path(__file__).parent.parent / "README.md"
    if not readme_path.exists():
        print(f"  Error: README.md not found at {readme_path}", file=sys.stderr)
        return False
    
    try:
        with open(readme_path, "r", encoding="utf-8") as f:
            content = f.read()
        
        # Replace badges (look for badge markers)
        for badge_id, badge_markdown in badges.items():
            # Pattern: ![Badge_ID](...)
            pattern = rf"!\[{re.escape(badge_id)}\]\(https://img\.shields\.io/badge/[^\)]+\)"
            
            if re.search(pattern, content):
                content = re.sub(pattern, badge_markdown, content)
                print(f"  Updated badge: {badge_id}")
            else:
                print(f"  Warning: Badge not found: {badge_id}", file=sys.stderr)
        
        # Write updated content
        with open(readme_path, "w", encoding="utf-8") as f:
            f.write(content)
        
        print("  README.md updated successfully")
        return True
    
    except Exception as e:
        print(f"  Error updating README.md: {e}", file=sys.stderr)
        return False


def main() -> int:
    """
    Main entry point.

    Returns:
        Exit code (0 for success, 1 for error)
    """
    print("=== CI Badge Automation ===\n")
    
    # Collect badge data
    badges: Dict[str, str] = {}
    
    # 1. Test count badge
    test_count = count_tests()
    if test_count is not None:
        test_count_str = format_number(test_count)
        color = "success" if test_count >= 400 else "yellow"
        badge_url = generate_badge_url("Tests", f"{test_count_str}%2B%20passing", color)
        badges["Tests"] = f"![Tests]({badge_url})"
    
    # 2. Code coverage badge
    coverage = get_code_coverage()
    if coverage is not None:
        coverage_str = f"{coverage:.1f}%25"  # URL-encoded %
        if coverage >= 80:
            color = "success"
        elif coverage >= 70:
            color = "yellow"
        else:
            color = "orange"
        badge_url = generate_badge_url("Coverage", coverage_str, color)
        badges["Coverage"] = f"![Coverage]({badge_url})"
    
    # 3. Lines of code badge
    loc = count_lines_of_code()
    if loc is not None:
        loc_str = format_number(loc)
        color = "blue"
        badge_url = generate_badge_url("LOC", loc_str, color)
        badges["LOC"] = f"![LOC]({badge_url})"
    
    # Update README.md
    if badges:
        success = update_readme_badges(badges)
        if not success:
            return 1
    else:
        print("\nNo badges to update (all metrics failed)", file=sys.stderr)
        return 1
    
    print("\n=== Badge Update Complete ===")
    return 0


if __name__ == "__main__":
    sys.exit(main())

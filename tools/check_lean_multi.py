#!/usr/bin/env python3
"""
Check multiple Lean files and provide aggregated summary.
Usage: python3 check_lean_multi.py <mode> <file1> <file2> ...
where mode is: errors-only, warnings, sorries, warnings-summary, or transparency
"""

import sys
import subprocess
import os
from pathlib import Path
from typing import List, Tuple, Dict

def check_all_files_single_build(file_paths: List[str], mode: str, script_dir: str) -> List[Tuple[str, int, str]]:
    """
    Check all files by calling single-file checker for each.

    Args:
        file_paths: List of Lean file paths
        mode: One of 'errors-only', 'warnings', 'sorries', 'warnings-summary', 'transparency'
        script_dir: Directory containing check scripts

    Returns:
        List of (file_path, exit_code, output) tuples
    """
    # Simply call the individual checker for each file
    # This ensures we get fresh results without caching confusion
    return [check_file_individual(fp, mode, script_dir) for fp in file_paths]

def file_has_diagnostics(build_output: str, file_path: str, mode: str) -> bool:
    """Check if build output contains diagnostics for a specific file."""
    import re

    # Patterns that indicate errors/warnings for this file
    if mode == 'errors-only':
        patterns = [
            rf'^error:\s+{re.escape(file_path)}:\d+:\d+:',
            rf'^{re.escape(file_path)}:\d+:\d+:\s+error',
            rf'^error:\s+{re.escape(file_path)}:\s+',  # Import/build errors without line:col
            rf'^error:.*{re.escape(file_path)}.*bad import',  # Bad import errors
        ]
    else:  # warnings or warnings-summary
        patterns = [
            rf'^error:\s+{re.escape(file_path)}:\d+:\d+:',
            rf'^{re.escape(file_path)}:\d+:\d+:\s+error',
            rf'^warning:\s+{re.escape(file_path)}:\d+:\d+:',
            rf'^{re.escape(file_path)}:\d+:\d+:\s+warning',
        ]

    for line in build_output.split('\n'):
        for pattern in patterns:
            if re.match(pattern, line):
                return True
    return False

def extract_file_diagnostics(build_output: str, file_path: str, mode: str) -> str:
    """Extract diagnostics for a specific file from build output."""
    import re

    lines = build_output.split('\n')
    result = []

    if mode == 'errors-only':
        patterns = [
            re.compile(rf'^error:\s+{re.escape(file_path)}:\d+:\d+:'),
            re.compile(rf'^{re.escape(file_path)}:\d+:\d+:\s+error'),
            re.compile(rf'^error:\s+{re.escape(file_path)}:\s+'),  # Import/build errors
            re.compile(rf'^error:.*{re.escape(file_path)}.*bad import'),  # Bad imports
        ]
    else:
        patterns = [
            re.compile(rf'^error:\s+{re.escape(file_path)}:\d+:\d+:'),
            re.compile(rf'^{re.escape(file_path)}:\d+:\d+:\s+error'),
            re.compile(rf'^warning:\s+{re.escape(file_path)}:\d+:\d+:'),
            re.compile(rf'^{re.escape(file_path)}:\d+:\d+:\s+warning'),
        ]

    in_diagnostic = False
    current_diagnostic = []

    for line in lines:
        # Check if line starts a diagnostic for our file
        if any(p.match(line) for p in patterns):
            if current_diagnostic:
                result.extend(current_diagnostic)
                result.append('')
            current_diagnostic = [line]
            in_diagnostic = True
        elif in_diagnostic:
            # Check if we hit a new section
            if line.startswith('⚠ [') or line.startswith('✔ [') or line.startswith('error:') or line.startswith('warning:'):
                if current_diagnostic:
                    result.extend(current_diagnostic)
                    result.append('')
                current_diagnostic = []
                in_diagnostic = False
            else:
                current_diagnostic.append(line)

    if current_diagnostic:
        result.extend(current_diagnostic)

    return '\n'.join(result).strip()

def check_file_individual(file_path: str, mode: str, script_dir: str) -> Tuple[str, int, str]:
    """
    Check a single file by calling the bash wrapper script.

    Args:
        file_path: Path to Lean file
        mode: One of 'errors-only', 'warnings', 'sorries', 'warnings-summary', 'transparency'
        script_dir: Directory containing check scripts (the tools/ directory)

    Returns:
        Tuple of (file_path, exit_code, output)
    """
    # Call the check_lean.sh script (one level up from tools/ directory)
    check_script = os.path.join(os.path.dirname(script_dir), 'check_lean.sh')

    if not os.path.exists(check_script):
        return (file_path, 2, f"Error: check_lean.sh not found at {check_script}")

    # Map mode to command-line flag
    mode_flag_map = {
        'errors-only': '--errors-only',
        'warnings': '',  # default mode (no flag)
        'sorries': '--sorries',
        'warnings-summary': '--warnings-summary',
        'transparency': '--transparency',
    }

    mode_flag = mode_flag_map.get(mode)
    if mode_flag is None:
        return (file_path, 2, f"Error: Unknown mode '{mode}'")

    try:
        # Build command: ./check_lean.sh [--flag] file_path
        if mode_flag:
            cmd = [check_script, mode_flag, file_path]
        else:
            cmd = [check_script, file_path]

        # Run the single-file checker
        result = subprocess.run(
            cmd,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True
        )

        return (file_path, result.returncode, result.stdout.strip())

    except Exception as e:
        return (file_path, 2, f"Error checking {file_path}: {str(e)}")


def format_multi_file_summary(results: List[Tuple[str, int, str]], mode: str) -> str:
    """
    Format results from multiple files into a summary.

    Args:
        results: List of (file_path, exit_code, output) tuples
        mode: The mode used for checking

    Returns:
        Formatted string
    """
    output = []

    # Summary header
    output.append("Build Status Summary:")

    clean_files = []
    failed_files = []

    for file_path, exit_code, file_output in results:
        if exit_code == 0:
            clean_files.append(file_path)
            output.append(f"  ✓ {file_path}: Clean")
        else:
            failed_files.append((file_path, file_output))
            # Extract count from output if possible
            if mode == 'errors-only':
                output.append(f"  ✗ {file_path}: Has errors")
            elif mode in ['warnings', 'warnings-summary']:
                # Try to extract warning count
                count_match = None
                for line in file_output.split('\n'):
                    if 'Total:' in line and 'warning' in line:
                        count_match = line
                        break
                if count_match:
                    output.append(f"  ✗ {file_path}: {count_match.split('Total:')[1].strip()}")
                else:
                    output.append(f"  ✗ {file_path}: Has warnings")
            elif mode == 'sorries':
                # Extract sorry count
                count_match = None
                for line in file_output.split('\n'):
                    if 'Total:' in line and 'sorries' in line:
                        count_match = line
                        break
                if count_match:
                    output.append(f"  ✗ {file_path}: {count_match.split('Total:')[1].strip()}")
                else:
                    output.append(f"  ✗ {file_path}: Has sorries")

    output.append("")

    # Overall result
    total = len(results)
    clean_count = len(clean_files)

    if mode == 'errors-only':
        if failed_files:
            output.append(f"Result: {clean_count}/{total} files compile without errors ✗\n")
        else:
            output.append(f"Result: {total}/{total} files compile without errors ✓\n")
    elif mode in ['warnings', 'warnings-summary']:
        if failed_files:
            output.append(f"Result: {clean_count}/{total} files have no warnings ✗\n")
        else:
            output.append(f"Result: {total}/{total} files are warning-free ✓\n")
    elif mode == 'sorries':
        if failed_files:
            output.append(f"Result: {clean_count}/{total} files have no sorries ✗\n")
        else:
            output.append(f"Result: {total}/{total} files are sorry-free ✓\n")

    # Show details for failed files
    if failed_files:
        output.append("Showing details for files with issues:\n")
        for file_path, file_output in failed_files:
            output.append(f"=== {file_path} ===")
            output.append(file_output)
            output.append("")

    return '\n'.join(output)


def main():
    if len(sys.argv) < 3:
        print("Usage: python3 check_lean_multi.py <mode> <file1> [file2] ...", file=sys.stderr)
        print("", file=sys.stderr)
        print("Modes:", file=sys.stderr)
        print("  errors-only      - Show only errors", file=sys.stderr)
        print("  warnings         - Show all warnings", file=sys.stderr)
        print("  sorries          - Show sorry summary", file=sys.stderr)
        print("  warnings-summary - Show warning summary", file=sys.stderr)
        print("", file=sys.stderr)
        print("Example:", file=sys.stderr)
        print("  python3 check_lean_multi.py errors-only TDCSG/*.lean", file=sys.stderr)
        sys.exit(1)

    mode = sys.argv[1]
    file_paths = sys.argv[2:]

    # Get script directory
    script_dir = os.path.dirname(os.path.abspath(__file__))

    # Check all files using a single build to avoid caching issues
    results = check_all_files_single_build(file_paths, mode, script_dir)

    # Format and print summary
    output = format_multi_file_summary(results, mode)
    print(output)

    # Exit with error code if any file failed
    any_failed = any(exit_code != 0 for _, exit_code, _ in results)
    sys.exit(1 if any_failed else 0)


if __name__ == '__main__':
    main()

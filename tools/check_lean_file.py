#!/usr/bin/env python3
"""
Extract diagnostics (errors/warnings) for a specific Lean file from lake build output.
Usage: python3 check_lean_file.py <filename>
"""

import sys
import re
from pathlib import Path

def extract_diagnostics(build_output: str, target_file: str) -> str:
    """
    Extract all errors and warnings for a specific file with full context.

    Args:
        build_output: Complete output from 'lake build'
        target_file: Target file to filter (e.g., 'TDCSG/Examples.lean')

    Returns:
        Filtered diagnostics with full multi-line context
    """
    lines = build_output.split('\n')
    result = []
    in_diagnostic = False
    current_diagnostic = []

    # Patterns to match error/warning lines for our target file
    # Format 1: "error: TDCSG/File.lean:line:col:" or "warning: TDCSG/File.lean:line:col:" (lake build)
    # Format 2: "TDCSG/File.lean:line:col: error:" or "TDCSG/File.lean:line:col: warning:" (lean command)
    diagnostic_pattern_1 = re.compile(
        rf'^(error|warning):\s+{re.escape(target_file)}:\d+:\d+:'
    )
    diagnostic_pattern_2 = re.compile(
        rf'^{re.escape(target_file)}:\d+:\d+:\s+(error|warning)'
    )

    # Patterns that indicate end of current diagnostic or start of new section
    section_markers = [
        re.compile(r'^⚠ \['),     # Build progress warning
        re.compile(r'^✔ \['),     # Build progress success
        re.compile(r'^Build '),   # Build completion message
        re.compile(rf'^(error|warning):\s+(?!{re.escape(target_file)})'),  # Diagnostic for different file (format 1)
        re.compile(rf'^(?!{re.escape(target_file)})[^:]+:\d+:\d+:\s+(error|warning)'),  # Diagnostic for different file (format 2)
    ]

    for line in lines:
        # Check if this line starts a diagnostic for our target file
        if diagnostic_pattern_1.match(line) or diagnostic_pattern_2.match(line):
            # Save previous diagnostic if exists
            if current_diagnostic:
                result.extend(current_diagnostic)
                result.append('')  # Blank line separator

            current_diagnostic = [line]
            in_diagnostic = True
            continue

        if in_diagnostic:
            # Check if we've hit a section marker
            is_section_marker = any(pattern.search(line) for pattern in section_markers)

            if is_section_marker:
                # End current diagnostic
                if current_diagnostic:
                    result.extend(current_diagnostic)
                    result.append('')  # Blank line separator
                current_diagnostic = []
                in_diagnostic = False
            else:
                # Continue current diagnostic (includes indented continuation lines)
                current_diagnostic.append(line)

    # Don't forget the last diagnostic
    if current_diagnostic:
        result.extend(current_diagnostic)

    # Remove trailing blank lines
    while result and result[-1] == '':
        result.pop()

    return '\n'.join(result)


def main():
    if len(sys.argv) != 2:
        print("Usage: python3 check_lean_file.py <filename>", file=sys.stderr)
        print("Example: python3 check_lean_file.py TDCSG/Examples.lean", file=sys.stderr)
        sys.exit(1)

    target_file = sys.argv[1]

    # Read stdin (pipe from lake build)
    build_output = sys.stdin.read()

    # Extract and print diagnostics
    diagnostics = extract_diagnostics(build_output, target_file)

    if diagnostics:
        print(diagnostics)
        sys.exit(1)  # Exit with error code if there are diagnostics
    else:
        # No diagnostics means success
        print(f"✓ {target_file}: No errors or warnings")
        sys.exit(0)


if __name__ == '__main__':
    main()

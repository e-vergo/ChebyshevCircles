#!/usr/bin/env python3
"""
Extract ONLY errors (no warnings) for a specific Lean file from lake build output.
Usage: python3 check_lean_errors_only.py <filename>
"""

import sys
import re

def extract_errors_only(build_output: str, target_file: str) -> str:
    """
    Extract ONLY errors (not warnings) for a specific file with full context.

    Args:
        build_output: Complete output from 'lake build'
        target_file: Target file to filter (e.g., 'TDCSG/Examples.lean')

    Returns:
        Filtered errors with full multi-line context (warnings excluded)
    """
    lines = build_output.split('\n')
    result = []
    in_diagnostic = False
    current_diagnostic = []

    # Patterns to match error lines for our target file
    # Format 1: "error: TDCSG/File.lean:line:col:" (lake build format)
    # Format 2: "TDCSG/File.lean:line:col: error:" (lean command format)
    # Format 3: "error: TDCSG/File.lean: bad import ..." (import/build errors without line:col)
    # Format 4: Various build errors mentioning the file
    error_pattern_1 = re.compile(
        rf'^error:\s+{re.escape(target_file)}:\d+:\d+:'
    )
    error_pattern_2 = re.compile(
        rf'^{re.escape(target_file)}:\d+:\d+:\s+error'
    )
    error_pattern_3 = re.compile(
        rf'^error:\s+{re.escape(target_file)}:\s+'
    )
    error_pattern_4 = re.compile(
        rf'^error:.*{re.escape(target_file)}.*bad import'
    )

    # Patterns that indicate end of current diagnostic or start of new section
    section_markers = [
        re.compile(r'^⚠ \['),     # Build progress
        re.compile(r'^✔ \['),     # Build progress
        re.compile(r'^Build '),   # Build completion
        re.compile(rf'^error:\s+(?!{re.escape(target_file)})'),  # Error for different file (format 1)
        re.compile(rf'^(?!{re.escape(target_file)})[^:]+:\d+:\d+:\s+error'),  # Error for different file (format 2)
        re.compile(r'^warning:'), # Warning (any file)
        re.compile(r':\s+warning:'), # Warning (lean format)
    ]

    for line in lines:
        # Check if this line starts an ERROR for our target file
        if (error_pattern_1.match(line) or error_pattern_2.match(line) or
            error_pattern_3.match(line) or error_pattern_4.match(line)):
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
                # Continue current diagnostic
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
        print("Usage: python3 check_lean_errors_only.py <filename>", file=sys.stderr)
        print("Example: python3 check_lean_errors_only.py TDCSG/Examples.lean", file=sys.stderr)
        sys.exit(1)

    target_file = sys.argv[1]

    # Read stdin (pipe from lake build)
    build_output = sys.stdin.read()

    # Extract and print ONLY errors
    errors = extract_errors_only(build_output, target_file)

    if errors:
        print(errors)
        sys.exit(1)  # Exit with error code if there are errors
    else:
        # No errors means success
        print(f"✓ {target_file}: No errors")
        sys.exit(0)


if __name__ == '__main__':
    main()

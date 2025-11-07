#!/usr/bin/env python3
"""
Extract sorries with theorem names and context from Lean build output and source file.
Usage: python3 check_lean_sorries.py <filename>
"""

import sys
import re
from pathlib import Path
from typing import List, Dict, Tuple, Optional

def extract_theorem_declaration_lines(build_output: str, target_file: str) -> List[int]:
    """
    Extract line numbers of theorem declarations that use sorry from build output.

    Args:
        build_output: Complete output from 'lake build'
        target_file: Target file (e.g., 'TDCSG/Ergodic.lean')

    Returns:
        List of line numbers where theorems with sorries are declared
    """
    declaration_lines = []

    # Normalize path (remove duplicate slashes)
    normalized_target = re.sub(r'/+', '/', target_file)

    # Pattern: "warning: TDCSG/File.lean:194:8: declaration uses 'sorry'"
    # Match flexibly to handle path variations
    pattern = re.compile(
        rf'^warning:\s+{re.escape(normalized_target)}:(\d+):\d+:\s+declaration uses [\'"]sorry[\'"]'
    )

    for line in build_output.split('\n'):
        # Normalize the line too
        normalized_line = re.sub(r'/+', '/', line)
        match = pattern.match(normalized_line)
        if match:
            declaration_lines.append(int(match.group(1)))

    return sorted(declaration_lines)


def find_theorem_for_sorry(source_lines: List[str], sorry_line: int) -> Optional[Tuple[str, int]]:
    """
    Find the theorem/lemma/def that contains a given sorry.

    Args:
        source_lines: Lines of the source file (1-indexed)
        sorry_line: Line number of the sorry

    Returns:
        Tuple of (theorem_name, theorem_line) or None if not found
    """
    # Search backwards from sorry_line to find theorem/lemma/def
    theorem_pattern = re.compile(r'^(theorem|lemma|def)\s+(\S+)')

    for line_num in range(sorry_line - 1, 0, -1):
        if line_num - 1 < len(source_lines):
            line = source_lines[line_num - 1]
            match = theorem_pattern.match(line)
            if match:
                decl_type = match.group(1)
                name = match.group(2)
                return (f"{decl_type} {name}", line_num)

    return None


def extract_inline_comment(source_lines: List[str], sorry_line: int) -> Optional[str]:
    """
    Extract inline comment after sorry (e.g., "sorry -- COMMENT").

    Args:
        source_lines: Lines of the source file (1-indexed)
        sorry_line: Line number of the sorry

    Returns:
        Comment text or None
    """
    if sorry_line - 1 < len(source_lines):
        line = source_lines[sorry_line - 1].strip()
        # Match "sorry -- COMMENT" or "sorry -- COMMENT..."
        match = re.search(r'sorry\s*--\s*(.+?)(?:\s*-/)?$', line)
        if match:
            return match.group(1).strip()
    return None


def find_all_sorries_in_theorem(source_lines: List[str], theorem_line: int, next_theorem_line: Optional[int]) -> List[int]:
    """
    Find all sorry statements within a theorem's body.

    Args:
        source_lines: Lines of the source file (1-indexed)
        theorem_line: Starting line of the theorem
        next_theorem_line: Starting line of next theorem (or None if last)

    Returns:
        List of line numbers where sorry appears
    """
    sorry_lines = []
    end_line = next_theorem_line if next_theorem_line else len(source_lines)

    for line_num in range(theorem_line, end_line):
        if line_num - 1 < len(source_lines):
            line = source_lines[line_num - 1]
            if re.search(r'\bsorry\b', line):
                sorry_lines.append(line_num)

    return sorry_lines


def get_all_theorem_lines(source_lines: List[str]) -> List[int]:
    """Get line numbers of all theorem/lemma/def declarations."""
    theorem_pattern = re.compile(r'^(theorem|lemma|def)\s+')
    theorem_lines = []

    for i, line in enumerate(source_lines, start=1):
        if theorem_pattern.match(line):
            theorem_lines.append(i)

    return theorem_lines


def format_sorries_output(target_file: str, sorry_data: List[Dict]) -> str:
    """
    Format sorry information for human-readable output.

    Args:
        target_file: Target file path
        sorry_data: List of dicts with theorem info

    Returns:
        Formatted string
    """
    if not sorry_data:
        return f"✓ {target_file}: No sorries found"

    output = [f"Sorries in {target_file}:\n"]

    for item in sorry_data:
        # Header: theorem name and line
        theorem_name = item['theorem_name']
        theorem_line = item['theorem_line']
        output.append(f"  {theorem_name} (line {theorem_line})")

        # Sorry locations
        sorry_lines = item['sorry_lines']
        for i, sline in enumerate(sorry_lines):
            is_last = (i == len(sorry_lines) - 1)
            prefix = "└─" if is_last else "├─"

            comment = item.get('comments', {}).get(sline)
            if comment:
                output.append(f"    {prefix} sorry at line {sline}")
                # Truncate long comments
                if len(comment) > 80:
                    comment = comment[:77] + "..."
                output.append(f"       └─ Comment: {comment}")
            else:
                output.append(f"    {prefix} sorry at line {sline}")

        output.append("")  # Blank line between theorems

    # Summary
    total_sorries = sum(len(item['sorry_lines']) for item in sorry_data)
    total_theorems = len(sorry_data)
    output.append(f"Total: {total_sorries} sorries across {total_theorems} theorem(s)")

    return '\n'.join(output)


def main():
    if len(sys.argv) != 2:
        print("Usage: python3 check_lean_sorries.py <filename>", file=sys.stderr)
        print("Example: python3 check_lean_sorries.py TDCSG/Ergodic.lean", file=sys.stderr)
        sys.exit(1)

    target_file = sys.argv[1]
    # Normalize path
    normalized_target = re.sub(r'/+', '/', target_file)

    # Read stdin (pipe from lake build)
    build_output = sys.stdin.read()

    # Extract theorem declaration line numbers from build output
    theorem_declaration_lines = extract_theorem_declaration_lines(build_output, normalized_target)

    if not theorem_declaration_lines:
        print(f"✓ {target_file}: No sorries found")
        sys.exit(0)

    # Read source file to extract theorem names and comments
    try:
        with open(normalized_target, 'r') as f:
            source_lines = f.readlines()
    except FileNotFoundError:
        print(f"Error: Could not read source file {normalized_target}", file=sys.stderr)
        sys.exit(2)

    # Get all theorem lines for boundary detection
    all_theorem_lines = get_all_theorem_lines(source_lines)

    # Group sorries by theorem
    theorem_sorry_map = {}

    for decl_line in theorem_declaration_lines:
        # The declaration line IS the theorem line
        if decl_line - 1 < len(source_lines):
            line = source_lines[decl_line - 1]
            theorem_pattern = re.compile(r'^(theorem|lemma|def)\s+(\S+)')
            match = theorem_pattern.match(line)

            if match:
                decl_type = match.group(1)
                name = match.group(2)
                theorem_name = f"{decl_type} {name}"
                theorem_line = decl_line

                # Find next theorem line for boundary
                next_theorem = None
                for tl in all_theorem_lines:
                    if tl > theorem_line:
                        next_theorem = tl
                        break

                # Find all sorries in this theorem
                all_sorries = find_all_sorries_in_theorem(source_lines, theorem_line, next_theorem)

                theorem_sorry_map[theorem_line] = {
                    'theorem_name': theorem_name,
                    'theorem_line': theorem_line,
                    'sorry_lines': all_sorries,
                    'comments': {}
                }

                # Extract comments for each sorry
                for sline in all_sorries:
                    comment = extract_inline_comment(source_lines, sline)
                    if comment:
                        theorem_sorry_map[theorem_line]['comments'][sline] = comment

    # Convert to sorted list
    sorry_data = [theorem_sorry_map[tl] for tl in sorted(theorem_sorry_map.keys())]

    # Format and print output
    output = format_sorries_output(target_file, sorry_data)
    print(output)

    # Exit with error code if sorries exist
    sys.exit(1)


if __name__ == '__main__':
    main()

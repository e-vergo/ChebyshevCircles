#!/usr/bin/env python3
"""
Extract and summarize warnings from Lean build output, grouping by type.
Usage: python3 check_lean_warnings_summary.py <filename>
"""

import sys
import re
from typing import List, Dict, Optional
from collections import defaultdict

def extract_warnings(build_output: str, target_file: str) -> List[Dict]:
    """
    Extract all warnings for a specific file with full context.

    Args:
        build_output: Complete output from 'lake build'
        target_file: Target file to filter

    Returns:
        List of warning dicts with line, type, and message
    """
    # Normalize path
    normalized_target = re.sub(r'/+', '/', target_file)

    lines = build_output.split('\n')
    warnings = []
    in_warning = False
    current_warning = None

    # Pattern to match warning lines
    warning_pattern = re.compile(
        rf'^warning:\s+{re.escape(normalized_target)}:(\d+):(\d+):\s+(.+)'
    )

    # Patterns that indicate end of current warning
    section_markers = [
        re.compile(r'^⚠ \['),
        re.compile(r'^✔ \['),
        re.compile(r'^Build '),
        re.compile(rf'^warning:\s+(?!{re.escape(normalized_target)})'),
        re.compile(r'^error:'),
    ]

    for line in lines:
        # Normalize line
        normalized_line = re.sub(r'/+', '/', line)
        match = warning_pattern.match(normalized_line)
        if match:
            # Save previous warning
            if current_warning:
                warnings.append(current_warning)

            line_num = int(match.group(1))
            col_num = int(match.group(2))
            first_line = match.group(3)

            current_warning = {
                'line': line_num,
                'col': col_num,
                'first_line': first_line,
                'full_message': [line],
            }
            in_warning = True
            continue

        if in_warning:
            is_section_marker = any(pattern.search(line) for pattern in section_markers)

            if is_section_marker:
                if current_warning:
                    warnings.append(current_warning)
                current_warning = None
                in_warning = False
            else:
                current_warning['full_message'].append(line)

    # Don't forget last warning
    if current_warning:
        warnings.append(current_warning)

    return warnings


def classify_warning(warning: Dict) -> Dict:
    """
    Classify warning by type and extract actionable information.

    Returns:
        Dict with 'category', 'subcategory', 'hint', etc.
    """
    first_line = warning['first_line']
    full_text = '\n'.join(warning['full_message'])

    # Pattern 1: "declaration uses 'sorry'"
    if "declaration uses 'sorry'" in first_line:
        return {
            'category': 'sorries',
            'subcategory': 'sorry',
            'severity': 'blocker',
            'message': first_line,
        }

    # Pattern 2: "automatically included section variable(s) unused"
    if 'automatically included section variable(s) unused' in first_line:
        # Extract variable names
        var_match = re.search(r'unused in theorem `([^`]+)`', full_text)
        theorem_name = var_match.group(1) if var_match else 'unknown'

        # Extract omit suggestion
        omit_match = re.search(r'omit (.+?) in theorem', full_text)
        omit_vars = omit_match.group(1) if omit_match else ''

        return {
            'category': 'easy_fixes',
            'subcategory': 'unused_section_vars',
            'severity': 'low',
            'theorem_name': theorem_name,
            'hint': f'omit {omit_vars} in theorem ...' if omit_vars else '',
            'message': f'Unused section variables in {theorem_name}',
        }

    # Pattern 3: "This simp argument is unused"
    if 'This simp argument is unused' in first_line:
        # Extract the unused argument
        arg_match = re.search(r'This simp argument is unused:\s*(.+)', full_text)
        unused_arg = arg_match.group(1).strip() if arg_match else ''

        # Extract the simp call with strikethrough
        simp_match = re.search(r'simp only \[([^\]]+)\]', full_text)
        simp_args = simp_match.group(1) if simp_match else ''

        # Remove strikethrough formatting to get clean version
        clean_args = re.sub(r'[̵\u0335]+', '', simp_args)

        return {
            'category': 'easy_fixes',
            'subcategory': 'unused_simp_args',
            'severity': 'low',
            'unused_arg': unused_arg,
            'simp_args': clean_args,
            'hint': f'Remove {unused_arg} from simp list',
            'message': f'Unused simp argument: {unused_arg}',
        }

    # Pattern 4: Deprecation warnings
    if 'has been deprecated' in first_line or 'deprecated' in first_line.lower():
        return {
            'category': 'deprecations',
            'subcategory': 'deprecated_lemma',
            'severity': 'medium',
            'message': first_line,
        }

    # Default: other warning
    return {
        'category': 'other',
        'subcategory': 'unknown',
        'severity': 'medium',
        'message': first_line,
    }


def format_summary(target_file: str, warnings: List[Dict], classified: List[Dict]) -> str:
    """
    Format warnings into a human-readable summary.

    Args:
        target_file: Target file path
        warnings: Raw warning data
        classified: Classified warnings

    Returns:
        Formatted string
    """
    if not warnings:
        return f"✓ {target_file}: No warnings"

    output = [f"Warning Summary for {target_file}:\n"]

    # Group by category
    by_category = defaultdict(list)
    for w, c in zip(warnings, classified):
        by_category[c['category']].append((w, c))

    # Display order: easy_fixes, sorries, deprecations, other
    display_order = ['easy_fixes', 'sorries', 'deprecations', 'other']

    for category in display_order:
        if category not in by_category:
            continue

        items = by_category[category]

        # Category header
        if category == 'easy_fixes':
            output.append(f"EASY FIXES ({len(items)} warning(s)):\n")
        elif category == 'sorries':
            output.append(f"SORRIES ({len(items)} warning(s)):\n")
        elif category == 'deprecations':
            output.append(f"DEPRECATIONS ({len(items)} warning(s)):\n")
        else:
            output.append(f"OTHER WARNINGS ({len(items)} warning(s)):\n")

        # Group by subcategory
        by_subcat = defaultdict(list)
        for w, c in items:
            by_subcat[c['subcategory']].append((w, c))

        for subcat, sub_items in by_subcat.items():
            if category == 'easy_fixes':
                # Format easy fixes nicely
                if subcat == 'unused_section_vars':
                    output.append(f"  Unused section variables ({len(sub_items)} instance(s)):")
                    for w, c in sub_items:
                        output.append(f"    ├─ Line {w['line']}: {c['theorem_name']}")
                        if c.get('hint'):
                            output.append(f"    │  Fix: {c['hint']}")
                    output.append("")

                elif subcat == 'unused_simp_args':
                    output.append(f"  Unused simp arguments ({len(sub_items)} instance(s)):")
                    for w, c in sub_items:
                        output.append(f"    ├─ Line {w['line']}: Remove `{c['unused_arg']}` from simp list")
                    output.append("")

            elif category == 'sorries':
                output.append(f"  See `--sorries` mode for detailed sorry information")
                output.append("")

            elif category == 'deprecations':
                for w, c in sub_items:
                    output.append(f"  └─ Line {w['line']}: {c['message']}")
                output.append("")

            else:
                # Other warnings
                for w, c in sub_items:
                    output.append(f"  └─ Line {w['line']}: {c['message']}")
                output.append("")

    # Summary line
    total = len(warnings)
    easy_count = len(by_category.get('easy_fixes', []))
    sorry_count = len(by_category.get('sorries', []))

    summary_parts = []
    if easy_count > 0:
        summary_parts.append(f"{easy_count} easy fix(es)")
    if sorry_count > 0:
        summary_parts.append(f"{sorry_count} sorry/ies")

    if summary_parts:
        output.append(f"Total: {total} warning(s) ({', '.join(summary_parts)})")
    else:
        output.append(f"Total: {total} warning(s)")

    return '\n'.join(output)


def main():
    if len(sys.argv) != 2:
        print("Usage: python3 check_lean_warnings_summary.py <filename>", file=sys.stderr)
        print("Example: python3 check_lean_warnings_summary.py TDCSG/Composition.lean", file=sys.stderr)
        sys.exit(1)

    target_file = sys.argv[1]
    # Normalize path
    normalized_target = re.sub(r'/+', '/', target_file)

    # Read stdin (pipe from lake build)
    build_output = sys.stdin.read()

    # Extract warnings
    warnings = extract_warnings(build_output, normalized_target)

    if not warnings:
        print(f"✓ {target_file}: No warnings")
        sys.exit(0)

    # Classify warnings
    classified = [classify_warning(w) for w in warnings]

    # Format and print summary
    output = format_summary(target_file, warnings, classified)
    print(output)

    # Exit with error code if warnings exist
    sys.exit(1)


if __name__ == '__main__':
    main()

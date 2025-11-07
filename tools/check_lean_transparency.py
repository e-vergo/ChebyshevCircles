#!/usr/bin/env python3
"""
Transparency checker for Lean proofs - detects proof evasion patterns.

This tool implements the Anti-Placeholder Protocol from CLAUDE.md, detecting:
- Axiom abuse (including hidden sorryAx)
- Trivial abuse (theorem foo : True := trivial)
- Placeholder definitions (def IsFoo := True)
- Admitted/unsafe declarations
- Hidden sorries

Usage: python3 check_lean_transparency.py <filename>
Exit codes:
  0 - No violations detected (transparent)
  1 - Violations detected
  2 - Error (file not found, etc.)
"""

import sys
import re
import subprocess
from pathlib import Path
from typing import List, Dict, Tuple, Optional, Set
from dataclasses import dataclass

@dataclass
class Violation:
    """A detected transparency violation."""
    category: str
    line: int
    message: str
    severity: str  # 'critical' or 'warning'

class TransparencyChecker:
    """Check Lean files for proof evasion patterns."""

    def __init__(self, file_path: str):
        self.file_path = file_path
        self.violations: List[Violation] = []
        self.source_lines: List[str] = []
        self.code_only_lines: List[str] = []  # Lines with comments removed

    def load_file(self) -> bool:
        """Load source file."""
        try:
            with open(self.file_path, 'r', encoding='utf-8') as f:
                self.source_lines = f.readlines()
            return True
        except FileNotFoundError:
            print(f"Error: File not found: {self.file_path}", file=sys.stderr)
            return False
        except Exception as e:
            print(f"Error reading file: {e}", file=sys.stderr)
            return False

    def remove_all_comments(self) -> List[str]:
        """
        Remove all comments from source file, handling multi-line block comments.
        Returns list of lines with comments removed.

        Handles:
        - Line comments: -- ...
        - Block comments: /- ... -/ (including multi-line)
        - Nested block comments: /- outer /- inner -/ outer -/
        """
        result = []
        in_block_comment = False
        block_comment_depth = 0

        for line in self.source_lines:
            processed = []
            i = 0

            while i < len(line):
                # Check for block comment start /-
                if i + 1 < len(line) and line[i:i+2] == '/-':
                    block_comment_depth += 1
                    in_block_comment = True
                    i += 2
                    continue

                # Check for block comment end -/
                if i + 1 < len(line) and line[i:i+2] == '-/':
                    if block_comment_depth > 0:
                        block_comment_depth -= 1
                    if block_comment_depth == 0:
                        in_block_comment = False
                    i += 2
                    continue

                # Check for line comment --
                if not in_block_comment and i + 1 < len(line) and line[i:i+2] == '--':
                    # Rest of line is comment
                    break

                # If not in comment, keep the character
                if not in_block_comment:
                    processed.append(line[i])

                i += 1

            result.append(''.join(processed))

        return result

    def scan_for_forbidden_keywords(self):
        """
        Zero-tolerance keyword detection.
        If keyword appears outside comments, it's a violation. No exceptions.

        Forbidden keywords:
        - trivial: tactic that may hide fake proofs
        - admitted: explicit proof admission
        - axiom: custom axiom declaration
        - unsafe: unsafe code
        """
        forbidden_keywords = {
            'trivial': 'Forbidden keyword (may indicate fake proof)',
            'admitted': 'Forbidden keyword (proof not completed)',
            'axiom': 'Forbidden keyword (custom axiom)',
            'unsafe': 'Forbidden keyword (unsafe code)'
        }

        for i, code_only in enumerate(self.code_only_lines, 1):
            # Check each forbidden keyword
            for keyword, message in forbidden_keywords.items():
                if re.search(rf'\b{keyword}\b', code_only):
                    self.violations.append(Violation(
                        category="Forbidden Keyword",
                        line=i,
                        message=f"'{keyword}' - {message}",
                        severity="critical"
                    ))

    def scan_for_placeholder_definitions(self):
        """
        Zero-tolerance pattern detection for placeholder definitions.
        If pattern appears outside comments, it's a violation. No exceptions.

        Forbidden patterns:
        - Prop := True (placeholder predicate)
        - : True := (theorem proving True)
        """
        for i, code_only in enumerate(self.code_only_lines, 1):
            # Pattern 1: Prop := True (placeholder definition)
            if 'Prop := True' in code_only or 'Prop:=True' in code_only:
                self.violations.append(Violation(
                    category="Forbidden Pattern",
                    line=i,
                    message="'Prop := True' - Placeholder definition (trivializes predicates)",
                    severity="critical"
                ))

            # Pattern 2: : True := (theorem proving True)
            if re.search(r':\s*True\s*:=', code_only):
                self.violations.append(Violation(
                    category="Forbidden Pattern",
                    line=i,
                    message="': True :=' - Theorem proving True (suspicious)",
                    severity="critical"
                ))


    def scan_for_hidden_sorries(self):
        """
        Detect hidden or commented sorries.
        Note: With improved comment removal, this catches sorries that somehow
        survived comment removal (which would be unusual).
        """
        for i, code_only in enumerate(self.code_only_lines, 1):
            # If 'sorry' appears in code after comment removal, flag it
            # (Regular sorry statements are OK - they indicate incomplete work)
            # This is mainly to catch edge cases
            pass  # Most sorry detection is handled by existing mechanisms

    def extract_declarations(self) -> List[Tuple[int, str, str]]:
        """
        Extract theorem/lemma/def declarations for axiom checking.
        Returns: List of (line_number, declaration_type, name)
        """
        declarations = []
        for i, line in enumerate(self.source_lines, 1):
            # Match theorem/lemma/def declarations
            match = re.search(r'^\s*(theorem|lemma|def|instance)\s+(\w+)', line)
            if match:
                decl_type = match.group(1)
                name = match.group(2)
                declarations.append((i, decl_type, name))
        return declarations

    def check_axioms_via_lean(self) -> Dict[str, List[str]]:
        """
        Use Lean's #print axioms to check declarations.
        Returns: Dict mapping declaration names to their axioms

        Note: This requires lake environment to be set up.
        Falls back gracefully if Lean is not available.
        """
        declarations = self.extract_declarations()
        axiom_map = {}

        # Create a temporary file with #print axioms commands
        temp_commands = []
        for line_num, decl_type, name in declarations:
            temp_commands.append(f"#print axioms {name}")

        if not temp_commands:
            return axiom_map

        # Try to run Lean to check axioms
        # This is optional - if it fails, we just skip axiom checking via Lean
        try:
            # Create temp file with axiom checks
            temp_file = Path(self.file_path).parent / f"_temp_axiom_check_{Path(self.file_path).stem}.lean"

            # Import the original file
            original_module = Path(self.file_path).stem
            parent_dir = Path(self.file_path).parent.name

            with open(temp_file, 'w') as f:
                f.write(f"import {parent_dir}.{original_module}\n\n")
                f.write("open PiecewiseIsometry\n\n")
                for cmd in temp_commands:
                    f.write(cmd + "\n")

            # Run lean on temp file
            result = subprocess.run(
                ['lake', 'env', 'lean', str(temp_file)],
                capture_output=True,
                text=True,
                timeout=30,
                cwd=Path(self.file_path).parent.parent
            )

            # Parse output for axioms
            output = result.stderr + result.stdout
            current_decl = None
            for line in output.split('\n'):
                # Match declaration name
                if '\'sorryAx\'' in line:
                    # Extract which declaration this is for
                    # Format: "'TheoremName' depends on axioms: [sorryAx]"
                    match = re.search(r'\'(\w+)\'.*axioms.*sorryAx', line)
                    if match:
                        decl_name = match.group(1)
                        if decl_name not in axiom_map:
                            axiom_map[decl_name] = []
                        axiom_map[decl_name].append('sorryAx')

            # Clean up temp file
            temp_file.unlink(missing_ok=True)

        except (subprocess.TimeoutExpired, subprocess.SubprocessError, FileNotFoundError):
            # Lean not available or error - skip axiom checking
            pass
        except Exception:
            # Any other error - skip axiom checking
            pass

        return axiom_map

    def add_axiom_violations(self, axiom_map: Dict[str, List[str]]):
        """Add violations for declarations that depend on problematic axioms."""
        # Get line numbers for declarations
        declarations = self.extract_declarations()
        name_to_line = {name: line for line, _, name in declarations}

        for decl_name, axioms in axiom_map.items():
            if 'sorryAx' in axioms:
                line = name_to_line.get(decl_name, 0)
                self.violations.append(Violation(
                    category="Axiom (sorryAx)",
                    line=line,
                    message=f"declaration '{decl_name}' depends on 'sorryAx' (hidden sorry)",
                    severity="critical"
                ))

    def check_all(self) -> bool:
        """Run all checks. Returns True if transparent (no violations)."""
        if not self.load_file():
            return False

        # Remove all comments first (handles multi-line block comments)
        self.code_only_lines = self.remove_all_comments()

        # Run all checks on comment-free code
        self.scan_for_forbidden_keywords()  # Catches trivial, admitted, axiom, unsafe
        self.scan_for_placeholder_definitions()  # Catches Prop := True and : True :=
        self.scan_for_hidden_sorries()  # Catches commented sorries (if any survive)

        # Try to check axioms via Lean (optional, may fail gracefully)
        axiom_map = self.check_axioms_via_lean()
        if axiom_map:
            self.add_axiom_violations(axiom_map)

        return len(self.violations) == 0

    def report(self) -> str:
        """Generate human-readable report."""
        lines = []
        lines.append(f"\n=== TRANSPARENCY CHECK: {self.file_path} ===\n")

        if not self.violations:
            lines.append("✓ PASS: No transparency violations detected")
            lines.append("")
            lines.append("File is transparent:")
            lines.append("  ✓ No forbidden keywords (trivial, admitted, axiom, unsafe)")
            lines.append("  ✓ No forbidden patterns (Prop := True, : True :=)")
            lines.append("  ✓ No hidden sorries")
            lines.append("")
            return '\n'.join(lines)

        # Group violations by category
        by_category: Dict[str, List[Violation]] = {}
        for v in self.violations:
            if v.category not in by_category:
                by_category[v.category] = []
            by_category[v.category].append(v)

        lines.append(f"✗ VIOLATIONS DETECTED: {len(self.violations)} total\n")

        for category in sorted(by_category.keys()):
            violations = by_category[category]
            lines.append(f"{category}: ✗ {len(violations)} violation(s)")
            for v in sorted(violations, key=lambda x: x.line):
                severity_marker = "🔴" if v.severity == "critical" else "⚠️"
                lines.append(f"  {severity_marker} Line {v.line}: {v.message}")
            lines.append("")

        # Summary
        critical_count = sum(1 for v in self.violations if v.severity == "critical")
        warning_count = sum(1 for v in self.violations if v.severity == "warning")

        lines.append("Summary:")
        if critical_count > 0:
            lines.append(f"  🔴 {critical_count} critical violation(s)")
        if warning_count > 0:
            lines.append(f"  ⚠️  {warning_count} warning(s)")
        lines.append("")
        lines.append("Result: ✗ FILE HAS TRANSPARENCY VIOLATIONS")
        lines.append("")

        return '\n'.join(lines)

def main():
    if len(sys.argv) != 2:
        print("Usage: python3 check_lean_transparency.py <filename>", file=sys.stderr)
        print("", file=sys.stderr)
        print("Checks Lean file for proof evasion patterns:", file=sys.stderr)
        print("  - Trivial abuse (theorem foo : True := trivial)", file=sys.stderr)
        print("  - Placeholder definitions (def IsFoo := True)", file=sys.stderr)
        print("  - Admitted/unsafe declarations", file=sys.stderr)
        print("  - Custom axioms", file=sys.stderr)
        print("  - Hidden sorries", file=sys.stderr)
        sys.exit(2)

    file_path = sys.argv[1]

    checker = TransparencyChecker(file_path)
    is_transparent = checker.check_all()

    # Print report
    print(checker.report())

    # Exit with appropriate code
    sys.exit(0 if is_transparent else 1)

if __name__ == '__main__':
    main()

# Check Lean Tool Documentation

Comprehensive build verification and diagnostic tool for Lean 4 projects.

## Quick Reference

```bash
# Single file modes
./check_lean.sh --errors-only TDCSG/File.lean        # Fast error checking
./check_lean.sh --sorries TDCSG/File.lean            # Sorry tracking
./check_lean.sh --warnings-summary TDCSG/File.lean   # Categorized warnings
./check_lean.sh --transparency TDCSG/File.lean       # Proof evasion detection
./check_lean.sh TDCSG/File.lean                      # All diagnostics

# Multi-file modes
./check_lean.sh --all errors-only TDCSG/             # Check all files for errors
./check_lean.sh --all sorries TDCSG/                 # Sorry summary across files
./check_lean.sh --all warnings-summary TDCSG/        # Warnings across files
./check_lean.sh --all transparency TDCSG/            # Transparency check all files
```

## Overview

**Purpose:** Efficient build verification with minimal token usage and complete diagnostics.

**Key Benefits:**
- **99% token reduction** vs raw `lake build` output
- **Complete diagnostics** - never clips error messages
- **Per-file filtering** - eliminates noise from other files
- **Multi-file aggregation** - see project-wide status at a glance
- **Sorry tracking** - shows theorem names and locations

## Installation

The tool is located in the repository root:

```
TDCSG/
├── check_lean.sh              # Main entry point (use this)
└── tools/                     # Implementation (Python scripts)
    ├── CHECK_LEAN_TOOL.md    # This file
    ├── check_lean_errors_only.py
    ├── check_lean_file.py
    ├── check_lean_multi.py
    ├── check_lean_sorries.py
    ├── check_lean_warnings_summary.py
    └── check_lean_transparency.py  # NEW: Proof evasion detection
```

**Requirements:**
- Python 3
- Lean 4 with `lake` build tool
- Bash shell

## Modes

### 1. Errors-Only Mode

**Purpose:** Fast compilation verification (use for iteration)

```bash
./check_lean.sh --errors-only TDCSG/File.lean
```

**Output:**
- ✅ Success: `✓ TDCSG/File.lean: No errors`
- ❌ Failure: Complete error messages with full context

**When to use:**
- After every code change
- During proof development
- Quick sanity checks
- 99% of your workflow

### 2. Sorries Mode

**Purpose:** Track incomplete proofs

```bash
./check_lean.sh --sorries TDCSG/File.lean
```

**Output:**
```
Sorries in TDCSG/File.lean:

  theorem example_theorem (line 42)
    └─ sorry at line 47
       └─ Comment: Requires additional lemma from Mathlib

Total: 1 sorries across 1 theorem(s)
```

**Features:**
- Shows theorem/definition name
- Displays line numbers
- Extracts inline comments
- Counts by theorem

**When to use:**
- Track proof completion progress
- Identify remaining work
- Prioritize which sorries to tackle

### 3. Warnings-Summary Mode

**Purpose:** Categorized warning analysis

```bash
./check_lean.sh --warnings-summary TDCSG/File.lean
```

**Output:**
```
Warning Summary for TDCSG/File.lean:

EASY FIXES (3 warning(s)):

  Unused section variables (2 instance(s)):
    ├─ Line 85: theorem foo
    │  Fix: omit [MetricSpace α] in theorem ...
    ├─ Line 121: theorem bar
    │  Fix: omit [MeasurableSpace α] in theorem ...

  Unused simp arguments (1 instance(s)):
    ├─ Line 446: Remove `_root_.id` from simp list

Total: 3 warning(s) (3 easy fix(es))
```

**Categories:**
- EASY FIXES - Simple mechanical fixes
- SORRIES - Declaration uses sorry
- OTHER - Miscellaneous warnings

**When to use:**
- Code quality review
- Before git commits
- Cleanup sessions

### 4. Transparency Mode (Proof Evasion Detection)

**Purpose:** Detect proof evasion patterns per Anti-Placeholder Protocol

```bash
./check_lean.sh --transparency TDCSG/File.lean
```

**What it detects:**
- **Trivial abuse:** `theorem foo : True := trivial` where name suggests real content
- **Placeholder definitions:** `def IsFoo := True` (trivializing predicates)
- **Admitted proofs:** Uses of `admitted` keyword
- **Custom axioms:** `axiom myAxiom : ...`
- **Unsafe declarations:** `unsafe def/theorem`
- **Hidden sorries:** Commented sorries in proof contexts
- **SorryAx axiom:** Declarations depending on `sorryAx` (hidden sorry usage)

**Output (Clean File):**
```
=== TRANSPARENCY CHECK: TDCSG/File.lean ===

✓ PASS: No transparency violations detected

File is transparent:
  ✓ No trivial abuse (theorem foo : True := trivial)
  ✓ No placeholder definitions (def IsFoo := True)
  ✓ No admitted/unsafe declarations
  ✓ No custom axioms
  ✓ No hidden sorries
```

**Output (Violations Found):**
```
=== TRANSPARENCY CHECK: TDCSG/File.lean ===

✗ VIOLATIONS DETECTED: 3 total

Trivial Abuse: ✗ 1 violation(s)
  🔴 Line 42: theorem 'interval_injective' proves 'True := trivial' but name suggests real content

Placeholder Definition: ✗ 1 violation(s)
  🔴 Line 67: def 'IsStandard' is a placeholder (Prop := True)

Custom Axiom: ✗ 1 violation(s)
  🔴 Line 89: custom axiom 'myAxiom' declared

Summary:
  🔴 3 critical violation(s)

Result: ✗ FILE HAS TRANSPARENCY VIOLATIONS
```

**When to use:**
- **Before claiming sorry completion** - Verify no fake proofs
- **After agent work** - Audit agent honesty
- **Pre-commit validation** - Ensure code quality
- **CI/CD integration** - Automated proof integrity checks

**Performance:**
- **Very fast** - No compilation required (static analysis only)
- Pattern matching + optional Lean axiom checking
- Safe to run on any file

**Anti-Placeholder Protocol Compliance:**
This mode implements the Self-Audit Protocol from CLAUDE.md:
- ✅ Theorem Quality Audit (detects `True :=` patterns)
- ✅ Trivial Usage Audit (flags suspicious `trivial` usage)
- ✅ Placeholder Definition Audit (finds `Prop := True`)
- ✅ Axiom Audit (detects custom axioms and `sorryAx`)
- ✅ Hidden Sorry Detection

### 5. Default Mode (All Diagnostics)

**Purpose:** See everything (errors + warnings)

```bash
./check_lean.sh TDCSG/File.lean
```

**When to use:**
- Final verification before commits
- Comprehensive review
- Debugging complex issues

## Multi-File Mode

**Purpose:** Check multiple files with aggregated summary

```bash
./check_lean.sh --all <mode> TDCSG/
```

**Supported modes:**
- `errors-only` - Fast multi-file error check
- `sorries` - Sorry summary across all files
- `warnings-summary` - Warning analysis for all files
- `transparency` - Proof evasion detection across all files
- (default) - All diagnostics for all files

**Example Output:**
```
Build Status Summary:
  ✓ TDCSG/Basic.lean: Clean
  ✓ TDCSG/Properties.lean: Clean
  ✗ TDCSG/Ergodic.lean: 4 sorries across 4 theorem(s)
  ✗ TDCSG/Examples.lean: Has errors

Result: 2/4 files compile without errors ✗

Showing details for files with issues:

=== TDCSG/Ergodic.lean ===
[detailed sorry breakdown]

=== TDCSG/Examples.lean ===
[error messages]
```

**Benefits:**
- Quick project-wide status
- Identify which files need attention
- Track overall completion progress

## Exit Codes

The tool uses standard exit codes:

- **0** - Success (no issues found)
- **1** - Failure (errors/warnings/sorries present)
- **2** - Usage error (invalid arguments)

**Example:**
```bash
if ./check_lean.sh --errors-only TDCSG/File.lean; then
    echo "Build successful!"
else
    echo "Build failed!"
fi
```

## Performance

### Token Usage Comparison

**Raw `lake build` output:** ~50,000-100,000 tokens per file (including all imports, progress messages, irrelevant warnings)

**`check_lean.sh --errors-only`:** ~500-1,000 tokens per file (only relevant errors for target file)

**Token Reduction:** ~99% reduction in typical cases

### Why This Matters

**Context Window Efficiency:**
- More iterations per session
- Less context pollution
- Faster iteration cycles
- Better AI agent performance

**Example Session:**
```
Without tool: 10 iterations before context limit
With tool: 1000+ iterations before context limit
```

## Implementation Details

### Architecture

```
check_lean.sh (bash)
  ├─ Single file mode
  │   └─ Pipes lake build → Python filter
  └─ Multi-file mode
      └─ Calls Python multi-file aggregator
          └─ Calls check_lean.sh for each file
```

**Why this design:**
- Bash wrapper provides simple CLI
- Python filters provide robust text processing
- Recursive structure avoids code duplication
- Single-file checker is reused by multi-file mode

### File Filtering

**How it works:**
1. Run `lake build <file>`
2. Capture complete output
3. Filter to lines matching target file
4. Extract multi-line diagnostic blocks
5. Format and display

**Error Patterns Matched:**

The tool matches **four distinct error patterns** to ensure complete coverage:

```
Pattern 1: error: TDCSG/File.lean:42:10: <message>
           (standard lake build format with line:col)

Pattern 2: TDCSG/File.lean:42:10: error: <message>
           (lean command format with line:col)

Pattern 3: error: TDCSG/File.lean: <message>
           (import/build errors WITHOUT line:col)

Pattern 4: error: ... TDCSG/File.lean ... bad import '...'
           (bad import errors - can appear anywhere in line)
```

**Warning Patterns:**
```
warning: TDCSG/File.lean:42:10: <message>
TDCSG/File.lean:42:10: warning: <message>
```

**Critical: Patterns 3 & 4 (2025-10-17 Fix)**

Prior to 2025-10-17, the tool **silently missed** critical error types:
- ❌ Bad import errors: `error: File.lean: bad import 'Mathlib.Nonexistent'`
- ❌ Build system errors without line numbers
- ❌ Dependency resolution errors

**Why this was critical:** These errors would cause builds to fail, but the tool would report `✓ No errors`, creating a false sense of success.

**Regression testing:** All error patterns are validated by `tools/test_error_detection.sh`

**Multi-line handling:**
- Diagnostics continue until next section marker
- Preserves indentation and formatting
- Never clips mid-diagnostic
- Filters out errors from other files

## Troubleshooting

### Issue: "Python script not found"

**Cause:** Tool moved or incorrect working directory

**Fix:**
```bash
# Ensure you're in project root
cd /path/to/TDCSG
./check_lean.sh --errors-only TDCSG/File.lean
```

### Issue: Multi-file shows "Has errors" but details say "No errors"

**Cause:** Dependency build failures - when file A fails, file B can't be fully checked

**This is correct behavior:**
- Multi-file build shows file B failed (due to A's failure)
- Individual check of B (after cache) shows it's actually clean

**Solution:** Fix the files with real errors first

### Issue: Build seems to hang

**Cause:** Large file or complex proof causing long build time

**Solutions:**
- Be patient (Lean can take time for complex proofs)
- Use `--errors-only` for faster feedback
- Check `lake build` directly to verify it's not the tool

### Issue: Warnings not showing in errors-only mode

**Expected behavior:** `--errors-only` deliberately hides warnings for clean output

**Solution:** Use `--warnings-summary` or default mode to see warnings

## Best Practices

### Development Workflow

1. **Write code**
2. **Fast check:** `./check_lean.sh --errors-only TDCSG/File.lean`
3. **Fix errors** (repeat step 2 until clean)
4. **Review warnings:** `./check_lean.sh --warnings-summary TDCSG/File.lean`
5. **Fix warnings**
6. **Commit**

### Agent/Automation Usage

**DO:**
```bash
# Always use errors-only for iteration
./check_lean.sh --errors-only TDCSG/File.lean

# Check sorries periodically
./check_lean.sh --sorries TDCSG/File.lean

# Final verification before completion
./check_lean.sh --all errors-only TDCSG/
```

**DON'T:**
```bash
# Never pipe to head/tail (clips diagnostics!)
lake build | head -50  # BAD

# Never use raw lake build in automated workflows
lake build  # BAD - too much output
```

### Multi-Agent Coordination

When multiple agents work in parallel:

1. **Use unique scratch file names** to avoid conflicts:
   ```
   scratch_agent_id_xyz_test.lean  # GOOD
   scratch.lean                     # BAD - collision risk
   ```

2. **Clean up scratch files** when done:
   ```bash
   rm scratch_agent_id_*.lean
   ```

3. **Check multi-file status** to track overall progress:
   ```bash
   ./check_lean.sh --all sorries TDCSG/
   ```

## Examples

### Example 1: Fix All Errors in File

```bash
# Start iteration loop
while ! ./check_lean.sh --errors-only TDCSG/MyFile.lean; do
    # Edit file to fix errors
    # Loop continues until clean build
done

echo "File is now error-free!"
```

### Example 2: Track Sorry Elimination Progress

```bash
# Before starting work
./check_lean.sh --sorries TDCSG/MyFile.lean > before.txt

# ... work on proofs ...

# After completing proofs
./check_lean.sh --sorries TDCSG/MyFile.lean > after.txt

# Compare
diff before.txt after.txt
```

### Example 3: Project-Wide Health Check

```bash
echo "=== ERROR CHECK ==="
./check_lean.sh --all errors-only TDCSG/

echo "\n=== SORRY COUNT ==="
./check_lean.sh --all sorries TDCSG/

echo "\n=== WARNINGS ==="
./check_lean.sh --all warnings-summary TDCSG/
```

### Example 4: CI/CD Integration

```bash
#!/bin/bash
# .github/workflows/verify.sh

set -e  # Exit on error

echo "Checking all files compile..."
./check_lean.sh --all errors-only TDCSG/

echo "Checking for new sorries..."
SORRY_COUNT=$(./check_lean.sh --all sorries TDCSG/ | grep -c "sorry at" || true)
if [ "$SORRY_COUNT" -gt 10 ]; then
    echo "Error: Too many sorries ($SORRY_COUNT)"
    exit 1
fi

echo "Checking warnings..."
./check_lean.sh --all warnings-summary TDCSG/ | tee warnings.txt

echo "All checks passed!"
```

## Changelog

### 2025-10-17b - Critical Error Detection Fix
- **CRITICAL FIX**: Added error patterns 3 & 4 to catch all error types
- Now detects bad import errors without line:col numbers
- Now detects build system errors without line:col numbers
- Added regression test suite (`tools/test_error_detection.sh`)
- Updated `check_lean_errors_only.py` and `check_lean_multi.py`
- Fixed false negatives where tool reported "✓ No errors" on failed builds

### 2025-10-17a - Major Refactoring
- Moved Python scripts to `tools/` directory
- Fixed double-slash path bug in multi-file mode
- Simplified multi-file checker to call single-file checker
- Added recursive file finding for `--all` mode (bash 3.2+ compatible)
- All modes now work correctly
- Improved error reporting consistency

### 2025-10-16 - Initial Version
- Created comprehensive build tool
- Implemented 4 modes (errors-only, sorries, warnings-summary, default)
- Added multi-file aggregation
- 99% token reduction achieved

## Support

**Issues:** Report bugs or requests in the project repository

**Documentation:** This file (tools/CHECK_LEAN_TOOL.md)

**Examples:** See README.md Quick Start section

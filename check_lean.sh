#!/usr/bin/env bash
#
# check_lean.sh - Build and extract diagnostics for Lean files
#
# Usage:
#   ./check_lean.sh <filename>                      # Show errors AND warnings
#   ./check_lean.sh --errors-only <filename>        # Show ONLY errors
#   ./check_lean.sh --sorries <filename>            # Show sorry summary
#   ./check_lean.sh --warnings-summary <filename>   # Show warning summary
#   ./check_lean.sh --transparency <filename>       # Check for proof evasion
#   ./check_lean.sh --all <mode> <directory>        # Check all files in directory
#
# Examples:
#   ./check_lean.sh ChebyshevCircles/MainTheorem.lean
#   ./check_lean.sh --errors-only ChebyshevCircles/PolynomialConstruction.lean
#   ./check_lean.sh --sorries ChebyshevCircles/MainTheorem.lean
#   ./check_lean.sh --warnings-summary ChebyshevCircles/RootsOfUnity.lean
#   ./check_lean.sh --transparency ChebyshevCircles/MainTheorem.lean
#   ./check_lean.sh --all errors-only ChebyshevCircles/
#   ./check_lean.sh --all transparency ChebyshevCircles/
#
# Returns:
#   - Exit code 0 if no issues found
#   - Exit code 1 if errors/warnings/sorries exist
#   - Exit code 2 for usage errors
#
# This script ensures agents always see ALL relevant diagnostics with full
# context, never clipped by head/tail commands.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Show usage
show_usage() {
    echo "Usage: $0 [MODE] <filename|directory>" >&2
    echo "" >&2
    echo "Modes:" >&2
    echo "  (default)           Show all diagnostics (errors + warnings)" >&2
    echo "  --errors-only       Show only errors (no warnings)" >&2
    echo "  --sorries           Show sorry summary with theorem names" >&2
    echo "  --warnings-summary  Show warning summary grouped by type" >&2
    echo "  --transparency      Check for proof evasion patterns" >&2
    echo "  --all <mode>        Check all .lean files in directory" >&2
    echo "" >&2
    echo "Examples:" >&2
    echo "  $0 ChebyshevCircles/MainTheorem.lean" >&2
    echo "  $0 --errors-only ChebyshevCircles/PolynomialConstruction.lean" >&2
    echo "  $0 --sorries ChebyshevCircles/MainTheorem.lean" >&2
    echo "  $0 --warnings-summary ChebyshevCircles/RootsOfUnity.lean" >&2
    echo "  $0 --transparency ChebyshevCircles/MainTheorem.lean" >&2
    echo "  $0 --all errors-only ChebyshevCircles/" >&2
    echo "  $0 --all sorries ChebyshevCircles/" >&2
    echo "  $0 --all transparency ChebyshevCircles/" >&2
    exit 2
}

# Parse arguments
MODE="default"
TARGET=""

if [ $# -eq 0 ]; then
    show_usage
fi

if [ $# -eq 1 ]; then
    MODE="default"
    TARGET="$1"
elif [ $# -eq 2 ]; then
    if [ "$1" = "--all" ]; then
        show_usage  # --all requires mode and directory (3 args total)
    fi
    MODE="$1"
    TARGET="$2"
elif [ $# -eq 3 ] && [ "$1" = "--all" ]; then
    MODE="$1"
    SUBMODE="$2"
    TARGET="$3"
else
    show_usage
fi

# Handle --all mode (multi-file)
if [ "$MODE" = "--all" ]; then
    # Expand directory to all .lean files (recursively)
    if [ -d "$TARGET" ]; then
        # Remove trailing slash from TARGET to avoid double slashes
        TARGET="${TARGET%/}"
        # Use find to get all .lean files recursively (compatible with bash 3.2+)
        LEAN_FILES=()
        while IFS= read -r file; do
            LEAN_FILES+=("$file")
        done < <(find "$TARGET" -type f -name "*.lean" | sort)

        if [ ${#LEAN_FILES[@]} -eq 0 ]; then
            echo "Error: No .lean files found in $TARGET" >&2
            exit 2
        fi
    else
        echo "Error: $TARGET is not a directory" >&2
        exit 2
    fi

    # Validate submode
    case "$SUBMODE" in
        errors-only|warnings|sorries|warnings-summary|transparency)
            ;;
        *)
            echo "Error: Invalid submode '$SUBMODE' for --all" >&2
            echo "Valid submodes: errors-only, warnings, sorries, warnings-summary, transparency" >&2
            exit 2
            ;;
    esac

    # Run multi-file checker
    PYTHON_SCRIPT="$SCRIPT_DIR/tools/check_lean_multi.py"
    if [ ! -f "$PYTHON_SCRIPT" ]; then
        echo "Error: Python script not found at $PYTHON_SCRIPT" >&2
        exit 2
    fi

    if output=$(python3 "$PYTHON_SCRIPT" "$SUBMODE" "${LEAN_FILES[@]}" 2>&1); then
        echo "$output"
        exit 0
    else
        echo "$output"
        exit 1
    fi
fi

# Single file mode - select appropriate Python script
case "$MODE" in
    default)
        PYTHON_SCRIPT="$SCRIPT_DIR/tools/check_lean_file.py"
        ;;
    --errors-only)
        PYTHON_SCRIPT="$SCRIPT_DIR/tools/check_lean_errors_only.py"
        ;;
    --sorries)
        PYTHON_SCRIPT="$SCRIPT_DIR/tools/check_lean_sorries.py"
        ;;
    --warnings-summary)
        PYTHON_SCRIPT="$SCRIPT_DIR/tools/check_lean_warnings_summary.py"
        ;;
    --transparency)
        PYTHON_SCRIPT="$SCRIPT_DIR/tools/check_lean_transparency.py"
        ;;
    *)
        echo "Error: Unknown mode '$MODE'" >&2
        show_usage
        ;;
esac

# Verify Python script exists
if [ ! -f "$PYTHON_SCRIPT" ]; then
    echo "Error: Python script not found at $PYTHON_SCRIPT" >&2
    exit 2
fi

# Verify target file exists
if [ ! -f "$TARGET" ]; then
    echo "Error: File not found: $TARGET" >&2
    exit 2
fi

# Transparency mode doesn't need lake build - just run the checker
if [ "$MODE" = "--transparency" ]; then
    if output=$(python3 "$PYTHON_SCRIPT" "$TARGET" 2>&1); then
        echo "$output"
        exit 0
    else
        echo "$output"
        exit 1
    fi
fi

# Build the file and pipe through Python filter
if output=$(lake build "$TARGET" 2>&1 | python3 "$PYTHON_SCRIPT" "$TARGET" 2>&1); then
    # Success case
    echo "$output"
    exit 0
else
    # Failure case (has diagnostics)
    echo "$output"
    exit 1
fi

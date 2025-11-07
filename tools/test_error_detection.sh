#!/usr/bin/env bash
#
# Regression tests for check_lean_errors_only.py error pattern matching
#
# This test suite verifies that the error detection catches all error types:
# 1. Errors with line:col numbers (standard format)
# 2. Bad import errors (no line:col)
# 3. Build system errors
# 4. Errors from other files are correctly filtered out
#

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
TEST_FILE="TDCSG/TestFile.lean"

echo "=== Error Detection Regression Tests ==="
echo

# Test 1: Standard error format (with line:col)
echo "Test 1: Standard error with line:col"
TEST_OUTPUT=$(cat <<'EOF'
⚠ [1/10] Building TestFile
error: TDCSG/TestFile.lean:42:10: Unknown identifier 'foo'
Some additional context about the error
EOF
)
RESULT=$(echo "$TEST_OUTPUT" | python3 "$SCRIPT_DIR/check_lean_errors_only.py" "$TEST_FILE")
if echo "$RESULT" | grep -q "Unknown identifier"; then
    echo "✓ PASS: Caught standard error with line:col"
else
    echo "✗ FAIL: Missed standard error"
    exit 1
fi
echo

# Test 2: Bad import error (no line:col)
echo "Test 2: Bad import error (no line:col)"
TEST_OUTPUT=$(cat <<'EOF'
⚠ [1/10] Building TestFile
error: TDCSG/TestFile.lean: bad import 'Mathlib.Nonexistent.Module'
Additional diagnostic info
EOF
)
RESULT=$(echo "$TEST_OUTPUT" | python3 "$SCRIPT_DIR/check_lean_errors_only.py" "$TEST_FILE")
if echo "$RESULT" | grep -q "bad import"; then
    echo "✓ PASS: Caught bad import error"
else
    echo "✗ FAIL: Missed bad import error"
    exit 1
fi
echo

# Test 3: Errors from other files should be filtered out
echo "Test 3: Filter errors from other files"
TEST_OUTPUT=$(cat <<'EOF'
⚠ [1/10] Building TestFile
error: TDCSG/OtherFile.lean:10:5: Type mismatch
error: TDCSG/TestFile.lean:42:10: Our error
error: TDCSG/AnotherFile.lean: bad import 'Foo'
EOF
)
RESULT=$(echo "$TEST_OUTPUT" | python3 "$SCRIPT_DIR/check_lean_errors_only.py" "$TEST_FILE")
if echo "$RESULT" | grep -q "Our error" && \
   ! echo "$RESULT" | grep -q "OtherFile" && \
   ! echo "$RESULT" | grep -q "AnotherFile"; then
    echo "✓ PASS: Correctly filtered other files' errors"
else
    echo "✗ FAIL: Didn't filter properly"
    echo "Result: $RESULT"
    exit 1
fi
echo

# Test 4: Warnings should be ignored in errors-only mode
echo "Test 4: Warnings should be filtered out"
TEST_OUTPUT=$(cat <<'EOF'
warning: TDCSG/TestFile.lean:10:5: unused variable
error: TDCSG/TestFile.lean:42:10: Type error
warning: TDCSG/TestFile.lean:50:1: declaration uses 'sorry'
EOF
)
RESULT=$(echo "$TEST_OUTPUT" | python3 "$SCRIPT_DIR/check_lean_errors_only.py" "$TEST_FILE")
if echo "$RESULT" | grep -q "Type error" && \
   ! echo "$RESULT" | grep -q "warning" && \
   ! echo "$RESULT" | grep -q "unused"; then
    echo "✓ PASS: Warnings correctly filtered"
else
    echo "✗ FAIL: Warnings not filtered"
    echo "Result: $RESULT"
    exit 1
fi
echo

# Test 5: No errors should report success
echo "Test 5: No errors = success"
TEST_OUTPUT=$(cat <<'EOF'
⚠ [1/10] Building TestFile
warning: TDCSG/TestFile.lean:10:5: unused variable
Build completed successfully
EOF
)
RESULT=$(echo "$TEST_OUTPUT" | python3 "$SCRIPT_DIR/check_lean_errors_only.py" "$TEST_FILE")
if echo "$RESULT" | grep -q "✓.*No errors"; then
    echo "✓ PASS: Correctly reports no errors"
else
    echo "✗ FAIL: Should report no errors"
    echo "Result: $RESULT"
    exit 1
fi
echo

echo "=== All Tests Passed ✓ ==="

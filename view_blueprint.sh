#!/usr/bin/env bash
# Script to build and view the Lean blueprint locally

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Configuration
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
BLUEPRINT_DIR="$SCRIPT_DIR/blueprint"
WEB_DIR="$BLUEPRINT_DIR/src/web"
PORT=8000

echo -e "${BLUE}Chebyshev Circles - Blueprint Viewer${NC}"
echo "======================================"
echo

# Check if blueprint directory exists
if [ ! -d "$BLUEPRINT_DIR" ]; then
    echo -e "${RED}Error: Blueprint directory not found at $BLUEPRINT_DIR${NC}"
    exit 1
fi

cd "$BLUEPRINT_DIR"

# Check if web files exist
if [ ! -d "$WEB_DIR" ] || [ -z "$(ls -A $WEB_DIR 2>/dev/null)" ]; then
    echo -e "${YELLOW}Blueprint web files not found. Building...${NC}"
    echo

    # Activate virtual environment if it exists
    if [ -d "$SCRIPT_DIR/.venv" ]; then
        echo "Activating Python virtual environment..."
        source "$SCRIPT_DIR/.venv/bin/activate"
    fi

    # Build the web version
    echo "Building blueprint (this may take a moment)..."
    if leanblueprint web; then
        echo -e "${GREEN}✓ Blueprint built successfully${NC}"
        echo
    else
        echo -e "${RED}✗ Failed to build blueprint${NC}"
        echo "Try running: cd blueprint && leanblueprint web"
        exit 1
    fi
else
    echo -e "${GREEN}✓ Blueprint web files found${NC}"
    echo
fi

# Check if port is already in use
if lsof -Pi :$PORT -sTCP:LISTEN -t >/dev/null 2>&1; then
    echo -e "${YELLOW}Warning: Port $PORT is already in use${NC}"
    echo "Finding an available port..."
    PORT=$((PORT + 1))
    while lsof -Pi :$PORT -sTCP:LISTEN -t >/dev/null 2>&1; do
        PORT=$((PORT + 1))
    done
    echo -e "${GREEN}Using port $PORT${NC}"
    echo
fi

# Start the server
echo -e "${GREEN}Starting local web server...${NC}"
echo
echo -e "${BLUE}Blueprint is now available at:${NC}"
echo -e "${GREEN}http://localhost:$PORT${NC}"
echo
echo "Press Ctrl+C to stop the server"
echo "========================================"
echo

# Change to web directory and start server
cd "$WEB_DIR"

# Trap Ctrl+C to provide clean exit message
trap 'echo -e "\n${YELLOW}Shutting down server...${NC}"; exit 0' INT

python3 -m http.server $PORT

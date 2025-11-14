#!/bin/bash
# Batch rendering script for all Chebyshev polynomial animations
# Renders all N values (3-10, 12, 15, 20) at high quality (1080x1920 @ 60fps)

set -e  # Exit on error

echo "========================================="
echo "Chebyshev Polynomial Animation Rendering"
echo "========================================="
echo ""

# Activate virtual environment
source .venv/bin/activate

# N values to render
N_VALUES=(3 4 5 6 7 8 9 10 12 15 20)

# Quality flag removed - manim.cfg controls all settings now

# Total scenes
TOTAL=${#N_VALUES[@]}
CURRENT=0

echo "Rendering $TOTAL scenes at high quality (1080x1920 @ 60fps)"
echo "This may take 30-60 minutes depending on your system..."
echo ""

# Render each scene
for N in "${N_VALUES[@]}"; do
    CURRENT=$((CURRENT + 1))
    echo "[$CURRENT/$TOTAL] Rendering N=$N..."

    manim chebyshev_manim.py Chebyshev_N${N}

    if [ $? -eq 0 ]; then
        echo "✓ N=$N completed successfully"
    else
        echo "✗ N=$N FAILED"
        exit 1
    fi

    echo ""
done

echo "========================================="
echo "All animations rendered successfully!"
echo "========================================="
echo ""
echo "Output location: media/videos/chebyshev_manim/"
echo ""
echo "File listing:"
ls -lh media/videos/chebyshev_manim/Chebyshev_N*/Chebyshev_N*.mp4 | awk '{print $9, "(" $5 ")"}'
echo ""
echo "Total size:"
du -sh media/videos/chebyshev_manim/
echo ""

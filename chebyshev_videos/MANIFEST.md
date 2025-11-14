# Chebyshev Circles Video Manifest

## Video Specifications

**Format:** 1080x1920 (portrait, 9:16 aspect ratio)
**Frame Rate:** 60 fps
**Codec:** H.264/MP4
**Background:** White
**Rendering Engine:** Manim Community Edition v0.19.0+

All videos use anti-aliased graphics with professional LaTeX typography.

## Animation Design

**Rotation:** Full 2π radians (complete circle)
**Oscillation Frequency:** 0.1 Hz (one polynomial oscillation every 10 seconds)
**Angular Velocity:** 2π/(N×10) rad/s (varies with N to maintain constant oscillation tempo)

Each video shows N complete polynomial oscillations as the roots rotate through a full 2π radians. This ensures consistent visual rhythm: regardless of N, viewers see one oscillation cycle every 10 seconds.

## Video Duration Formula

```
duration(N) = N × 10.0 seconds
```

**Reasoning:**
- Full 2π rotation creates N polynomial oscillations
- To show N oscillations at 0.1 Hz: time = N / 0.1 = 10N seconds

## Available Videos

| N | Filename | Duration | Total Frames | Oscillations Shown | Angular Velocity |
|---|----------|----------|--------------|--------------------|--------------------|
| 3 | chebyshev_N3.mp4 | 30.0s | 1800 | 3 | 2π/30 ≈ 0.209 rad/s |
| 4 | chebyshev_N4.mp4 | 40.0s | 2400 | 4 | 2π/40 ≈ 0.157 rad/s |
| 5 | chebyshev_N5.mp4 | 50.0s | 3000 | 5 | 2π/50 ≈ 0.126 rad/s |
| 6 | chebyshev_N6.mp4 | 60.0s | 3600 | 6 | 2π/60 ≈ 0.105 rad/s |
| 10 | chebyshev_N10.mp4 | 100.0s | 6000 | 10 | 2π/100 ≈ 0.063 rad/s |

## Visual Elements

All videos display:

**Geometric Elements:**
- **Unit circle** (gray, 3px stroke) - Reference circle in complex plane
- **N-gon** (coral #FF4444, 4.5px stroke) - Regular polygon connecting roots, rotates with them
- **Root dots** (red #C81010, ~8pt radius) - N-th roots of unity on unit circle, rotating by angle φ
- **Projection lines** (pink #FF9090, 3px stroke, 40% opacity) - Vertical lines from roots to x-axis
- **Projection dots** (pink #FF5050, ~6pt radius, 70% opacity) - Projected roots on x-axis, serve as polynomial roots
- **Polynomial curve** (blue #1850A0, 6px stroke) - The scaled polynomial S(x) with projected roots

**Text Overlay** (top-left corner, black text):
1. **Line 1:** "N = {N} Roots of Unity" (40pt)
2. **Line 2:** "φ = 0.000 rad | Scaling: 2^(N-1) = {value}" (32pt)
   - φ displayed in radians with format: 4 significant figures, 3 decimal places, leading zero
3. **Line 3:** "S(x) = {polynomial}" (28pt, adaptive sizing for high N)
   - Real-time polynomial equation with exact integer coefficients and floating-point constant
4. **Line 4:** "= T_N(x) + c" (32pt)
   - Explicit reference to Chebyshev polynomial relationship

## Polynomial Display

The polynomial S(x) is computed in real-time as:

```
S(x) = 2^(N-1) × ∏(x - cos(φ + 2πk/N))  for k = 0, ..., N-1
```

For high N values (N ≥ 12), the polynomial display intelligently truncates middle terms:
```
S(x) = leading_terms ... trailing_terms
```

This maintains readability while showing the general form.

## Technical Implementation

**Polynomial Rendering:**
- `ParametricFunction` with dense sampling (dt=0.002, ~500 samples)
- Eliminates aliasing artifacts even at high N values (tested N=3 to N=20)
- Y-range clipping to [-2.5, 2.5] for portrait format

**Animation Updates:**
- `always_redraw()` updaters for all dynamic elements
- `ValueTracker` for smooth rotation angle progression
- Linear rate function for constant angular velocity

**Z-Index Layering** (back to front):
1. z=0: Coordinate axes
2. z=1: Unit circle
3. z=2: Projection lines
4. z=3: N-gon polygon
5. z=4-5: Dots (roots and projections)
6. z=6: Polynomial curve
7. z=9: Text overlays (always on top)

## Generation

### Render All Videos

```bash
# Navigate to project root
cd /path/to/ChebyshevCircles

# Activate virtual environment
source .venv/bin/activate

# Render videos (uses manim.cfg for portrait format)
for N in 3 4 5 6 10; do
    echo "Rendering N=$N..."
    manim chebyshev_manim.py Chebyshev_N${N}
    cp media/videos/chebyshev_manim/Chebyshev_N${N}/Chebyshev_N${N}.mp4 chebyshev_videos/
done

# Verify all videos
for N in 3 4 5 6 10; do
    ffprobe -v error -select_streams v:0 -show_entries stream=width,height,r_frame_rate,duration \
        -of default=noprint_wrappers=1 chebyshev_videos/chebyshev_N${N}.mp4
done
```

### Extract Frames for Paper Figures

Use the unified extraction tool to generate portrait-oriented PNG frames:

```bash
# Extract all paper figures (N=3,5,10 at φ=0)
python extract_frames_from_videos.py --batch-paper-figures

# Or extract individual frames
python extract_frames_from_videos.py \
    --video chebyshev_videos/chebyshev_N5.mp4 \
    --time 0.0 \
    --output paper_figures/figure_N5_phi0.png \
    --pdf
```

Frames are extracted at timestamp t=0.0 seconds (φ=0 radians).

## File Sizes

Approximate video file sizes (may vary based on compression):

- N=3 (30s): ~3-5 MB
- N=4 (40s): ~4-6 MB
- N=5 (50s): ~5-7 MB
- N=6 (60s): ~6-8 MB
- N=10 (100s): ~10-14 MB

Total: ~30-40 MB for all 5 videos

## Usage Notes

- Videos are optimized for portrait viewing (mobile-friendly)
- Autoplay compatible (no audio track)
- Suitable for web embedding with `<video>` tag
- Paper figures maintain same portrait orientation

## Quality Assurance

All videos have been verified for:
- ✓ Correct dimensions (1080x1920)
- ✓ Correct frame rate (60 fps)
- ✓ Correct duration (N × 10 seconds)
- ✓ Radians display format (φ = 0.000 rad)
- ✓ Full 2π rotation
- ✓ Smooth polynomial curve (no artifacts)
- ✓ Proper text overlay visibility

## Version History

**v2.0 (2025-11-14)**
- Unified animation system: all N values show full 2π rotation
- Radians display format for all videos (φ = 0.000 rad)
- Equal oscillation frequency (0.1 Hz) across all N values
- Duration scales with N: N × 10 seconds
- Replaced 3 legacy extraction scripts with unified tool

**v1.0 (2025-11-13)**
- Initial portrait format videos
- N=3 special case with full rotation and radians
- Other N values showed ~1 oscillation with degree display

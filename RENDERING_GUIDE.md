# Chebyshev Manim Rendering Guide

Quick reference for rendering animations with the new Manim implementation.

## Quick Start

### Render Single Scene (Preview Quality)
```bash
manim -ql chebyshev_manim.py Chebyshev_N3
```

Opens preview automatically after rendering.

### Render High Quality (1080x1920 @ 60fps)
```bash
manim -qh chebyshev_manim.py Chebyshev_N3
```

### Render All N Values
```bash
for N in 3 4 5 6 7 8 9 10 12 15 20; do
    manim -qh chebyshev_manim.py Chebyshev_N${N}
done
```

## Available Scenes

| Scene Class | N Value | Duration | Rotation |
|-------------|---------|----------|----------|
| Chebyshev_N3 | 3 | 10.0s | 120° |
| Chebyshev_N4 | 4 | 13.3s | 90° |
| Chebyshev_N5 | 5 | 16.7s | 72° |
| Chebyshev_N6 | 6 | 20.0s | 60° |
| Chebyshev_N7 | 7 | 23.3s | 51.4° |
| Chebyshev_N8 | 8 | 26.7s | 45° |
| Chebyshev_N9 | 9 | 30.0s | 40° |
| Chebyshev_N10 | 10 | 33.3s | 36° |
| Chebyshev_N12 | 12 | 40.0s | 30° |
| Chebyshev_N15 | 15 | 50.0s | 24° |
| Chebyshev_N20 | 20 | 66.7s | 18° |

## Quality Flags

- `-ql` : Low quality (854x480, 15fps) - Fast preview
- `-qm` : Medium quality (1280x720, 30fps)
- `-qh` : High quality (1080x1920, 60fps) - Production
- `-qk` : 4K quality (2160x3840, 60fps)

## Output Locations

Videos save to:
```
media/videos/chebyshev_manim/Chebyshev_N{N}/Chebyshev_N{N}.mp4
```

Example:
```
media/videos/chebyshev_manim/Chebyshev_N10/Chebyshev_N10.mp4
```

## Additional Flags

### Save Last Frame as Image
```bash
manim -qh -s chebyshev_manim.py Chebyshev_N3
```
Saves to: `media/images/chebyshev_manim/Chebyshev_N3.png`

### Render Without Preview
```bash
manim -qh --disable_caching chebyshev_manim.py Chebyshev_N3
```

### Transparent Background
```bash
manim -qh --transparent chebyshev_manim.py Chebyshev_N3
```

## Configuration

Settings in `manim.cfg`:
- **Format**: 1080x1920 (9:16 portrait)
- **Frame rate**: 60fps
- **Background**: White
- **Quality**: high_quality preset

To modify, edit `manim.cfg` or use CLI flags.

## Troubleshooting

### "ModuleNotFoundError: No module named 'manim'"
```bash
# Activate virtual environment
source .venv/bin/activate

# Or install manim
pip install manim
```

### Slow Rendering
Normal behavior. High N values render slowly due to dense polynomial sampling:
- N=3: ~6s (low quality)
- N=10: ~32s (low quality)
- N=20: ~72s (low quality)

High quality (-qh) takes 3-4x longer.

### LaTeX Errors
Current implementation uses Text objects (no LaTeX required). If you see LaTeX errors, verify you're using the latest `chebyshev_manim.py` which avoids LaTeX dependencies.

## Batch Processing

### Render specific N values
```bash
for N in 3 6 10 20; do
    manim -qh chebyshev_manim.py Chebyshev_N${N}
done
```

### Render with custom output names
```bash
manim -qh -o N3_chebyshev.mp4 chebyshev_manim.py Chebyshev_N3
```

### Convert to GIF (requires ffmpeg)
```bash
ffmpeg -i media/videos/chebyshev_manim/Chebyshev_N3/Chebyshev_N3.mp4 \
       -vf "fps=15,scale=540:-1:flags=lanczos" \
       -loop 0 chebyshev_N3.gif
```

## Performance Tips

1. **Preview first**: Always test with `-ql` before high-quality render
2. **Selective rendering**: Only render N values you need
3. **Caching**: Manim caches partial renders, don't disable unless needed
4. **Parallel rendering**: Run multiple manim processes for different N values simultaneously (on multi-core systems)

## Example Workflow

```bash
# 1. Test implementation
manim -ql chebyshev_manim.py Chebyshev_N3

# 2. Verify polynomial rendering quality
manim -ql chebyshev_manim.py Chebyshev_N10
manim -ql chebyshev_manim.py Chebyshev_N20

# 3. Render production versions
manim -qh chebyshev_manim.py Chebyshev_N3
manim -qh chebyshev_manim.py Chebyshev_N10
manim -qh chebyshev_manim.py Chebyshev_N20

# 4. Batch render remaining scenes
for N in 4 5 6 7 8 9 12 15; do
    manim -qh chebyshev_manim.py Chebyshev_N${N}
done
```

---

**For detailed implementation notes, see:** `MANIM_IMPLEMENTATION_REPORT.md`

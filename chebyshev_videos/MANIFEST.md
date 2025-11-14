# Chebyshev Circles Video Manifest

This directory contains high-quality Manim-generated animations visualizing the geometric construction of Chebyshev polynomials through rotated roots of unity.

## Video Specifications

- **Format:** MP4 (H.264 video codec)
- **Resolution:** 1080x1920 pixels (portrait orientation)
- **Frame Rate:** 60 fps
- **Aspect Ratio:** 9:16 (mobile-friendly)
- **Duration:** 9 seconds per full rotation cycle
- **Generator:** Manim Community Edition v0.19.0+

## Available Videos

| Filename | N Value | Description |
|----------|---------|-------------|
| `chebyshev_N3.mp4` | 3 | Triangle (3rd roots of unity) |
| `chebyshev_N10.mp4` | 10 | Decagon (10th roots of unity) |

## Video Content

Each animation shows:
- **Regular N-gon:** Visual overlay connecting the N roots of unity, rotating in sync
- **Roots of Unity:** N red points on the unit circle rotating continuously
- **Projection Lines:** Vertical lines from each root to its projection on the real axis
- **Projected Roots:** Pink points on the real axis where the vertical projections land
- **Polynomial Curve:** Blue curve representing the scaled polynomial S(x) = 2^(N-1) · P(x)
- **Polynomial Equation:** LaTeX-rendered equation showing S(x) = T_N(x) + c(φ), updated in real-time
- **Rotation Angle:** φ parameter displayed and updated continuously

## Generation Details

Videos were rendered using the Manim Community Edition at 60 fps with the following configuration:
- 9-second rotation cycle with normalized angular velocity
- Anti-aliased graphics and professional LaTeX typography
- White background with high-contrast colors for clarity

All mathematical expressions are rendered with exact coefficients, showing the explicit relationship between the rotated roots and Chebyshev polynomials.

## Source Code

Animation code is located in the root directory:
- `chebyshev_manim.py` - Manim scene definitions
- `manim.cfg` - Manim configuration with video specifications

To render additional N values, modify `N_VALUES` in `chebyshev_manim.py` and run:
```bash
manim chebyshev_manim.py Chebyshev_N{N}
```

Videos will be saved to `media/videos/chebyshev_manim/Chebyshev_N{N}/Chebyshev_N{N}.mp4`

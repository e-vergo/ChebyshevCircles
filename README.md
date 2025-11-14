# Chebyshev Circles

[![CI](https://github.com/e-vergo/ChebyshevCircles/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/e-vergo/ChebyshevCircles/actions)
[![Documentation](https://img.shields.io/badge/docs-passing-brightgreen)](https://e-vergo.github.io/ChebyshevCircles/)
[![License](https://img.shields.io/badge/license-Apache%202.0-blue.svg)](LICENSE)

When the N-th roots of unity are rotated by angle φ and projected onto the real axis and then taken to be the roots of a polynomial, after scaling by 2^(N-1) the polynomial formed from these projections equals the N-th Chebyshev polynomial of the first kind plus a φ-dependent constant.

```lean
theorem rotated_roots_yield_chebyshev (N : ℕ) (φ : ℝ) (hN : 0 < N) :
    ∃ (c : ℝ), scaledPolynomial N φ = Polynomial.Chebyshev.T ℝ N + C c
```

**Construction:**
- Projected roots: `cos(φ + 2πk/N)` for k = 0, ..., N-1
- Unscaled polynomial: `P(x) = ∏(x - cos(φ + 2πk/N))`
- Scaled polynomial: `S(x) = 2^(N-1) · P(x)`
- Result: `S(x) = T_N(x) + c(φ)`

## Visualization

The geometric intuition behind this theorem is best understood through animation. When roots of unity are rotated and projected onto the real axis, the resulting polynomial maintains a fixed shape (the Chebyshev polynomial) while only its constant term varies with the rotation angle.

**Video Specifications:**
- **Format:** 1080x1920 @ 60fps (portrait orientation, mobile-friendly)
- **Duration:** N × 10 seconds (e.g., 30s for N=3, 50s for N=5, 100s for N=10)
- **Quality:** Manim Community Edition with anti-aliased graphics and professional LaTeX typography

**Animation Features:**
- **Regular N-gon:** Visual overlay connecting the N roots of unity, rotating in sync
- **Normalized Speed:** All animations use consistent angular velocity
- **Real-time Math:** LaTeX-rendered polynomial equation with exact coefficients
- **Chebyshev Link:** Explicit reference showing S(x) = T_N(x) + c relationship
- **Scaling Display:** Shows the 2^(N-1) scaling factor applied to the polynomial
- **High Quality:** Smooth video with anti-aliased graphics and professional typography

<details>
<summary>Example: N=3 (Triangle)</summary>

Animation showing N=3 roots of unity being rotated. The regular triangle (coral edges) rotates with the roots (red points). Vertical projection lines show how roots project to the real axis (pink points), which serve as roots for the blue polynomial curve. The displayed polynomial equation updates in real-time, showing that the curve's shape remains a 3rd-degree Chebyshev polynomial (T₃(x)) while only the constant term c changes with rotation angle φ.

**View video:** [`chebyshev_videos/chebyshev_N3.mp4`](chebyshev_videos/chebyshev_N3.mp4)

See [`chebyshev_videos/MANIFEST.md`](chebyshev_videos/MANIFEST.md) for complete video list and specifications.

</details>

## Mathematical Background

**Chebyshev Polynomials** of the first kind, denoted T_N(x), are orthogonal polynomials defined by the recurrence:
- T_0(x) = 1
- T_1(x) = x
- T_{n+1}(x) = 2x·T_n(x) - T_{n-1}(x)

They satisfy T_N(cos θ) = cos(Nθ) and have leading coefficient 2^(N-1) for N ≥ 1.

**Why This Connection Matters:** This theorem reveals a surprising geometric interpretation of Chebyshev polynomials. Rather than defining them via recurrence relations or cosine composition, we can construct them by:
1. Taking N equally-spaced points on the unit circle
2. Rotating them by any angle φ
3. Projecting onto the real axis
4. Building the monic polynomial with these projections as roots
5. Scaling by 2^(N-1)

The result is always T_N(x) plus a constant. This provides a bridge between:
- **Discrete geometry** (roots of unity on the circle)
- **Harmonic analysis** (discrete orthogonality relations)
- **Polynomial theory** (Chebyshev polynomials)

## Project Organization

This project comprises four main components:

1. **Research Paper** (`paper/`) - A traditional mathematics paper presenting the main theorem and complete proofs in classical mathematical notation (14 pages, LaTeX)
2. **Formal Verification** (`ChebyshevCircles/`) - Complete Lean 4 formalization across 10 modules totaling 3,457 lines
3. **Blueprint** (`blueprint/`) - Interactive documentation showing the dependency structure and formalization status
4. **Visualizations** (Manim animations) - High-quality video animations demonstrating the geometric construction

### Research Paper

A publication-ready mathematics paper is available in the `paper/` directory:

- **Paper:** [chebyshev_circles.pdf](paper/chebyshev_circles.pdf) (14 pages)
- **Source:** LaTeX with full bibliography
- **Style:** Traditional mathematics exposition (no mention of formal verification)
- **Target Audience:** General mathematical audience (graduate level)
- **Status:** Ready for arXiv submission or journal review

The paper presents the theorem, complete proofs, numerical examples, and discusses connections to discrete Fourier analysis and Chebyshev-Gauss quadrature. See [paper/README.md](paper/README.md) for compilation instructions.

### Lean 4 Formalization

The complete verification is structured into 10 modules totaling 3,457 lines of Lean 4 code:

| Module | Lines | Purpose |
|--------|-------|---------|
| [RootsOfUnity.lean](ChebyshevCircles/RootsOfUnity.lean) ([docs](https://e-vergo.github.io/ChebyshevCircles/docs/ChebyshevCircles/RootsOfUnity.html)) | 108 | Root definitions and list properties |
| [PolynomialConstruction.lean](ChebyshevCircles/PolynomialConstruction.lean) ([docs](https://e-vergo.github.io/ChebyshevCircles/docs/ChebyshevCircles/PolynomialConstruction.html)) | 541 | Polynomial construction from roots |
| [TrigonometricIdentities.lean](ChebyshevCircles/TrigonometricIdentities.lean) ([docs](https://e-vergo.github.io/ChebyshevCircles/docs/ChebyshevCircles/TrigonometricIdentities.html)) | 137 | Trigonometric sum identities |
| [ChebyshevRoots.lean](ChebyshevCircles/ChebyshevRoots.lean) ([docs](https://e-vergo.github.io/ChebyshevCircles/docs/ChebyshevCircles/ChebyshevRoots.html)) | 235 | Chebyshev root characterization |
| [PowerSums.lean](ChebyshevCircles/PowerSums.lean) ([docs](https://e-vergo.github.io/ChebyshevCircles/docs/ChebyshevCircles/PowerSums.html)) | 705 | Power sum φ-invariance |
| [NewtonIdentities.lean](ChebyshevCircles/NewtonIdentities.lean) ([docs](https://e-vergo.github.io/ChebyshevCircles/docs/ChebyshevCircles/NewtonIdentities.html)) | 317 | Newton's identities framework |
| [PolynomialProperties.lean](ChebyshevCircles/PolynomialProperties.lean) ([docs](https://e-vergo.github.io/ChebyshevCircles/docs/ChebyshevCircles/PolynomialProperties.html)) | 130 | Polynomial degree and coefficient properties |
| [PowerSumEquality.lean](ChebyshevCircles/PowerSumEquality.lean) ([docs](https://e-vergo.github.io/ChebyshevCircles/docs/ChebyshevCircles/PowerSumEquality.html)) | 273 | General power sum equality |
| [ChebyshevOrthogonality.lean](ChebyshevCircles/ChebyshevOrthogonality.lean) ([docs](https://e-vergo.github.io/ChebyshevCircles/docs/ChebyshevCircles/ChebyshevOrthogonality.html)) | 538 | Discrete orthogonality relations |
| [MainTheorem.lean](ChebyshevCircles/MainTheorem.lean) ([docs](https://e-vergo.github.io/ChebyshevCircles/docs/ChebyshevCircles/MainTheorem.html)) | 473 | Main theorem and supporting results |

## Proof Strategy

The verification follows a carefully structured approach:

**Step 1: Root Characterization**
Both the rotated roots and Chebyshev roots can be expressed as cosines of equally-spaced angles (modulo phase shifts). This parallel structure is established in [`ChebyshevRoots.lean`](https://e-vergo.github.io/ChebyshevCircles/docs/ChebyshevCircles/ChebyshevRoots.html).

**Step 2: Power Sum Invariance**
The key insight: For any polynomial, power sums of its roots determine all coefficients (via Newton's identities). We prove in [`PowerSums.lean`](https://e-vergo.github.io/ChebyshevCircles/docs/ChebyshevCircles/PowerSums.html) that:
```lean
∑_{k=0}^{N-1} cos(φ + 2πk/N)^m = ∑_{k=0}^{N-1} cos(2πk/N)^m
```
for all m > 0 ([`powerSumCos_invariant`](https://e-vergo.github.io/ChebyshevCircles/docs/ChebyshevCircles/PowerSums.html#powerSumCos_invariant)). This shows the rotated roots and unrotated roots have identical power sums (except m=0).

**Step 3: Discrete Orthogonality**
The power sum equality relies on discrete orthogonality of complex exponentials over N-th roots of unity. [`ChebyshevOrthogonality.lean`](https://e-vergo.github.io/ChebyshevCircles/docs/ChebyshevCircles/ChebyshevOrthogonality.html) proves:
```lean
∑_{k=0}^{N-1} exp(i·j·2πk/N) = 0  (when j ≠ 0 mod N)
```
([`sum_exp_chebyshev_angles`](https://e-vergo.github.io/ChebyshevCircles/docs/ChebyshevCircles/ChebyshevOrthogonality.html#sum_exp_chebyshev_angles)). This is the discrete analog of continuous Fourier orthogonality.

**Step 4: Newton's Identities**
[`NewtonIdentities.lean`](https://e-vergo.github.io/ChebyshevCircles/docs/ChebyshevCircles/NewtonIdentities.html) implements the bridge between power sums and elementary symmetric polynomials (which determine polynomial coefficients). For polynomials of the same degree with identical power sums (except the 0-th), all coefficients match except the constant term ([`esymm_eq_of_psum_eq`](https://e-vergo.github.io/ChebyshevCircles/docs/ChebyshevCircles/NewtonIdentities.html#esymm_eq_of_psum_eq)).

**Step 5: Assembly**
[`MainTheorem.lean`](https://e-vergo.github.io/ChebyshevCircles/docs/ChebyshevCircles/MainTheorem.html) combines these results: since scaled polynomials from rotated and unrotated roots have identical non-constant coefficients and the same degree, they differ only by a constant ([`rotated_roots_yield_chebyshev`](https://e-vergo.github.io/ChebyshevCircles/docs/ChebyshevCircles/MainTheorem.html#rotated_roots_yield_chebyshev)). The unrotated case (φ=0) is shown to equal T_N.

**Technical Challenges Overcome:**
- Handling complex/real conversions in power sum computations
- Proving non-degeneracy of roots (no duplicates) for polynomial construction
- Managing index arithmetic modulo N in discrete sums
- Careful degree tracking to apply Newton's identities correctly

### Blueprint

An interactive formalization blueprint is available in the `blueprint/` directory:

- **Blueprint:** [View online](https://e-vergo.github.io/ChebyshevCircles/blueprint/) (once deployed)
- **View Locally:** Run `./view_blueprint.sh` from the project root (automatically builds and serves)
- **Features:**
  - Dependency graph visualization showing how lemmas connect
  - Formalization status tracking (which theorems are proven)
  - Cross-references between mathematical exposition and Lean code
  - Interactive navigation through the proof structure
- **Manual Building:** See [blueprint/BP_README.md](blueprint/BP_README.md) for detailed instructions

The blueprint provides a "map" of the formalization, making it easier to understand the proof architecture and see which parts correspond to the paper. It's particularly useful for:
- Understanding the dependency structure before diving into the code
- Tracking formalization progress for contributors
- Bridging between traditional mathematics and formal proofs

## Prerequisites

**Mathematical Background:**
- Undergraduate algebra: polynomials, roots, symmetric functions
- Complex numbers and exponentials
- Trigonometric identities
- Familiarity with orthogonal polynomials (helpful but not required)

**Software Requirements:**
- [Lean 4](https://leanprover.github.io/) (v4.25.0-rc2)
- [Lake](https://github.com/leanprover/lake) (Lean's build tool, included with Lean)
- [Manim Community Edition](https://www.manim.community/) (v0.19.0+) - for visualizations
- [FFmpeg](https://ffmpeg.org/) - required by Manim for video rendering
- [LaTeX](https://www.latex-project.org/) - required by Manim for mathematical typography
  - macOS: [MacTeX](https://www.tug.org/mactex/) or `brew install --cask mactex-no-gui`
  - Linux: `sudo apt-get install texlive-full` or equivalent
  - Windows: [MiKTeX](https://miktex.org/) or [TeX Live](https://www.tug.org/texlive/)

**Expected Build Time:** ~5-10 minutes on first build (compiles Mathlib dependencies)

## Installation

### Lean 4 Verification

1. **Install Lean 4:**
   ```bash
   # Via elan (recommended)
   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
   ```

2. **Clone and build:**
   ```bash
   git clone https://github.com/e-vergo/ChebyshevCircles.git
   cd ChebyshevCircles
   lake exe cache get  # Download cached Mathlib builds (optional but recommended)
   lake build
   ```

3. **Verify the proof:**
   ```bash
   lake build ChebyshevCircles
   ```
   If successful, all 3,457 lines of proof are verified with no `sorry` statements.

### Manim Visualizations

1. **Install system dependencies:**
   ```bash
   # macOS
   brew install ffmpeg cairo pkg-config
   brew install --cask mactex-no-gui  # LaTeX required for mathematical typography

   # Linux (Ubuntu/Debian)
   sudo apt-get install ffmpeg libcairo2-dev pkg-config python3-dev
   sudo apt-get install texlive-latex-base texlive-fonts-recommended texlive-latex-extra

   # Windows
   # Install FFmpeg from https://ffmpeg.org/download.html
   # Install MiKTeX from https://miktex.org/ or TeX Live from https://www.tug.org/texlive/
   ```

   **Note:** FFmpeg and LaTeX are required by Manim for video rendering and mathematical typography. Without these system dependencies, Manim cannot generate videos.

2. **Create virtual environment and install Python dependencies:**
   ```bash
   python3 -m venv .venv
   source .venv/bin/activate  # On Windows: .venv\Scripts\activate
   pip install -r requirements.txt
   ```
   This installs Manim Community Edition v0.19.0+ along with NumPy and other dependencies.

3. **Verify installation:**
   ```bash
   manim --version  # Should show: Manim Community v0.19.0 (or later)
   ```

## Usage

**Read the paper:**
```bash
# View the PDF
open paper/chebyshev_circles.pdf

# Compile from source (requires LaTeX)
cd paper
make
```

**View the blueprint:**
```bash
# Quick start - automatically builds and serves
./view_blueprint.sh

# Then open your browser to http://localhost:8000
```

**Explore the Lean proofs:**
```bash
# Open in VS Code with Lean 4 extension
code ChebyshevCircles/MainTheorem.lean

# Check a specific module
lake build ChebyshevCircles.PowerSums

# View API documentation online
open https://e-vergo.github.io/ChebyshevCircles/docs/
```

**Examine proof states:**
The Lean 4 VS Code extension shows the proof state (goals and hypotheses) at any cursor position. Key theorems to explore:
- `MainTheorem.lean:446` - Main theorem statement ([API docs](https://e-vergo.github.io/ChebyshevCircles/docs/ChebyshevCircles/MainTheorem.html#rotated_roots_yield_chebyshev))
- `PowerSums.lean:287` - Power sum invariance ([API docs](https://e-vergo.github.io/ChebyshevCircles/docs/ChebyshevCircles/PowerSums.html#powerSumCos_invariant))
- `ChebyshevOrthogonality.lean:412` - Discrete orthogonality ([API docs](https://e-vergo.github.io/ChebyshevCircles/docs/ChebyshevCircles/ChebyshevOrthogonality.html#sum_exp_chebyshev_angles))
- `NewtonIdentities.lean:156` - Newton's identities application ([API docs](https://e-vergo.github.io/ChebyshevCircles/docs/ChebyshevCircles/NewtonIdentities.html#esymm_eq_of_psum_eq))

**Generate animations:**
```bash
# Render specific N value
manim chebyshev_manim.py Chebyshev_N5

# Render at different quality levels
manim -ql chebyshev_manim.py Chebyshev_N5  # Low quality preview (faster)
manim -qh chebyshev_manim.py Chebyshev_N5  # High quality (default)
```
Videos are saved to `media/videos/chebyshev_manim/Chebyshev_N{N}/Chebyshev_N{N}.mp4`

After rendering, copy the final video to `chebyshev_videos/`:
```bash
cp media/videos/chebyshev_manim/Chebyshev_N{N}/Chebyshev_N{N}.mp4 chebyshev_videos/chebyshev_N{N}.mp4
```

See [`chebyshev_videos/MANIFEST.md`](chebyshev_videos/MANIFEST.md) for available videos and specifications.

**Extract still frames:**
```bash
# Extract frames from rendered videos at specified angles
python extract_frames_from_videos.py
```
Frames are saved to `paper_figures/` as both PNG and PDF formats (portrait 1080×1920).
Edit the script to customize N values and rotation angles (φ in radians).

**Customize visualizations:**
Edit `chebyshev_manim.py` to change:
- `N_VALUES` (near top of file): Which roots of unity to animate
- Color scheme: Customize colors for all graphical elements
- Frame rate/resolution: Edit `manim.cfg`
- Animation duration: Modify oscillation normalization in scene classes

## Contributing

This project has completed its primary goals: formal verification in Lean 4 and a publication-ready research paper. Potential extensions:
- Generalize to Chebyshev polynomials of the second kind (U_N)
- Prove analogous results for other orthogonal polynomial families
- Optimize proof tactics for better maintainability
- Add interactive web visualizations
- Extend the paper with additional results or applications

Pull requests welcome. Please ensure:
- All proofs compile with `lake build`
- No `sorry` statements introduced
- Code follows Mathlib style conventions
- Paper changes maintain mathematical accuracy

## Citation

If you use this work in your research, please cite:

**For the mathematical result:**
```bibtex
@misc{vergo2025chebyshev,
  author = {Eric Vergo},
  title = {Rotated Roots of Unity and Chebyshev Polynomials: A Geometric Construction},
  year = {2025},
  note = {Available at \url{https://github.com/e-vergo/ChebyshevCircles/paper/chebyshev_circles.pdf}}
}
```

**For the formal verification:**
```bibtex
@misc{chebyshev-circles-lean,
  author = {Eric Vergo},
  title = {Chebyshev Circles: Formal Verification of Rotated Roots of Unity},
  year = {2025},
  publisher = {GitHub},
  url = {https://github.com/e-vergo/ChebyshevCircles},
  note = {Lean 4 formalization}
}
```

## License

This project is licensed under the Apache License 2.0 - see the [LICENSE](LICENSE) file for details.

Copyright (c) 2025 Eric. All rights reserved.

## Acknowledgments

- Built with [Lean 4](https://leanprover.github.io/) and [Mathlib](https://leanprover-community.github.io/)
- Visualizations created with [Manim Community Edition](https://www.manim.community/)
- CI infrastructure via [lean-action](https://github.com/leanprover/lean-action)

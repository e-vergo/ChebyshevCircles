# Chebyshev Circles Paper

This directory contains a traditional mathematics paper presenting the main theorem from the Chebyshev Circles project.

## Files

- `chebyshev_circles.tex` - Main LaTeX document (~20 pages)
- `references.bib` - BibTeX bibliography with 15 references
- `figures/` - Directory containing extracted PNG figures from visualizations
- `Makefile` - Compilation automation

## Requirements

To compile this paper, you need a LaTeX distribution installed:

### macOS
```bash
brew install --cask mactex
# or install BasicTeX for a smaller distribution:
brew install --cask basictex
```

### Linux (Ubuntu/Debian)
```bash
sudo apt-get install texlive-full
# or for a minimal installation:
sudo apt-get install texlive-latex-base texlive-latex-extra texlive-fonts-recommended
```

### Windows
Download and install [MiKTeX](https://miktex.org/) or [TeX Live](https://www.tug.org/texlive/)

## Required LaTeX Packages

The document uses the following packages (included in most full LaTeX distributions):
- amsmath, amsthm, amssymb, amsfonts
- mathtools
- graphicx
- geometry
- hyperref
- cleveref
- enumitem
- tikz
- subcaption

## Compilation

### Using Make (recommended)
```bash
cd paper
make           # Full compilation with bibliography
make quick     # Quick compilation without bibliography update
make clean     # Remove auxiliary files
make view      # Open PDF (macOS only)
```

### Manual Compilation
```bash
cd paper
pdflatex chebyshev_circles
bibtex chebyshev_circles
pdflatex chebyshev_circles
pdflatex chebyshev_circles
```

The multiple `pdflatex` runs are necessary to resolve cross-references and include the bibliography.

## Output

Successfully compiling will produce `chebyshev_circles.pdf`, an approximately 20-page research paper suitable for arXiv submission or journal review.

## Paper Structure

1. **Introduction** - Main theorem statement and geometric intuition
2. **Preliminaries** - Chebyshev polynomials, roots of unity, Newton's identities
3. **Discrete Orthogonality Relations** - Foundation for power sum calculations
4. **Power Sum Invariance** - Key technical result via binomial expansion
5. **From Power Sums to Coefficients** - Applying Newton's identities
6. **Proof of Main Theorem** - Assembly of all components
7. **Examples and Illustrations** - Explicit cases with figures
8. **Discussion and Extensions** - Connections and future work
9. **Conclusion** - Summary and significance

## Figures

The paper includes 6 PNG figures extracted from the Python animations:
- `chebyshev_N3_angle0.png` through `chebyshev_N6_angle0.png` - Different polynomial degrees
- `chebyshev_N5_angle60.png` - Showing rotation dependence
- `chebyshev_N12_angle0.png` - Higher degree example

## Citation

If you use or reference this paper, please cite the repository:

```bibtex
@misc{chebyshev-circles-2025,
  author = {Eric Vergo},
  title = {Rotated Roots of Unity and Chebyshev Polynomials: A Geometric Construction},
  year = {2025},
  publisher = {GitHub},
  url = {https://github.com/e-vergo/ChebyshevCircles}
}
```

## Notes

- This is a pure mathematics paper written in traditional style
- No mention of the Lean formalization appears in the paper itself
- The paper targets a general mathematical audience (graduate level)
- All proofs are presented in classical mathematical notation

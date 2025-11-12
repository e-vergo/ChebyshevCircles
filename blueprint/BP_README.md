# Chebyshev Circles Blueprint

This directory contains the formalization blueprint for the Chebyshev Circles project. A blueprint is an interactive documentation system that shows the dependency structure of the Lean formalization and tracks which theorems have been proven.

## What is a Blueprint?

A blueprint provides:
- **Dependency graph**: Visual representation of how lemmas and theorems depend on each other
- **Formalization status**: Track which mathematical statements have been formalized in Lean
- **Interactive navigation**: Click through the mathematical development to see both the paper version and the Lean code
- **Cross-references**: Links between the mathematical exposition and the formal proofs

## Structure

```
blueprint/
├── src/                    # Source files
│   ├── content.tex        # Main mathematical content
│   ├── web.tex           # Web version configuration
│   ├── print.tex         # PDF version configuration
│   └── macros/           # LaTeX macro definitions
│       ├── common.tex    # Shared macros
│       ├── web.tex       # Web-specific macros
│       └── print.tex     # Print-specific macros
├── plastex.cfg           # PlasTeX configuration
├── tasks.py              # Build automation script
└── README.md             # This file
```

## Prerequisites

To build the blueprint, you need:

1. **Python 3.7+** with the following packages:
   ```bash
   pip install leanblueprint
   ```

2. **System dependencies**:
   - `graphviz` and `libgraphviz-dev` (for dependency graphs)
   - `texlive-full` or a complete LaTeX distribution (for PDF generation)

3. **Lean 4**: The project must be built first so that declarations can be checked

## Building the Blueprint

### Web Version (HTML)

Build the interactive web version:

```bash
cd blueprint
leanblueprint web
```

The output will be in `src/web/`. To view it:

```bash
cd src/web
python3 -m http.server 8000
```

Then open http://localhost:8000 in your browser.

### PDF Version

Build the printable PDF version:

```bash
cd blueprint
leanblueprint pdf
```

The PDF will be generated in `src/print/`.

### Build Everything

Build both web and PDF versions and check that all Lean declarations exist:

```bash
cd blueprint
leanblueprint all
```

### Check Declarations

Verify that all `\lean{...}` references in the blueprint correspond to actual declarations in the Lean code:

```bash
cd blueprint
leanblueprint checkdecls
```

## Using invoke (Optional)

If you have `invoke` installed, you can use the tasks defined in `tasks.py`:

```bash
pip install invoke

# Build web version
invoke web

# Build PDF version
invoke pdf

# Build everything
invoke all

# Serve the blueprint locally
invoke serve

# Check declarations
invoke checkdecls
```

## Updating the Blueprint

### Adding New Content

Edit `src/content.tex` to add new mathematical content. The file is organized by chapters corresponding to the main proof steps.

### Marking Lean Declarations

To link a theorem or lemma to its Lean formalization, use the `\lean{...}` command:

```latex
\begin{theorem}\label{thm:main}
\lean{rotated_roots_yield_chebyshev}
\leanok
...
\end{theorem}
```

- `\lean{name}`: Links to the Lean declaration `name`
- `\leanok`: Indicates this statement has been fully formalized (green checkmark)
- `\uses{lem1, lem2}`: Declares dependencies on other results

### Adding Macros

- Edit `src/macros/common.tex` for macros used in both web and print versions
- Edit `src/macros/web.tex` for web-specific macros
- Edit `src/macros/print.tex` for print-specific macros

## Lean Declaration Mapping

The blueprint references the following key Lean declarations:

| Blueprint Label | Lean Declaration | File |
|----------------|------------------|------|
| `thm:main` | `rotated_roots_yield_chebyshev` | MainTheorem.lean |
| `lem:discrete_orthogonality` | `geom_sum_eq` | ChebyshevOrthogonality.lean |
| `thm:newton_identities` | `newton_power_sum_eq_esymm` | NewtonIdentities.lean |
| `lem:power_sum_invariance` | `powerSum_rotated_roots_indep_phi` | PowerSums.lean |
| `prop:chebyshev_properties` | `Polynomial.Chebyshev.T` | Mathlib |

## Deployment

The blueprint is automatically built and deployed to GitHub Pages via GitHub Actions. The workflow is defined in `.github/workflows/blueprint.yml`.

When you push to the `main` branch:
1. The Lean code is built
2. The blueprint web version is generated
3. The blueprint PDF is compiled
4. Everything is deployed to https://e-vergo.github.io/ChebyshevCircles/blueprint/

## Troubleshooting

### PlasTeX warnings about missing packages

If you see warnings like "WARNING: Could not find any file named: blueprint.sty", this is normal. The blueprint package is loaded as a Python plugin, not a LaTeX package.

### Missing theorem environments

Make sure you have the theorem environments defined in your TeX files. The `amsthm` package should provide most of them.

### Declaration check failures

If `leanblueprint checkdecls` fails:
1. Make sure you've built the Lean project first: `lake build`
2. Verify the declaration names match exactly (case-sensitive)
3. Check that the Lean file path is correct relative to the project root

### PDF generation issues

If PDF generation fails:
1. Ensure you have a complete LaTeX distribution installed
2. Check that `pdflatex` or `lualatex` is in your PATH
3. Look at the LaTeX error messages in the build output

## Resources

- **Leanblueprint Documentation**: https://github.com/PatrickMassot/leanblueprint
- **Example Projects**:
  - Sphere Eversion: https://leanprover-community.github.io/sphere-eversion/
  - Liquid Tensor Experiment: https://leanprover-community.github.io/liquid/
- **Terence Tao's Blog Post**: https://terrytao.wordpress.com/2023/11/18/formalizing-the-proof-of-pfr-in-lean4-using-blueprint-a-short-tour/

## License

This blueprint is part of the Chebyshev Circles project and is licensed under the Apache License 2.0.

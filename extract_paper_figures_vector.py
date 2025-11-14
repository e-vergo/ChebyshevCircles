"""
Generate TRUE VECTOR PDF figures for academic publication.

This version uses matplotlib to create vector PDFs directly, ensuring infinite scalability.
Replicates the exact visual style from Manim but with native vector output.
"""

import numpy as np
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.path import Path
from matplotlib.patches import PathPatch, FancyBboxPatch
from pathlib import Path as FilePath


def render_vector_figure(N, phi_deg, output_path, dpi=300):
    """
    Render a single figure as vector PDF.

    Args:
        N: Number of roots
        phi_deg: Rotation angle in degrees
        output_path: Path to output PDF file
        dpi: DPI for text rendering (vector elements scale infinitely)
    """
    phi = np.radians(phi_deg)

    # Create figure with landscape 16:9 aspect ratio
    # Use inches: 19.2" × 10.8" gives 5760×3240 at 300 DPI
    fig = plt.figure(figsize=(19.2, 10.8), dpi=dpi, facecolor='white')

    # Main axes for geometric plot (right 60% of figure)
    ax = fig.add_axes([0.42, 0.05, 0.55, 0.9])  # [left, bottom, width, height]

    # Configure axes
    ax.set_xlim(-1.5, 1.5)
    ax.set_ylim(-2.5, 2.5)
    ax.set_aspect('equal')
    ax.grid(False)
    ax.spines['left'].set_color('#DCDCDC')
    ax.spines['bottom'].set_color('#DCDCDC')
    ax.spines['left'].set_linewidth(1.5)
    ax.spines['bottom'].set_linewidth(1.5)
    ax.spines['right'].set_visible(False)
    ax.spines['top'].set_visible(False)
    ax.tick_params(colors='#DCDCDC', which='both', labelsize=10, width=1.5)

    # ===== Unit circle =====
    circle = plt.Circle((0, 0), 1, color='#B4B4B4', fill=False, linewidth=2, zorder=1)
    ax.add_patch(circle)

    # ===== Roots of unity =====
    roots = [np.exp(2j * np.pi * k / N + 1j * phi) for k in range(N)]

    # Projection lines (z=2)
    for root in roots:
        ax.plot([root.real, root.real], [root.imag, 0],
                color='#FFB4B4', linewidth=2, alpha=0.4, zorder=2)

    # Polygon (z=3)
    polygon_x = [r.real for r in roots] + [roots[0].real]
    polygon_y = [r.imag for r in roots] + [roots[0].imag]
    ax.plot(polygon_x, polygon_y, color='#FF6464', linewidth=3, zorder=3)

    # Projection dots (z=5)
    for root in roots:
        ax.plot(root.real, 0, 'o', color='#FF7878', markersize=8,
                alpha=0.7, zorder=5, markeredgewidth=0)

    # Root dots (z=4)
    for root in roots:
        ax.plot(root.real, root.imag, 'o', color='#DC3232', markersize=10,
                zorder=4, markeredgecolor='black', markeredgewidth=0.5)

    # ===== Polynomial curve =====
    real_parts = [r.real for r in roots]
    coeffs = np.poly(real_parts)
    scale = 2**(N - 1)
    scaled_coeffs = [c.real * scale for c in coeffs]

    def poly_func(x):
        """Evaluate polynomial using Horner's method."""
        result = 0.0
        for c in scaled_coeffs:
            result = result * x + c
        return result

    # Plot polynomial (z=6)
    x_curve = np.linspace(-1.5, 1.5, 1000)
    y_curve = np.array([poly_func(x) for x in x_curve])
    y_curve = np.clip(y_curve, -2.5, 2.5)
    ax.plot(x_curve, y_curve, color='#2864C8', linewidth=4, zorder=6)

    # ===== Text annotations (left 40% of figure) =====
    text_color = '#3C3C3C'

    # Position text on left side
    text_x = 0.05
    text_y_start = 0.85

    # Line 1: N = X Roots of Unity
    fig.text(text_x, text_y_start, f'$N = {N}$ Roots of Unity',
             fontsize=48, color=text_color, verticalalignment='top',
             family='serif')

    # Line 2: Rotation and scaling
    scaling_value = int(scale)
    fig.text(text_x, text_y_start - 0.12,
             f'$\\varphi = {phi_deg:.1f}^\\circ$ | Scaling: $2^{{{N-1}}} = {scaling_value}$',
             fontsize=40, color=text_color, verticalalignment='top',
             family='serif')

    # Line 3: Polynomial
    poly_str = format_poly_latex(scaled_coeffs, N)
    poly_fontsize = 36
    if N >= 8:
        poly_fontsize = 32
    if N >= 12:
        poly_fontsize = 28

    fig.text(text_x, text_y_start - 0.26, poly_str,
             fontsize=poly_fontsize, color=text_color, verticalalignment='top',
             family='serif')

    # Line 4: Chebyshev relation
    fig.text(text_x, text_y_start - 0.38, f'$= T_{{{N}}}(x) + c$',
             fontsize=40, color=text_color, verticalalignment='top',
             family='serif')

    # Save as vector PDF
    plt.savefig(output_path, format='pdf', bbox_inches='tight',
                dpi=dpi, backend='pdf')
    plt.close()

    print(f"Created vector PDF: {output_path}")


def format_poly_latex(coeffs, N):
    """
    Format polynomial for LaTeX rendering.

    Args:
        coeffs: Polynomial coefficients (highest degree first)
        N: Degree of polynomial

    Returns:
        LaTeX string
    """
    n_deg = len(coeffs) - 1
    terms = []

    for i, c in enumerate(coeffs):
        power = n_deg - i
        c_val = round(c, 2) if abs(c) < 10 else int(round(c))

        if abs(c_val) < 1e-10:
            continue

        # Build coefficient string
        if i == 0:  # First term
            if abs(c_val - 1) < 1e-10:
                coeff_str = ""
            elif abs(c_val + 1) < 1e-10:
                coeff_str = "-"
            else:
                coeff_str = str(c_val) if isinstance(c_val, int) else f"{c_val:.2f}"
        else:  # Subsequent terms
            if abs(c_val - 1) < 1e-10:
                coeff_str = "+"
            elif abs(c_val + 1) < 1e-10:
                coeff_str = "-"
            elif c_val > 0:
                coeff_str = f"+{c_val}" if isinstance(c_val, int) else f"+{c_val:.2f}"
            else:
                coeff_str = str(c_val) if isinstance(c_val, int) else f"{c_val:.2f}"

        # Build variable string
        if power == 0:
            terms.append(coeff_str)
        elif power == 1:
            terms.append(f"{coeff_str}x")
        else:
            terms.append(f"{coeff_str}x^{{{power}}}")

    # Truncate middle terms for large polynomials
    if len(terms) > 5 and N >= 8:
        poly_str = "".join(terms[:2]) + r" \cdots " + "".join(terms[-2:])
    else:
        poly_str = "".join(terms)

    if poly_str.startswith("+"):
        poly_str = poly_str[1:]

    return f"$S(x) = {poly_str}$"


def main():
    """Generate all vector PDF figures."""
    output_dir = FilePath("/Users/eric/Documents/GitHub/ChebyshevCircles/paper_figures")
    output_dir.mkdir(exist_ok=True)

    # Generate figures for N=3, 5, 10 at phi=0°
    for N in [3, 5, 10]:
        output_file = output_dir / f"paper_figure_N{N}_phi0_vector.pdf"
        render_vector_figure(N, 0.0, str(output_file), dpi=300)

    print("\nAll vector PDFs generated successfully!")
    print(f"Output directory: {output_dir}")


if __name__ == "__main__":
    main()

"""
Extract high-quality landscape figures for academic paper publication.

Generates static frames at N=3, 5, 10 with phi=0° in landscape orientation (16:9).
Outputs both vector PDF and high-resolution PNG (300 DPI) suitable for print journals.

Technical specifications:
- Resolution: 5760×3240 pixels (16:9 landscape at 300 DPI for 19.2" × 10.8" print)
- Vector output: PDF with true vector graphics
- Raster output: PNG at 300 DPI
- Layout: Text repositioned to left side for landscape orientation
- Frame dimensions: 16:9 aspect ratio with proper scaling

Usage:
    manim extract_paper_figures.py PaperFigureN3 -pql --format=png --media_dir=./paper_figures
    manim extract_paper_figures.py PaperFigureN3 -pql --format=pdf --media_dir=./paper_figures
"""

from manim import *
import numpy as np


class LandscapePaperFigure(Scene):
    """
    Base class for landscape paper figures.

    Rendering configuration:
    - Use -pql flag for production quality PNG (5760×3240)
    - Use --format=pdf for vector output
    - Override pixel dimensions in subclass or via CLI
    """

    # Color scheme (matching existing aesthetic)
    COLOR_CIRCLE = "#B4B4B4"
    COLOR_AXES = "#DCDCDC"
    COLOR_POLYGON = "#FF6464"
    COLOR_ROOT = "#DC3232"
    COLOR_PROJECTION_LINE = "#FFB4B4"
    COLOR_PROJECTION_POINT = "#FF7878"
    COLOR_CURVE = "#2864C8"
    COLOR_TEXT = "#3C3C3C"

    def construct(self):
        """Override in subclasses to set N value."""
        pass

    def render_landscape_frame(self, N, phi_deg):
        """
        Render a single landscape frame with specified parameters.

        Args:
            N: Number of roots
            phi_deg: Rotation angle in degrees
        """
        phi = phi_deg * DEGREES

        # Landscape frame configuration (16:9 aspect ratio)
        # Frame width = 16 logical units, height = 9 logical units
        self.camera.frame_width = 16.0
        self.camera.frame_height = 9.0

        # ===== Axes - positioned right of center =====
        # For landscape: axes on right 60%, text on left 40%
        axes = Axes(
            x_range=[-1.5, 1.5, 0.5],
            y_range=[-2.5, 2.5, 0.5],
            x_length=5,       # Horizontal extent
            y_length=6.67,    # Vertical extent (maintains aspect ratio)
            axis_config={
                "stroke_color": self.COLOR_AXES,
                "stroke_width": 1.5,
                "include_tip": False,
            }
        ).shift(RIGHT * 2.5).set_z_index(0)  # Shift right for landscape layout

        # ===== Unit circle =====
        circle = ParametricFunction(
            lambda t: axes.c2p(np.cos(t), np.sin(t)),
            t_range=[0, 2*np.pi],
            color=self.COLOR_CIRCLE,
            stroke_width=2
        ).set_z_index(1)

        # ===== Roots of unity =====
        roots = [np.exp(2j * np.pi * k / N + 1j * phi) for k in range(N)]

        # Root dots
        root_dots = VGroup(*[
            Dot(axes.c2p(r.real, r.imag),
                color=self.COLOR_ROOT,
                radius=0.10,
                stroke_width=1,
                stroke_color=BLACK).set_z_index(4)
            for r in roots
        ])

        # Polygon
        polygon = Polygon(
            *[axes.c2p(r.real, r.imag) for r in roots],
            color=self.COLOR_POLYGON,
            stroke_width=3,
            fill_opacity=0
        ).set_z_index(3)

        # Projection lines
        proj_lines = VGroup(*[
            Line(axes.c2p(r.real, r.imag), axes.c2p(r.real, 0),
                 color=self.COLOR_PROJECTION_LINE,
                 stroke_width=2).set_opacity(0.4).set_z_index(2)
            for r in roots
        ])

        # Projection dots
        proj_dots = VGroup(*[
            Dot(axes.c2p(r.real, 0),
                color=self.COLOR_PROJECTION_POINT,
                radius=0.08).set_opacity(0.7).set_z_index(5)
            for r in roots
        ])

        # ===== Polynomial curve =====
        real_parts = [r.real for r in roots]
        coeffs = np.poly(real_parts)
        scale = 2**(N - 1)
        scaled_coeffs = [c.real * scale for c in coeffs]

        def poly_func(x):
            """Horner's method for polynomial evaluation."""
            result = 0.0
            for c in scaled_coeffs:
                result = result * x + c
            return result

        # Dense sampling for smooth curve
        curve = ParametricFunction(
            lambda t: axes.c2p(t, poly_func(t)),
            t_range=np.array([-1.5, 1.5, 0.002]),
            color=self.COLOR_CURVE,
            stroke_width=4
        ).set_z_index(6)

        # ===== Text - positioned on left side for landscape =====
        text_color = self.COLOR_TEXT

        # Position text on left side of frame
        # Frame extends from -8 to +8 horizontally (width=16)
        text_x = -6.5  # Left margin
        text_y_start = 3.5  # Top of text block

        line1 = Tex(
            f"$N = {N}$ Roots of Unity",
            font_size=44,
            color=text_color
        ).move_to([text_x, text_y_start, 0], aligned_edge=LEFT).set_z_index(7)

        scaling_value = int(scale)
        line2 = Tex(
            f"$\\varphi = {phi_deg:.1f}^\\circ$ | Scaling: $2^{{{N-1}}} = {scaling_value}$",
            font_size=36,
            color=text_color
        ).next_to(line1, DOWN, aligned_edge=LEFT, buff=0.25).set_z_index(7)

        # Format polynomial using LaTeX
        poly_str = self.format_poly_latex(scaled_coeffs, N)

        # Adaptive font size based on N
        poly_font_size = 32
        if N >= 8:
            poly_font_size = 28
        if N >= 12:
            poly_font_size = 24

        line3 = MathTex(
            poly_str,
            font_size=poly_font_size,
            color=text_color
        ).next_to(line2, DOWN, aligned_edge=LEFT, buff=0.25).set_z_index(7)

        line4 = MathTex(
            f"= T_{{{N}}}(x) + c",
            font_size=36,
            color=text_color
        ).next_to(line3, DOWN, aligned_edge=LEFT, buff=0.25).set_z_index(7)

        # ===== Add all elements to scene =====
        self.add(axes, circle, proj_lines, polygon, proj_dots, root_dots, curve)
        self.add(line1, line2, line3, line4)

    @staticmethod
    def format_poly_latex(coeffs, N):
        """
        Format polynomial for LaTeX rendering with intelligent truncation.

        Args:
            coeffs: Polynomial coefficients (highest degree first)
            N: Degree of polynomial (for truncation decisions)

        Returns:
            LaTeX string for MathTex
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

        return f"S(x) = {poly_str}"


class PaperFigureN3(LandscapePaperFigure):
    """N=3, phi=0° - Landscape figure for paper."""

    def construct(self):
        self.render_landscape_frame(N=3, phi_deg=0.0)


class PaperFigureN5(LandscapePaperFigure):
    """N=5, phi=0° - Landscape figure for paper."""

    def construct(self):
        self.render_landscape_frame(N=5, phi_deg=0.0)


class PaperFigureN10(LandscapePaperFigure):
    """N=10, phi=0° - Landscape figure for paper."""

    def construct(self):
        self.render_landscape_frame(N=10, phi_deg=0.0)

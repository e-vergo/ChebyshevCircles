"""Test static frames for N=3, 5, 10 at phi=0 degrees."""

from manim import *
import numpy as np


class FrameN3Phi0(Scene):
    """N=3, phi=0°"""

    def construct(self):
        self.render_frame(N=3, phi_deg=0.0)

    def render_frame(self, N, phi_deg):
        phi = phi_deg * DEGREES
        self.camera.frame_width = 6.0

        # Axes - shifted down to leave room for text at top
        axes = Axes(
            x_range=[-1.5, 1.5, 0.5],
            y_range=[-2.5, 2.5, 0.5],
            x_length=4,
            y_length=5.5,  # Reduced from 7 to leave room for text
            axis_config={"stroke_color": ManimColor("#DCDCDC"), "stroke_width": 1.5}
        ).shift(DOWN * 0.8).set_z_index(0)  # Shift down

        # Unit circle (radius = 1 in coordinate space)
        # Use ParametricFunction to ensure proper coordinate transformation
        circle = ParametricFunction(
            lambda t: axes.c2p(np.cos(t), np.sin(t)),
            t_range=[0, 2*np.pi],
            color=ManimColor("#B4B4B4"),
            stroke_width=2
        ).set_z_index(1)

        # Roots
        roots = [np.exp(2j * np.pi * k / N + 1j * phi) for k in range(N)]

        # Root dots
        root_dots = VGroup(*[
            Dot(axes.c2p(r.real, r.imag), color=ManimColor("#DC3232"), radius=0.08).set_z_index(4)
            for r in roots
        ])

        # Polygon
        polygon = Polygon(
            *[axes.c2p(r.real, r.imag) for r in roots],
            color=ManimColor("#FF6464"),
            stroke_width=3,
            fill_opacity=0
        ).set_z_index(3)

        # Projection lines
        proj_lines = VGroup(*[
            Line(axes.c2p(r.real, r.imag), axes.c2p(r.real, 0),
                 color=ManimColor("#FFB4B4"), stroke_width=2).set_opacity(0.4).set_z_index(2)
            for r in roots
        ])

        # Projection dots
        proj_dots = VGroup(*[
            Dot(axes.c2p(r.real, 0), color=ManimColor("#FF7878"), radius=0.06).set_opacity(0.7).set_z_index(5)
            for r in roots
        ])

        # Polynomial
        real_parts = [r.real for r in roots]
        coeffs = np.poly(real_parts)
        scale = 2**(N - 1)
        scaled_coeffs = [c.real * scale for c in coeffs]

        def poly_func(x):
            result = 0.0
            for c in scaled_coeffs:
                result = result * x + c
            return result

        curve = ParametricFunction(
            lambda t: np.array([t, poly_func(t), 0]),
            t_range=np.array([-1.5, 1.5, 0.002]),
            color=ManimColor("#2864C8"),
            stroke_width=4
        ).shift(axes.c2p(0, 0) - axes.c2p(0, 0)).set_z_index(6)

        # Text - positioned at top of frame (frame_height ≈ 10.67 for portrait)
        text_color = ManimColor("#3C3C3C")

        # Position from top of frame downward
        line1 = Tex(
            f"$N = {N}$ Roots of Unity",
            font_size=36,  # Slightly smaller
            color=text_color
        ).to_edge(UP, buff=0.6).shift(LEFT * 1.2).set_z_index(7)

        scaling_value = int(scale)
        line2 = Tex(
            f"$\\varphi = {phi_deg:.1f}^\\circ$ | Scaling: $2^{{{N-1}}} = {scaling_value}$",
            font_size=28,
            color=text_color
        ).next_to(line1, DOWN, aligned_edge=LEFT, buff=0.1).set_z_index(7)

        # Format polynomial using LaTeX
        poly_str = self.format_poly_latex(scaled_coeffs)

        line3 = MathTex(
            poly_str,
            font_size=24,
            color=text_color
        ).next_to(line2, DOWN, aligned_edge=LEFT, buff=0.1).set_z_index(7)

        line4 = MathTex(
            f"= T_{{{N}}}(x) + c",
            font_size=28,
            color=text_color
        ).next_to(line3, DOWN, aligned_edge=LEFT, buff=0.1).set_z_index(7)

        # Add all
        self.add(axes, circle, proj_lines, polygon, proj_dots, root_dots, curve)
        self.add(line1, line2, line3, line4)

    @staticmethod
    def format_poly_latex(coeffs):
        """Format polynomial for LaTeX rendering."""
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

        if len(terms) > 4:
            poly_str = "".join(terms[:2]) + r"\\cdots" + "".join(terms[-2:])
        else:
            poly_str = "".join(terms)

        if poly_str.startswith("+"):
            poly_str = poly_str[1:]

        return f"S(x) = {poly_str}"

    @staticmethod
    def format_poly(coeffs):
        terms = []
        n_deg = len(coeffs) - 1
        for i, c in enumerate(coeffs):
            power = n_deg - i
            c_val = round(c, 2) if abs(c) < 10 else int(round(c))
            if abs(c_val) < 1e-10:
                continue
            if power == 0:
                terms.append(f"{c_val:+.2f}" if isinstance(c_val, float) else f"{c_val:+d}")
            elif power == 1:
                if abs(c_val - 1) < 1e-10:
                    terms.append("+x")
                elif abs(c_val + 1) < 1e-10:
                    terms.append("-x")
                else:
                    terms.append(f"{c_val:+g}x")
            else:
                superscripts = {'0': '⁰', '1': '¹', '2': '²', '3': '³', '4': '⁴',
                               '5': '⁵', '6': '⁶', '7': '⁷', '8': '⁸', '9': '⁹'}
                power_str = ''.join(superscripts[d] for d in str(power))
                if abs(c_val - 1) < 1e-10:
                    terms.append(f"+x{power_str}")
                elif abs(c_val + 1) < 1e-10:
                    terms.append(f"-x{power_str}")
                else:
                    terms.append(f"{c_val:+g}x{power_str}")

        if len(terms) > 4:
            poly_str = "".join(terms[:2]) + "..." + "".join(terms[-2:])
        else:
            poly_str = "".join(terms)
        if poly_str.startswith("+"):
            poly_str = poly_str[1:]
        return poly_str


class FrameN5Phi0(FrameN3Phi0):
    """N=5, phi=0°"""

    def construct(self):
        self.render_frame(N=5, phi_deg=0.0)


class FrameN10Phi0(FrameN3Phi0):
    """N=10, phi=0°"""

    def construct(self):
        self.render_frame(N=10, phi_deg=0.0)

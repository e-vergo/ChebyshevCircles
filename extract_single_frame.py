"""
Create a static frame scene for specific N and phi values.
Use with: manim -s -qh extract_single_frame.py FrameN3_Phi0
"""

from manim import *
import numpy as np
import sys

# Get N and phi from command line or use defaults
if len(sys.argv) > 2:
    TARGET_N = int(sys.argv[1])
    TARGET_PHI_DEG = float(sys.argv[2])
else:
    TARGET_N = 3
    TARGET_PHI_DEG = 0.0


class StaticFrame(Scene):
    """Single static frame at specific N and phi."""

    def construct(self):
        N = TARGET_N
        phi = TARGET_PHI_DEG * DEGREES

        # Configure frame (portrait)
        self.camera.frame_width = 6.0

        # Axes
        axes = Axes(
            x_range=[-1.5, 1.5, 0.5],
            y_range=[-2.5, 2.5, 0.5],
            x_length=4,
            y_length=7,
            axis_config={"stroke_color": ManimColor("#DCDCDC"), "stroke_width": 1.5}
        ).set_z_index(0)

        # Unit circle
        circle = Circle(
            radius=1.0,
            color=ManimColor("#B4B4B4"),
            stroke_width=2
        ).move_to(axes.c2p(0, 0)).set_z_index(1)

        # Generate rotated roots
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

        # Text
        text_color = ManimColor("#3C3C3C")

        line1 = Text(
            f"N = {N} Roots of Unity",
            font_size=40,
            color=text_color
        ).to_corner(UL, buff=0.4).set_z_index(7)

        phi_deg = phi / DEGREES
        scaling_value = int(scale)
        line2 = Text(
            f"φ = {phi_deg:.1f}° | Scaling: 2^{N-1} = {scaling_value}",
            font_size=32,
            color=text_color
        ).next_to(line1, DOWN, aligned_edge=LEFT, buff=0.2).set_z_index(7)

        # Format polynomial
        terms = []
        n_deg = len(scaled_coeffs) - 1
        for i, c in enumerate(scaled_coeffs):
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

        line3 = Text(
            f"S(x) = {poly_str}",
            font_size=28,
            color=text_color
        ).next_to(line2, DOWN, aligned_edge=LEFT, buff=0.2).set_z_index(7)

        line4 = Text(
            f"= T_{N}(x) + c",
            font_size=32,
            color=text_color
        ).next_to(line3, DOWN, aligned_edge=LEFT, buff=0.2).set_z_index(7)

        # Add all
        self.add(axes, circle, proj_lines, polygon, proj_dots, root_dots, curve)
        self.add(line1, line2, line3, line4)

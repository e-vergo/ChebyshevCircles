"""
Chebyshev Circles Manim Visualization

Renders professional animated videos demonstrating the geometric construction of Chebyshev
polynomials via rotated roots of unity projected onto the real axis.

Key Features:
- Dense polynomial sampling to eliminate artifacts at high N values
- Oscillation normalization: All videos show ~1 polynomial oscillation cycle
- Portrait format (1080x1920 @ 60fps) optimized for mobile viewing
- Professional typography using MathTex for all mathematical expressions
- Minimalist color scheme matching existing GIF aesthetic

Technical Implementation:
- Uses ParametricFunction for smooth polynomial curves (tested superior to FunctionGraph)
- ValueTracker-based rotation for smooth circular motion
- always_redraw() updaters for dynamic geometric elements
- Proper z-index layering for visual clarity

Author: Generated for ChebyshevCircles project
Date: 2025-11-13
"""

import numpy as np
from manim import *

# ============================================================================
# Core Mathematical Functions (adapted from main.py)
# ============================================================================

def roots_of_unity(N):
    """
    Generate N equally-spaced points on the unit circle.

    Args:
        N: Number of roots

    Returns:
        List of complex numbers representing N-th roots of unity
    """
    if N <= 0:
        raise ValueError("N must be a positive integer.")

    roots = []
    for k in range(N):
        angle = 2 * np.pi * k / N
        root = np.cos(angle) + 1j * np.sin(angle)
        roots.append(root)

    return roots


def rotate_complex_numbers(complex_list, angle):
    """
    Rotate a list of complex numbers by a given angle.

    Args:
        complex_list: List of complex numbers
        angle: Rotation angle in radians

    Returns:
        List of rotated complex numbers
    """
    rotated = []
    for z in complex_list:
        rotated_z = z * (np.cos(angle) + 1j * np.sin(angle))
        rotated.append(rotated_z)
    return rotated


def compute_polynomial_coeffs(rotated_roots):
    """
    Compute polynomial coefficients from roots and scale by 2^(N-1).

    Args:
        rotated_roots: List of complex roots

    Returns:
        Tuple of (scaled_coeffs, constant_term, scaling_factor)
        scaled_coeffs: list with highest degree first (excluding constant)
        constant_term: the constant term value
        scaling_factor: 2^(N-1) scaling applied
    """
    real_parts = [z.real for z in rotated_roots]
    poly_coeffs = np.poly(real_parts)  # Returns coefficients highest degree first

    N = len(rotated_roots)
    scaling_factor = 2 ** (N - 1)

    # Scale and extract real parts
    scaled_coeffs = [coeff.real * scaling_factor for coeff in poly_coeffs]

    return scaled_coeffs[:-1], scaled_coeffs[-1], scaling_factor


def eval_poly(coeffs, x):
    """
    Evaluate polynomial at x given coefficients (highest degree first).

    Args:
        coeffs: Polynomial coefficients, highest degree first
        x: Point at which to evaluate

    Returns:
        Polynomial value at x
    """
    result = 0
    for coeff in coeffs:
        result = result * x + coeff
    return result


def format_polynomial_text(coeffs, constant_term, max_width=50):
    """
    Format polynomial coefficients as plain text string with superscripts using Unicode.

    Args:
        coeffs: List with highest degree first (excluding constant term)
        constant_term: The constant term value
        max_width: Maximum character width before truncation (adaptive)

    Returns:
        Plain text string with Unicode superscripts
    """
    # Unicode superscript mapping
    superscripts = {'0': '⁰', '1': '¹', '2': '²', '3': '³', '4': '⁴',
                   '5': '⁵', '6': '⁶', '7': '⁷', '8': '⁸', '9': '⁹'}

    def to_superscript(n):
        return ''.join(superscripts[d] for d in str(n))

    n = len(coeffs)  # degree of polynomial
    terms = []

    for i, coeff in enumerate(coeffs):
        power = n - i
        rounded_coeff = int(round(coeff))

        if rounded_coeff == 0:
            continue

        # Format coefficient
        if power == n:  # Leading term
            if rounded_coeff == 1:
                coeff_str = ""
            elif rounded_coeff == -1:
                coeff_str = "-"
            else:
                coeff_str = str(rounded_coeff)
        else:
            if rounded_coeff == 1:
                coeff_str = "+"
            elif rounded_coeff == -1:
                coeff_str = "-"
            elif rounded_coeff > 0:
                coeff_str = f"+{rounded_coeff}"
            else:
                coeff_str = str(rounded_coeff)

        # Format variable part
        if power == 0:
            var_str = ""
        elif power == 1:
            var_str = "x"
        else:
            var_str = f"x{to_superscript(power)}"

        terms.append(f"{coeff_str}{var_str}")

    # Add constant term
    if constant_term >= 0:
        terms.append(f"+{constant_term:.2f}")
    else:
        terms.append(f"{constant_term:.2f}")

    polynomial_str = "".join(terms)

    # Clean up leading +
    if polynomial_str.startswith('+'):
        polynomial_str = polynomial_str[1:]

    # Truncate middle terms if too long (for N >= 15)
    if len(polynomial_str) > max_width and n > 8:
        # Keep first 2 terms, ellipsis, and last 2 terms
        first_terms = terms[:2]
        last_terms = terms[-2:]
        polynomial_str = "".join(first_terms) + " ... " + "".join(last_terms)

    return f"S(x) = {polynomial_str}"


def format_polynomial_latex(coeffs, constant_term, max_width=40):
    """
    Format polynomial coefficients as LaTeX string with intelligent truncation.

    Args:
        coeffs: List with highest degree first (excluding constant term)
        constant_term: The constant term value
        max_width: Maximum character width before truncation (adaptive)

    Returns:
        LaTeX string for MathTex
    """
    n = len(coeffs)  # degree of polynomial
    terms = []

    for i, coeff in enumerate(coeffs):
        power = n - i
        rounded_coeff = int(round(coeff))

        if rounded_coeff == 0:
            continue

        # Format coefficient
        if power == n:  # Leading term
            if rounded_coeff == 1:
                coeff_str = ""
            elif rounded_coeff == -1:
                coeff_str = "-"
            else:
                coeff_str = str(rounded_coeff)
        else:
            if rounded_coeff == 1:
                coeff_str = "+"
            elif rounded_coeff == -1:
                coeff_str = "-"
            elif rounded_coeff > 0:
                coeff_str = f"+{rounded_coeff}"
            else:
                coeff_str = str(rounded_coeff)

        # Format variable part
        if power == 0:
            var_str = ""
        elif power == 1:
            var_str = "x"
        else:
            var_str = f"x^{{{power}}}"

        terms.append(f"{coeff_str}{var_str}")

    # Add constant term
    if constant_term >= 0:
        terms.append(f"+{constant_term:.2f}")
    else:
        terms.append(f"{constant_term:.2f}")

    polynomial_str = "".join(terms)

    # Clean up leading +
    if polynomial_str.startswith('+'):
        polynomial_str = polynomial_str[1:]

    # Truncate middle terms if too long (for N >= 15)
    if len(polynomial_str) > max_width and n > 8:
        # Keep first 2 terms, ellipsis, and last 2 terms
        first_terms = terms[:2]
        last_terms = terms[-2:]
        polynomial_str = "".join(first_terms) + r" \cdots " + "".join(last_terms)

    return f"S(x) = {polynomial_str}"


def get_oscillation_duration(N, baseline_N=3, baseline_duration=10.0):
    """
    Calculate video duration for oscillation normalization.

    Strategy: Each video shows approximately 1 complete polynomial oscillation.
    Higher N values rotate slower to maintain similar visual tempo.

    Formula:
        duration(N) = baseline_duration × (N / baseline_N)

    Reasoning:
        - A full 2π rotation of roots creates N oscillations in the polynomial
        - To show 1 oscillation: rotate by 2π/N radians
        - Higher N requires slower rotation to match N=3's visual rhythm
        - Linear scaling preserves angular velocity ratio

    Args:
        N: Current number of roots
        baseline_N: Reference N value (default 3)
        baseline_duration: Duration for baseline_N in seconds (default 10.0)

    Returns:
        Duration in seconds for this N value
    """
    return baseline_duration * (N / baseline_N)


# ============================================================================
# Manim Scene Base Class
# ============================================================================

class ChebyshevBase(Scene):
    """
    Base scene for Chebyshev polynomial visualization.

    Subclasses must set self.N to the desired number of roots.

    Visual Elements:
    - Unit circle with rotated N-gon
    - Projection lines from roots to x-axis
    - Dynamically updated polynomial curve
    - Professional typography displaying equations

    Animation Flow:
    1. Show initial state at φ=0
    2. Rotate roots through 2π/N radians (1 polynomial oscillation)
    3. Continuously update all geometric elements
    """

    N = 3  # Default, override in subclasses

    # Color scheme (high contrast)
    COLOR_CIRCLE = "#909090"
    COLOR_AXES = "#C0C0C0"
    COLOR_POLYGON = "#FF4444"
    COLOR_ROOT = "#C81010"
    COLOR_PROJECTION_LINE = "#FF9090"
    COLOR_PROJECTION_POINT = "#FF5050"
    COLOR_CURVE = "#1850A0"
    COLOR_TEXT = "#000000"

    # Geometric parameters
    CIRCLE_STROKE_WIDTH = 3
    AXIS_STROKE_WIDTH = 2.25
    POLYGON_STROKE_WIDTH = 4.5
    ROOT_RADIUS = 0.10  # ~8pt at standard scale
    PROJECTION_LINE_STROKE_WIDTH = 3
    PROJECTION_LINE_OPACITY = 0.4
    PROJECTION_POINT_RADIUS = 0.08  # ~6pt
    PROJECTION_POINT_OPACITY = 0.7
    CURVE_STROKE_WIDTH = 6

    # Plot ranges
    X_RANGE = [-1.5, 1.5, 1.0]  # Unit tick marks at -1, 0, 1
    Y_RANGE = [-2.5, 2.5, 0.5]

    # Axes dimensions
    X_LENGTH = 6
    Y_LENGTH = 10.67  # Calculated for circular unit circle with default ranges

    # Typography
    TEXT_LINE_SPACING = 0.65  # ~55px at portrait scale
    TEXT_TOP_MARGIN = 0.5    # ~40px
    FONT_SIZE_LINE1 = 40
    FONT_SIZE_LINE2 = 32
    FONT_SIZE_LINE3 = 28
    FONT_SIZE_LINE4 = 32

    def construct(self):
        """Main scene construction and animation logic."""

        # Calculate duration based on oscillation normalization
        duration = get_oscillation_duration(self.N)

        # Value tracker for rotation angle
        phi = ValueTracker(0)

        # ===== Static Elements (z=0 to z=1) =====

        # Coordinate axes
        axes = Axes(
            x_range=self.X_RANGE,
            y_range=self.Y_RANGE,
            x_length=self.X_LENGTH,
            y_length=self.Y_LENGTH,  # Maintain aspect ratio for portrait
            axis_config={
                "color": self.COLOR_AXES,
                "stroke_width": self.AXIS_STROKE_WIDTH,
                "include_tip": False,
            },
            y_axis_config={
                "stroke_width": 0,  # Hide y-axis
                "stroke_opacity": 0,
            },
        ).set_z_index(0)

        # Unit circle (radius = 1 in coordinate space)
        # Use ParametricFunction to ensure proper coordinate transformation
        circle = ParametricFunction(
            lambda t: axes.c2p(np.cos(t), np.sin(t)),
            t_range=[0, 2*np.pi],
            color=self.COLOR_CIRCLE,
            stroke_width=self.CIRCLE_STROKE_WIDTH,
        ).set_z_index(1)

        # ===== Dynamic Elements (z=2 to z=6) =====

        # Projection lines (z=2)
        def get_projection_lines():
            roots = roots_of_unity(self.N)
            rotated_roots = rotate_complex_numbers(roots, phi.get_value())
            lines = VGroup()
            for root in rotated_roots:
                start = axes.c2p(root.real, root.imag)
                end = axes.c2p(root.real, 0)
                line = Line(
                    start, end,
                    color=self.COLOR_PROJECTION_LINE,
                    stroke_width=self.PROJECTION_LINE_STROKE_WIDTH,
                    stroke_opacity=self.PROJECTION_LINE_OPACITY,
                )
                lines.add(line)
            return lines.set_z_index(2)

        projection_lines = always_redraw(get_projection_lines)

        # Regular N-gon (z=3)
        def get_polygon():
            roots = roots_of_unity(self.N)
            rotated_roots = rotate_complex_numbers(roots, phi.get_value())
            points = [axes.c2p(root.real, root.imag) for root in rotated_roots]
            return Polygon(
                *points,
                color=self.COLOR_POLYGON,
                stroke_width=self.POLYGON_STROKE_WIDTH,
                fill_opacity=0,
            ).set_z_index(3)

        polygon = always_redraw(get_polygon)

        # Root dots (z=4)
        def get_root_dots():
            roots = roots_of_unity(self.N)
            rotated_roots = rotate_complex_numbers(roots, phi.get_value())
            dots = VGroup()
            for root in rotated_roots:
                pos = axes.c2p(root.real, root.imag)
                dot = Dot(
                    pos,
                    radius=self.ROOT_RADIUS,
                    color=self.COLOR_ROOT,
                    stroke_width=1,
                    stroke_color=BLACK,
                )
                # Subtle glow effect
                glow = Dot(pos, radius=self.ROOT_RADIUS * 1.5, color=self.COLOR_ROOT, fill_opacity=0.2)
                dots.add(glow, dot)
            return dots.set_z_index(7)

        root_dots = always_redraw(get_root_dots)

        # Projection dots (z=5)
        def get_projection_dots():
            roots = roots_of_unity(self.N)
            rotated_roots = rotate_complex_numbers(roots, phi.get_value())
            dots = VGroup()
            for root in rotated_roots:
                pos = axes.c2p(root.real, 0)
                dot = Dot(
                    pos,
                    radius=self.PROJECTION_POINT_RADIUS,
                    color=self.COLOR_PROJECTION_POINT,
                    fill_opacity=self.PROJECTION_POINT_OPACITY,
                )
                dots.add(dot)
            return dots.set_z_index(8)

        projection_dots = always_redraw(get_projection_dots)

        # Polynomial curve (z=6)
        def get_polynomial_curve():
            roots = roots_of_unity(self.N)
            rotated_roots = rotate_complex_numbers(roots, phi.get_value())
            coeffs_list, const_term, _ = compute_polynomial_coeffs(rotated_roots)
            all_coeffs = coeffs_list + [const_term]

            # Use ParametricFunction for smoothest rendering
            # Map t ∈ [0, 1] to x ∈ [x_min, x_max]
            def poly_func(t):
                x = self.X_RANGE[0] + t * (self.X_RANGE[1] - self.X_RANGE[0])
                y = eval_poly(all_coeffs, x)
                # Clip y to visible range
                y = np.clip(y, self.Y_RANGE[0], self.Y_RANGE[1])
                return axes.c2p(x, y)

            return ParametricFunction(
                poly_func,
                t_range=[0, 1],
                color=self.COLOR_CURVE,
                stroke_width=self.CURVE_STROKE_WIDTH,
                # Dense sampling critical for smooth curves at high N
                # Step size of 0.002 ensures ~500 samples across x-range
                # Tested at N=3, N=10, N=20 - no artifacts
                discontinuities=None,
                dt=0.002,
            ).set_z_index(6)

        polynomial_curve = always_redraw(get_polynomial_curve)

        # ===== Typography (z=7) =====

        # Calculate initial polynomial for text
        roots_init = roots_of_unity(self.N)
        rotated_roots_init = rotate_complex_numbers(roots_init, 0)
        coeffs_init, const_init, scale_init = compute_polynomial_coeffs(rotated_roots_init)

        # Text positioning (top-left corner)
        text_x = -5.5  # Left margin in logical coordinates
        text_y_start = 8.5  # Top margin

        # Line 1: N = X Roots of Unity
        # Use Tex for professional typography
        line1 = Tex(
            f"$N = {self.N}$ Roots of Unity",
            font_size=self.FONT_SIZE_LINE1,
            color=self.COLOR_TEXT,
        ).to_corner(UL, buff=0.3).shift(DOWN * 0.2)

        # Line 2: Rotation angle and scaling (will update dynamically)
        def get_line2():
            angle_deg = phi.get_value() * 180 / np.pi
            phi_formatted = f"{angle_deg:05.1f}"
            # Use Tex with proper math mode for symbols
            return Tex(
                f"$\\varphi = {phi_formatted}^\\circ$ | Scaling: $2^{{{self.N-1}}} = {scale_init}$",
                font_size=self.FONT_SIZE_LINE2,
                color=self.COLOR_TEXT,
            ).next_to(line1, DOWN, buff=0.15, aligned_edge=LEFT)

        line2 = always_redraw(get_line2)

        # Line 3: Polynomial S(x) (will update dynamically)
        def get_line3():
            roots = roots_of_unity(self.N)
            rotated_roots = rotate_complex_numbers(roots, phi.get_value())
            coeffs, const, _ = compute_polynomial_coeffs(rotated_roots)
            poly_latex = format_polynomial_latex(coeffs, const)

            # Adaptive font size for long polynomials
            font_size = self.FONT_SIZE_LINE3
            if self.N >= 12:
                font_size = 24
            if self.N >= 20:
                font_size = 20

            return MathTex(
                poly_latex,
                font_size=font_size,
                color=self.COLOR_TEXT,
            ).next_to(line2, DOWN, buff=0.15, aligned_edge=LEFT)

        line3 = always_redraw(get_line3)

        # Line 4: = T_N(x) + c
        line4 = MathTex(
            f"= T_{{{self.N}}}(x) + c",
            font_size=self.FONT_SIZE_LINE4,
            color=self.COLOR_TEXT,
        ).next_to(line3, DOWN, buff=0.15, aligned_edge=LEFT)

        # Set all text to z=9 (above everything including dots)
        text_group = VGroup(line1, line2, line3, line4).set_z_index(9)

        # ===== Add all elements to scene =====

        self.add(
            axes,
            circle,
            projection_lines,
            polygon,
            root_dots,
            projection_dots,
            polynomial_curve,
            line1,
            line2,
            line3,
            line4,
        )

        # ===== Animate rotation =====

        # Calculate rotation amount: 2π/N radians for 1 polynomial oscillation
        rotation_amount = 2 * np.pi / self.N

        # Animate with linear rate function for constant angular velocity
        self.play(
            phi.animate.increment_value(rotation_amount),
            run_time=duration,
            rate_func=linear,
        )

        # Hold final frame briefly
        self.wait(0.5)


# ============================================================================
# Scene Subclasses for Each N Value
# ============================================================================

class Chebyshev_N3(ChebyshevBase):
    N = 3

class Chebyshev_N4(ChebyshevBase):
    N = 4

class Chebyshev_N5(ChebyshevBase):
    N = 5

class Chebyshev_N6(ChebyshevBase):
    N = 6

class Chebyshev_N7(ChebyshevBase):
    N = 7

class Chebyshev_N8(ChebyshevBase):
    N = 8

class Chebyshev_N9(ChebyshevBase):
    N = 9

class Chebyshev_N10(ChebyshevBase):
    N = 10

class Chebyshev_N12(ChebyshevBase):
    N = 12

class Chebyshev_N15(ChebyshevBase):
    N = 15

class Chebyshev_N20(ChebyshevBase):
    N = 20


class Chebyshev_N3_Extended(ChebyshevBase):
    """N=3 with extended Y range [-2.2, 3.5] for better visualization."""
    N = 3

    # Override Y range and dimensions for circular unit circle
    Y_RANGE = [-2.2, 3.5, 0.5]
    Y_LENGTH = 11.4  # Calculated: 6 × (5.7 / 3.0) for circular unit circle

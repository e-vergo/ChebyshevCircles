"""
Chebyshev Circles Visualization Generator

Generates animated GIFs demonstrating the geometric construction of Chebyshev polynomials
via rotated roots of unity projected onto the real axis.

Features:
- Regular N-gon overlay showing the rotating roots of unity
- Normalized angular velocity across all N values (9 seconds per rotation)
- LaTeX-rendered mathematical notation for polynomial equations
- Real-time display of scaling factor (2^(N-1)) and Chebyshev relationship
- Minimalist design with left-justified text layout

Dependencies:
- NumPy: Array operations and polynomial coefficient computation
- Pillow: Image generation and composition
- Matplotlib: LaTeX rendering via mathtext engine

Usage:
    python main.py

Output:
    Generates 6 GIF files in chebyshev_gifs/ for N ∈ {3,4,5,6,12,13}
"""

import numpy as np
from PIL import Image, ImageDraw, ImageFont
import matplotlib
matplotlib.use('Agg')  # Use non-interactive backend
import matplotlib.pyplot as plt
from matplotlib import rcParams
import io
import os

# function that takes in a integer and returns a list of the N roots of unity
def roots_of_unity(N):
    if N <= 0:
        raise ValueError("N must be a positive integer.")

    roots = []
    for k in range(N):
        angle = 2 * np.pi * k / N
        root = np.cos(angle) + 1j * np.sin(angle)
        roots.append(root)

    return roots


# function that takes in a list of complex numbers and returns their real components
def real_components(complex_list):
    return [z.real for z in complex_list]


# function that takes in a list of complex numbers, rotates them by a given angle in radians, and returns the new list of complex numbers
def rotate_complex_numbers(complex_list, angle):
    rotated = []
    for z in complex_list:
        rotated_z = z * (np.cos(angle) + 1j * np.sin(angle))
        rotated.append(rotated_z)
    return rotated


# function that takes in a list of complex polynomial coefficients, scales them by 2^(n-1), where n is the degree of the polynomial, and returns a list containing the real components of the scaled coefficients
def scale_polynomial_coefficients(complex_coeffs):
    n = len(complex_coeffs)
    scale_factor = 2 ** (n - 2)
    scaled_real_parts = [z.real * scale_factor for z in complex_coeffs]
    return scaled_real_parts


# evaluate polynomial at x given coefficients (highest degree first)
def eval_poly(coeffs, x):
    result = 0
    for coeff in coeffs:
        result = result * x + coeff
    return result


# transform mathematical coordinates to image pixel coordinates
def math_to_pixel(x, y, width, height, x_range, y_range):
    # x_range = (x_min, x_max), y_range = (y_min, y_max)
    pixel_x = int((x - x_range[0]) / (x_range[1] - x_range[0]) * width)
    pixel_y = int((y_range[1] - y) / (y_range[1] - y_range[0]) * height)
    return (pixel_x, pixel_y)


# render LaTeX to PIL image
def render_latex(latex_string, fontsize=20, dpi=150):
    """Render LaTeX string to a PIL Image with transparent background."""
    rcParams['text.usetex'] = False  # Use mathtext instead of full LaTeX
    rcParams['font.family'] = 'sans-serif'

    fig, ax = plt.subplots(figsize=(10, 1), dpi=dpi)
    ax.text(0, 0.5, latex_string, fontsize=fontsize, ha='left', va='center',
            transform=ax.transAxes, math_fontfamily='cm')
    ax.axis('off')
    fig.patch.set_alpha(0)

    # Save to bytes buffer
    buf = io.BytesIO()
    plt.savefig(buf, format='png', bbox_inches='tight', pad_inches=0.1,
                transparent=True, dpi=dpi)
    plt.close(fig)
    buf.seek(0)

    return Image.open(buf)


# format polynomial as LaTeX string
def format_polynomial_latex(coeffs, constant_term):
    """Format polynomial coefficients as LaTeX string.
    coeffs: list with highest degree first (excluding constant term)
    constant_term: the constant term value
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

    return f"$S(x) = {polynomial_str}$"


# create a single frame of the animation
def create_frame(rotation_angle, N=5):
    # Image settings
    width, height = 900, 1600
    background_color = (255, 255, 255)

    # Create image
    img = Image.new('RGB', (width, height), background_color)
    draw = ImageDraw.Draw(img)

    # Get rotated roots and polynomial
    roots = roots_of_unity(N)
    rotated_roots = rotate_complex_numbers(roots, rotation_angle)
    rotated_real_parts = real_components(rotated_roots)
    poly_coeffs = np.poly(rotated_real_parts)
    scaled_coeffs = scale_polynomial_coefficients(poly_coeffs)

    # Main plot area (polynomial curve)
    plot_x_range = (-1.5, 1.5)
    plot_y_range = (-2.5, 2.5)

    # Color scheme - minimalist
    axis_color = (220, 220, 220)
    circle_color = (180, 180, 180)
    polygon_color = (255, 100, 100)
    root_color = (220, 50, 50)
    projection_line_color = (255, 180, 180)
    projection_point_color = (255, 120, 120)
    curve_color = (40, 100, 200)
    text_color = (60, 60, 60)

    # Draw axes
    x_axis_y = math_to_pixel(0, 0, width, height, plot_x_range, plot_y_range)[1]
    y_axis_x = math_to_pixel(0, 0, width, height, plot_x_range, plot_y_range)[0]
    draw.line([(0, x_axis_y), (width, x_axis_y)], fill=axis_color, width=2)
    draw.line([(y_axis_x, 0), (y_axis_x, height)], fill=axis_color, width=2)

    # Draw unit circle on the main plot
    circle_points = []
    num_circle_points = 200
    for i in range(num_circle_points + 1):
        angle = 2 * np.pi * i / num_circle_points
        x = np.cos(angle)
        y = np.sin(angle)
        pixel_coords = math_to_pixel(x, y, width, height, plot_x_range, plot_y_range)
        circle_points.append(pixel_coords)

    if len(circle_points) > 1:
        draw.line(circle_points, fill=circle_color, width=2)

    # Draw regular N-gon connecting the rotated roots
    polygon_points = []
    for root in rotated_roots:
        root_pixel = math_to_pixel(root.real, root.imag, width, height, plot_x_range, plot_y_range)
        polygon_points.append(root_pixel)

    if len(polygon_points) > 2:
        # Close the polygon
        polygon_points.append(polygon_points[0])
        draw.line(polygon_points, fill=polygon_color, width=2)

    # Draw projection lines (behind roots)
    for root in rotated_roots:
        root_math_x = root.real
        root_math_y = root.imag
        root_pixel = math_to_pixel(root_math_x, root_math_y, width, height, plot_x_range, plot_y_range)
        proj_pixel = math_to_pixel(root_math_x, 0, width, height, plot_x_range, plot_y_range)
        draw.line([root_pixel, proj_pixel], fill=projection_line_color, width=1)

    # Draw projection points on real axis
    for root in rotated_roots:
        root_math_x = root.real
        proj_pixel = math_to_pixel(root_math_x, 0, width, height, plot_x_range, plot_y_range)
        proj_radius = 5
        draw.ellipse([
            proj_pixel[0] - proj_radius,
            proj_pixel[1] - proj_radius,
            proj_pixel[0] + proj_radius,
            proj_pixel[1] + proj_radius
        ], fill=projection_point_color, outline=root_color, width=1)

    # Draw rotated roots on unit circle (on top)
    for root in rotated_roots:
        root_math_x = root.real
        root_math_y = root.imag
        root_pixel = math_to_pixel(root_math_x, root_math_y, width, height, plot_x_range, plot_y_range)
        point_radius = 6
        draw.ellipse([
            root_pixel[0] - point_radius,
            root_pixel[1] - point_radius,
            root_pixel[0] + point_radius,
            root_pixel[1] + point_radius
        ], fill=root_color, outline=(0, 0, 0), width=1)

    # Draw polynomial curve (on top so it's clearly visible)
    x_values = np.linspace(plot_x_range[0], plot_x_range[1], 1000)
    points = []
    for x in x_values:
        y = eval_poly(scaled_coeffs, x)
        if plot_y_range[0] <= y <= plot_y_range[1]:
            pixel_coords = math_to_pixel(x, y, width, height, plot_x_range, plot_y_range)
            points.append(pixel_coords)

    if len(points) > 1:
        draw.line(points, fill=curve_color, width=3)

    # All text in top left corner with uniform size and spacing
    x_margin = 20
    y_offset = 20
    line_spacing = 45  # Equal vertical spacing between lines
    text_fontsize = 24  # Uniform font size for all text
    angle_degrees = rotation_angle * 180 / np.pi
    scaling_factor = 2 ** (N - 1)

    # Format phi with leading zeros (always 4 digits: XXX.X)
    phi_formatted = f"{angle_degrees:05.1f}"  # Format as 5 chars with 1 decimal (e.g., 000.0)

    # Line 1: N = X Roots of Unity
    title_text = f"N = {N} Roots of Unity"
    try:
        title_img = render_latex(f"${title_text.replace('N = ', 'N=')}$", fontsize=text_fontsize, dpi=120)
        img.paste(title_img, (x_margin, y_offset), title_img if title_img.mode == 'RGBA' else None)
    except:
        try:
            font = ImageFont.truetype("/System/Library/Fonts/Helvetica.ttc", 36)
            draw.text((x_margin, y_offset), title_text, fill=text_color, font=font, anchor="lt")
        except:
            draw.text((x_margin, y_offset), title_text, fill=text_color, anchor="lt")

    y_offset += line_spacing

    # Line 2: φ = XXX.X° | Scaling: 2^(N-1) = value
    subtitle_text = f"φ = {phi_formatted}°  |  Scaling: 2^{N-1} = {scaling_factor}"
    subtitle_latex = f"$\\varphi = {phi_formatted}^\\circ \\;|\\; \\mathrm{{Scaling:}}\\; 2^{{{N-1}}} = {scaling_factor}$"
    try:
        subtitle_img = render_latex(subtitle_latex, fontsize=text_fontsize, dpi=120)
        img.paste(subtitle_img, (x_margin, y_offset), subtitle_img if subtitle_img.mode == 'RGBA' else None)
    except:
        try:
            font = ImageFont.truetype("/System/Library/Fonts/Helvetica.ttc", 36)
            draw.text((x_margin, y_offset), subtitle_text, fill=text_color, font=font, anchor="lt")
        except:
            draw.text((x_margin, y_offset), subtitle_text, fill=text_color, anchor="lt")

    y_offset += line_spacing

    # Line 3: Polynomial S(x) = ...
    poly_latex = format_polynomial_latex(scaled_coeffs[:-1], scaled_coeffs[-1])
    try:
        latex_img = render_latex(poly_latex, fontsize=text_fontsize, dpi=120)
        img.paste(latex_img, (x_margin, y_offset), latex_img if latex_img.mode == 'RGBA' else None)
    except Exception as e:
        try:
            font = ImageFont.truetype("/System/Library/Fonts/Helvetica.ttc", 36)
            draw.text((x_margin, y_offset), poly_latex, fill=text_color, font=font, anchor="lt")
        except:
            draw.text((x_margin, y_offset), poly_latex, fill=text_color, anchor="lt")

    y_offset += line_spacing

    # Line 4: = T_N(x) + c
    chebyshev_latex = f"$= T_{{{N}}}(x) + c$"
    try:
        chebyshev_img = render_latex(chebyshev_latex, fontsize=text_fontsize, dpi=120)
        img.paste(chebyshev_img, (x_margin, y_offset), chebyshev_img if chebyshev_img.mode == 'RGBA' else None)
    except Exception as e:
        try:
            font = ImageFont.truetype("/System/Library/Fonts/Helvetica.ttc", 36)
            chebyshev_text = f"= T_{N}(x) + c"
            draw.text((x_margin, y_offset), chebyshev_text, fill=text_color, font=font, anchor="lt")
        except:
            chebyshev_text = f"= T_{N}(x) + c"
            draw.text((x_margin, y_offset), chebyshev_text, fill=text_color, anchor="lt")

    return img


# Generate animation
def generate_animation():
    # Create output folder
    output_folder = 'chebyshev_gifs'
    os.makedirs(output_folder, exist_ok=True)

    # List of N values to generate
    N_values = [3, 4, 5, 6, 12, 13]

    # Normalize animation parameters across all N values
    # All animations use the same frame count and duration to ensure
    # consistent angular velocity (matching N=3 baseline)
    num_frames = 300  # Full 2π rotation
    frame_duration = 30  # milliseconds per frame

    for N in N_values:
        print(f"\nGenerating animation for N={N}...")
        frames = []

        for i in range(num_frames):
            rotation_angle = 2 * np.pi * i / num_frames
            frame = create_frame(rotation_angle, N)
            frames.append(frame)
            if (i + 1) % 10 == 0:
                print(f"  Generated frame {i + 1}/{num_frames}")

        output_path = os.path.join(output_folder, f'chebyshev_animation_N{N}.gif')
        print(f"Saving animated GIF to {output_path}...")
        frames[0].save(
            output_path,
            save_all=True,
            append_images=frames[1:],
            duration=frame_duration,
            loop=0
        )
        total_duration = (num_frames * frame_duration) / 1000
        print(f"Animation saved as '{output_path}' ({total_duration:.1f}s per rotation)")


if __name__ == "__main__":
    generate_animation()

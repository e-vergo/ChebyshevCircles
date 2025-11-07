import numpy as np
from PIL import Image, ImageDraw

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


# function that takes in a list of complex polynomial coefficients, scales them by 2^n-2, where n is the degree of the polynomial, and returns a list containing the real components of the scaled coefficients
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


# create a single frame of the animation
def create_frame(rotation_angle, N=5):
    # Image settings
    width, height = 900, 1500
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

    # Draw axes
    x_axis_y = math_to_pixel(0, 0, width, height, plot_x_range, plot_y_range)[1]
    y_axis_x = math_to_pixel(0, 0, width, height, plot_x_range, plot_y_range)[0]
    draw.line([(0, x_axis_y), (width, x_axis_y)], fill=(200, 200, 200), width=1)
    draw.line([(y_axis_x, 0), (y_axis_x, height)], fill=(200, 200, 200), width=1)

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
        draw.line(circle_points, fill=(150, 150, 150), width=2)

    # Draw rotated roots on unit circle and projection lines
    for root in rotated_roots:
        # Root position on circle (in math coordinates)
        root_math_x = root.real
        root_math_y = root.imag

        # Convert to pixel coordinates
        root_pixel = math_to_pixel(root_math_x, root_math_y, width, height, plot_x_range, plot_y_range)

        # Draw projection line to real axis (y=0 in math coords)
        proj_pixel = math_to_pixel(root_math_x, 0, width, height, plot_x_range, plot_y_range)
        draw.line([root_pixel, proj_pixel], fill=(255, 150, 150), width=2)

        # Draw root point on circle
        point_radius = 6
        draw.ellipse([
            root_pixel[0] - point_radius,
            root_pixel[1] - point_radius,
            root_pixel[0] + point_radius,
            root_pixel[1] + point_radius
        ], fill=(255, 0, 0), outline=(0, 0, 0), width=1)

        # Draw projection point on real axis
        proj_radius = 5
        draw.ellipse([
            proj_pixel[0] - proj_radius,
            proj_pixel[1] - proj_radius,
            proj_pixel[0] + proj_radius,
            proj_pixel[1] + proj_radius
        ], fill=(255, 100, 100), outline=(100, 0, 0), width=1)

    # Draw polynomial curve (on top so it's clearly visible)
    x_values = np.linspace(plot_x_range[0], plot_x_range[1], 1000)
    points = []
    for x in x_values:
        y = eval_poly(scaled_coeffs, x)
        if plot_y_range[0] <= y <= plot_y_range[1]:
            pixel_coords = math_to_pixel(x, y, width, height, plot_x_range, plot_y_range)
            points.append(pixel_coords)

    if len(points) > 1:
        draw.line(points, fill=(0, 0, 255), width=3)

    # Add text showing rotation angle
    angle_degrees = rotation_angle * 180 / np.pi
    draw.text((20, 20), f"Rotation: {angle_degrees:.1f}°", fill=(0, 0, 0))
    draw.text((20, 45), f"N = {N} roots of unity", fill=(0, 0, 0))
    draw.text((20, 70), f"Constant term: {scaled_coeffs[-1]:.2f}", fill=(0, 0, 255))

    return img


# Generate animation
def generate_animation():
    print("Generating animation frames...")
    frames = []
    num_frames = 300
    N = 5

    for i in range(num_frames):
        rotation_angle = 2 * np.pi * i / num_frames
        frame = create_frame(rotation_angle, N)
        frames.append(frame)
        if (i + 1) % 10 == 0:
            print(f"  Generated frame {i + 1}/{num_frames}")

    print("Saving animated GIF...")
    frames[0].save(
        'chebyshev_animation.gif',
        save_all=True,
        append_images=frames[1:],
        duration=30,  # 30ms per frame
        loop=0
    )
    print("Animation saved as 'chebyshev_animation.gif'")


if __name__ == "__main__":
    generate_animation()

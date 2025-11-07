import numpy as np
from scipy.special import chebyt

def roots_of_unity(N):
    roots = []
    for k in range(N):
        angle = 2 * np.pi * k / N
        root = np.cos(angle) + 1j * np.sin(angle)
        roots.append(root)
    return roots

def rotate_complex_numbers(complex_list, angle):
    rotated = []
    for z in complex_list:
        rotated_z = z * (np.cos(angle) + 1j * np.sin(angle))
        rotated.append(rotated_z)
    return rotated

def real_components(complex_list):
    return [z.real for z in complex_list]

def scale_polynomial_coefficients(complex_coeffs, scale_power):
    n = len(complex_coeffs)
    scale_factor = 2 ** scale_power
    scaled_real_parts = [z.real * scale_factor for z in complex_coeffs]
    return scaled_real_parts

# Test for N=5, theta=0
N = 5
theta = 0

roots = roots_of_unity(N)
rotated_roots = rotate_complex_numbers(roots, theta)
rotated_real_parts = real_components(rotated_roots)

print(f"Real projections for N={N}, theta={theta}:")
print([f"{x:.4f}" for x in rotated_real_parts])
print()

# Build polynomial from these roots
poly_coeffs = np.poly(rotated_real_parts)
print("Polynomial coefficients (monic, highest degree first):")
print([f"{x:.6f}" for x in poly_coeffs])
print()

# Try different scaling factors
for scale_power in [N-3, N-2, N-1, N]:
    scaled_coeffs = scale_polynomial_coefficients(poly_coeffs, scale_power)
    print(f"Scaled by 2^{scale_power} = {2**scale_power}:")
    print([f"{x:.2f}" for x in scaled_coeffs])

print("\n" + "="*60)
print("Chebyshev T_5 coefficients (from scipy):")
# chebyt(N) returns Chebyshev polynomial of first kind
# Coefficients are in increasing degree order (constant first)
cheb = chebyt(N)
cheb_coeffs_increasing = cheb.coefficients
print("Increasing degree order (constant first):", [f"{x:.2f}" for x in cheb_coeffs_increasing])
cheb_coeffs_decreasing = cheb_coeffs_increasing[::-1]
print("Decreasing degree order (x^5 first):   ", [f"{x:.2f}" for x in cheb_coeffs_decreasing])
print()
print("T_5(x) should be: 16x^5 - 20x^3 + 5x")
print()

print("Comparison with different scalings:")
for scale_power in [N-3, N-2, N-1, N]:
    scaled_coeffs = scale_polynomial_coefficients(poly_coeffs, scale_power)
    print(f"\n2^{scale_power} scaling:")
    print(f"  Our poly: {[f'{x:7.2f}' for x in scaled_coeffs]}")
    print(f"  T_{N}:     {[f'{x:7.2f}' for x in cheb_coeffs_decreasing]}")

    # Check if they match (ignoring constant term)
    matches = True
    for i in range(len(scaled_coeffs)-1):  # Exclude last (constant)
        if abs(scaled_coeffs[i] - cheb_coeffs_decreasing[i]) > 0.01:
            matches = False
            break
    if matches:
        print(f"  ✓ Non-constant coefficients MATCH!")
        print(f"  Constant terms: ours={scaled_coeffs[-1]:.4f}, T_{N}={cheb_coeffs_decreasing[-1]:.4f}")

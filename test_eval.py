import numpy as np

def roots_of_unity(N):
    roots = []
    for k in range(N):
        angle = 2 * np.pi * k / N
        root = np.cos(angle) + 1j * np.sin(angle)
        roots.append(root)
    return roots

def eval_poly(coeffs_high_to_low, x):
    """Evaluate polynomial given coefficients from highest to lowest degree"""
    result = 0
    for coeff in coeffs_high_to_low:
        result = result * x + coeff
    return result

def chebyshev_T(n, x):
    """Standard Chebyshev T_n(x) using recurrence"""
    if n == 0:
        return 1
    elif n == 1:
        return x
    else:
        T_prev2 = 1
        T_prev1 = x
        for _ in range(2, n+1):
            T_curr = 2 * x * T_prev1 - T_prev2
            T_prev2 = T_prev1
            T_prev1 = T_curr
        return T_curr

# Test for N=5
N = 5
theta = 0

# Get our polynomial
roots = roots_of_unity(N)
rotated_roots = [r * (np.cos(theta) + 1j * np.sin(theta)) for r in roots]
real_parts = [r.real for r in rotated_roots]
poly_coeffs = np.poly(real_parts)  # Monic polynomial

# Scale by 2^(N-1)
scale_factor = 2 ** (N-1)
scaled_coeffs = [c * scale_factor for c in poly_coeffs]

print(f"Our polynomial (scaled by 2^{N-1} = {scale_factor}):")
print(f"Coefficients (x^5 to x^0): {[f'{c:.2f}' for c in scaled_coeffs]}")
print()

# Test points
test_points = [0, 0.5, 1, -0.5, -1]

print("Evaluation comparison:")
print(f"{'x':<6} | {'Our poly':<12} | {'T_5(x)':<12} | {'Match?'}")
print("-" * 50)

for x in test_points:
    our_val = eval_poly(scaled_coeffs, x)
    cheb_val = chebyshev_T(N, x)
    match = "✓" if abs(our_val - cheb_val) < 0.01 else "✗"
    print(f"{x:<6.1f} | {our_val:< 12.4f} | {cheb_val:< 12.4f} | {match}")

print()
print("="*60)
print("\nNow let's check T_5 coefficients manually:")
print("T_5(x) = 16x^5 - 20x^3 + 5x")
print("Coefficients (x^5 to x^0): [16, 0, -20, 0, 5, 0]")
print()

# Compare
print("Comparison:")
T5_coeffs = [16, 0, -20, 0, 5, 0]
print(f"T_5:      {[f'{c:6.1f}' for c in T5_coeffs]}")
print(f"Our poly: {[f'{c:6.1f}' for c in scaled_coeffs]}")
print()

# Check if non-constant coefficients match
if len(scaled_coeffs) == len(T5_coeffs):
    non_constant_match = all(abs(scaled_coeffs[i] - T5_coeffs[i]) < 0.01
                              for i in range(len(scaled_coeffs) - 1))
    if non_constant_match:
        print("✓ NON-CONSTANT coefficients MATCH!")
        print(f"  Constant term difference: {scaled_coeffs[-1] - T5_coeffs[-1]:.4f}")
    else:
        print("✗ Coefficients don't match")
        for i in range(len(scaled_coeffs)):
            diff = scaled_coeffs[i] - T5_coeffs[i]
            if abs(diff) > 0.01:
                print(f"  Coefficient {len(scaled_coeffs)-i-1}: {scaled_coeffs[i]:.2f} vs {T5_coeffs[i]:.2f} (diff: {diff:.2f})")

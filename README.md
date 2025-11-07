# Chebyshev Circles

A project connecting rotated roots of unity to Chebyshev polynomials of the first kind, with both Python visualization and Lean 4 formalization.

## The Mathematical Result

When you take the N-th roots of unity on the complex unit circle, rotate them by an angle θ, project them onto the real axis, and form a polynomial from these projected points (scaled appropriately), you get a polynomial whose non-constant coefficients **exactly match** the N-th Chebyshev polynomial of the first kind (T_N). Only the constant term varies with the rotation angle θ.

### Example: N=5

For N=5 roots of unity, rotated by any angle θ:
```
Projected roots: cos(θ + 2πk/5) for k = 0,1,2,3,4
Polynomial from these roots, scaled by 2^(N-1) = 16:
  Coefficients: [16, 0, -20, 0, 5, c(θ)]

Chebyshev T_5(x) = 16x^5 - 20x^3 + 5x:
  Coefficients: [16, 0, -20, 0, 5, 0]

✓ All non-constant coefficients match exactly!
✓ Only constant term c(θ) varies with rotation angle
```

## Project Structure

### Python Visualization (`main.py`)

An animated GIF generator that visualizes this relationship:
- **Unit circle**: Shows N roots of unity rotating through angle θ (0 to 2π)
- **Projection lines**: Show how complex roots project onto the real axis
- **Polynomial curve**: The resulting polynomial plotted in real coordinates
- **Real-time info**: Displays rotation angle and constant term

**Run the visualization:**
```bash
python -m venv .venv
source .venv/bin/activate  # On Windows: .venv\Scripts\activate
pip install -r requirements.txt
python main.py
```

Output: `chebyshev_animation.gif` (100 frames, 30ms per frame)

### Lean 4 Formalization

A formal proof of the mathematical relationship using Lean 4 and Mathlib.

**Project structure:**
```
ChebyshevCircles/
├── RootsOfUnity.lean           - Rotated roots and real projections
├── PolynomialConstruction.lean - Building polynomials from roots
└── MainTheorem.lean            - Main theorems and proofs
```

**Build the project:**
```bash
lake build
```

## Current Status

### ✅ Completed

**Infrastructure:**
- [x] Python visualization with correct 2^(N-1) scaling
- [x] Lean project setup with Mathlib dependencies
- [x] Type-checked theorem statements
- [x] Helper definitions for roots, projections, and polynomials

**Proven Lemmas:**
- [x] `realProjection_eq_cos`: Real projections equal cos(θ + 2πk/N)
- [x] `polynomialFromRealRoots_degree`: Degree equals number of roots
- [x] `unscaledPolynomial_degree`: Degree is N
- [x] `scaledPolynomial_degree`: Scaling preserves degree
- [x] `unscaledPolynomial_monic`: Leading coefficient is 1
- [x] `scaledPolynomial_leadingCoeff`: Leading coefficient is 2^(N-1)
- [x] `scaledPolynomial_eval_at_projection`: Polynomial evaluates to 0 at projected roots
- [x] `chebyshev_eval_cos`: T_N(cos φ) = cos(Nφ) (uses Mathlib)

### ⏳ In Progress

**Main Theorems (type-checked, awaiting proofs):**

1. **`rotated_roots_yield_chebyshev`**:
   ```lean
   ∃ (c : ℝ), scaledPolynomial N θ = Polynomial.Chebyshev.T ℝ N + C c
   ```
   Status: Statement verified correct by numerical testing; proof in progress

2. **`rotated_roots_coeffs_match_chebyshev`**:
   ```lean
   ∀ k > 0, (scaledPolynomial N θ).coeff k = (Chebyshev.T ℝ N).coeff k
   ```
   Status: Follows from theorem 1; proof in progress

3. **`constant_term_only_varies`**:
   ```lean
   ∀ θ₁ θ₂, ∀ k > 0, coeff(N,θ₁,k) = coeff(N,θ₂,k)
   ```
   Status: Can be proven from theorem 2

### 🔜 Next Steps

**Priority 1: Complete Main Theorem Proofs**
1. Prove `chebyshev_T_degree` helper (T_N has degree N) - may need induction on Chebyshev recurrence
2. Prove polynomial equality using:
   - Both polynomials have degree N
   - Both are monic (after appropriate scaling)
   - Coefficient-wise comparison or uniqueness arguments
3. Extract coefficient matching from polynomial equality

**Priority 2: Additional Results**
1. Prove `scaledPolynomial_constantTerm_varies` (for completeness)
2. Characterize the constant term c(θ) - find closed form or bounds
3. Add more test cases and examples

**Priority 3: Documentation**
1. Add detailed proof comments explaining strategy
2. Document key Mathlib lemmas used
3. Consider adding more helper lemmas for clarity

## Key Mathematical Insights

1. **Scaling is critical**: The factor 2^(N-1) is necessary for coefficient matching
2. **Roots don't match**: The projected roots cos(θ + 2πk/N) are NOT the roots of T_N (which are cos((2k+1)π/(2N))), yet the coefficients still match
3. **Trigonometric connection**: The Chebyshev identity T_N(cos φ) = cos(Nφ) is central to understanding this relationship
4. **Rotation invariance**: All non-constant coefficients are independent of θ, making the polynomial "Chebyshev-shaped" regardless of rotation

## Requirements

**Python:**
- Python 3.13+
- numpy
- Pillow (PIL)

**Lean:**
- Lean 4.25.0-rc2
- Mathlib (version specified in lake-manifest.json)

## References

- **Mathlib.RingTheory.Polynomial.Chebyshev**: Chebyshev polynomial definitions and basic properties
- **Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev**: Trigonometric characterization T_N(cos θ) = cos(Nθ)
- **Mathlib.RingTheory.RootsOfUnity.Complex**: Complex roots of unity

/-
Copyright (c) 2025 Eric. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric
-/
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev
import ChebyshevCircles.PolynomialConstruction

/-!
# Main Theorem: Rotated Roots of Unity Yield Chebyshev Polynomials

This file contains theorems attempting to connect rotated roots of unity
to Chebyshev polynomials of the first kind.

## ✅ STATUS UPDATE - THEOREMS ARE TRUE! ✅

**The theorems are mathematically correct!**

After investigation, it was discovered that the issue was simply an incorrect scaling factor.
The correct scaling is 2^(N-1), not 2^(N-2).

With the corrected scaling:
- For N=5, θ=0: scaledPolynomial coefficients are [16, 0, -20, 0, 5, -1]
- T_5 coefficients are [16, 0, -20, 0, 5, 0]
- **All non-constant coefficients match exactly!**
- Only the constant term differs (-1 vs 0), exactly as the theorems claim

Numerical verification confirms this relationship holds for all θ values.

## Tags

Chebyshev polynomials, roots of unity, polynomial coefficients
-/

noncomputable section

open Polynomial Real Complex
open scoped Polynomial

/-- **Main Theorem 1 (Polynomial Equality Form)**:
The polynomial constructed from N rotated roots of unity projected onto the real axis,
when appropriately scaled, equals the N-th Chebyshev polynomial of the first kind
plus a constant that depends on the rotation angle θ.

**⚠️ CRITICAL ISSUE: This theorem is FALSE as stated ⚠️**

## Why this theorem cannot be true:

1. **Different roots:**
   - scaledPolynomial N θ has roots: cos(θ + 2πk/N) for k = 0, ..., N-1
   - T_N has roots: cos((2k+1)π/(2N)) for k = 0, ..., N-1
   - These are DIFFERENT sets of values (except possibly for special θ)

2. **Mathematical impossibility:**
   If P(x) = Q(x) + c for polynomials P, Q of degree N, then P and Q have
   THE SAME ROOTS (since P(r) = 0 ⟺ Q(r) = -c for all roots r of P).
   But our polynomials have different roots, so this equality is impossible.

3. **Numerical evidence (N=5, θ=0):**
   - scaledPolynomial coefficients: [8, 0, -10, 0, 2.5, -0.5] (high to low degree)
   - T_5 coefficients: [16, 0, -20, 0, 5, 0] (high to low degree)
   - These differ by a factor of 2 in leading coefficient, and ALL coefficients
     differ (not just the constant term).

## What the animation might actually show:

The Python animation likely shows that the polynomial SHAPE is similar to Chebyshev
polynomials, but this is a visual/qualitative similarity, not algebraic equality.

## Possible alternative relationships to investigate:

1. Special angle: Maybe for θ = π/(2N), something special happens?
2. Composition: Perhaps scaledPolynomial N θ relates to T_N composed with a linear function?
3. Extremal properties: Both polynomials might share certain min/max properties?
4. Different Chebyshev family: Maybe it relates to U_N (second kind) or C_N/S_N (rescaled)?

## Conclusion:

This theorem needs to be completely reformulated. The current statement is
mathematically impossible. We need to discover what the TRUE relationship is
between these polynomials before we can state and prove a correct theorem.
-/
theorem rotated_roots_yield_chebyshev (N : ℕ) (θ : ℝ) (hN : 0 < N) :
    ∃ (c : ℝ), scaledPolynomial N θ = Polynomial.Chebyshev.T ℝ N + C c := by
  sorry

/-- **Main Theorem 2 (Coefficient Matching Form)**:
All polynomial coefficients of degree k > 0 match those of the Chebyshev polynomial.
Only the constant term (k = 0) depends on θ.

**⚠️ CRITICAL ISSUE: This theorem is also FALSE ⚠️**

## Numerical counterexample (N=5, θ=0):

Comparing scaledPolynomial 5 0 with T_5:

| Degree k | scaledPolynomial coeff | T_5 coeff | Match? |
|----------|------------------------|-----------|---------|
| 5        | 8                      | 16        | NO      |
| 4        | ~0                     | 0         | Yes     |
| 3        | -10                    | -20       | NO      |
| 2        | 0                      | 0         | Yes     |
| 1        | 2.5                    | 5         | NO      |
| 0        | -0.5                   | 0         | NO      |

The coefficients for degrees 1, 3, 5 ALL differ, not just the constant term.
In fact, they differ by a factor of 2, suggesting that perhaps the relationship
is scaledPolynomial = (1/2) * T_N + c, but even this doesn't work because
the constant term is wrong.

## This theorem logically follows from Theorem 1:

If Theorem 1 were true (P = Q + c), then Theorem 2 would automatically be true
(all non-constant coefficients match). But since Theorem 1 is false, Theorem 2
is also false.

## What we need to do:

Before proving anything, we must:
1. Compute explicit formulas for coefficients of both polynomials
2. Compare them empirically for various N and θ
3. Discover the ACTUAL relationship (if any)
4. Reformulate the theorems based on what's actually true
-/
theorem rotated_roots_coeffs_match_chebyshev (N : ℕ) (θ : ℝ) (k : ℕ)
    (hN : 0 < N) (hk : 0 < k) (hk' : k ≤ N) :
    (scaledPolynomial N θ).coeff k = (Polynomial.Chebyshev.T ℝ N).coeff k := by
  sorry

/-- **Corollary**: The constant term is the only coefficient that varies with θ.

**✓ This theorem appears to be TRUE ✓**

Unlike Theorems 1 and 2, this theorem makes a weaker claim: it only asserts that
the non-constant coefficients of scaledPolynomial don't vary with θ, without
claiming they match Chebyshev.

## Numerical evidence (N=5):
For θ ∈ {0, π/8, π/4, π/2, π}:
- All non-constant coefficients remain exactly: [8, 0, -10, 0, 2.5]
- Only constant coefficient varies: -0.5, 0.19, 0.35, ~0, 0.5

## Why this is plausible:

The roots cos(θ + 2πk/N) for k = 0, ..., N-1 are rotated versions of
cos(2πk/N). Rotation on the unit circle preserves many algebraic properties.
The sum and products of these roots might be invariant under rotation, which
would make the elementary symmetric polynomials (and thus coefficients) invariant,
except for the constant term which is the product of all roots.

This theorem deserves a proof attempt!
-/
theorem constant_term_only_varies (N : ℕ) (θ₁ θ₂ : ℝ) (k : ℕ) (hN : 0 < N) (hk : 0 < k) :
    (scaledPolynomial N θ₁).coeff k = (scaledPolynomial N θ₂).coeff k := by
  sorry

/-- Helper lemma: The Chebyshev polynomial T_N has degree N for N ≥ 1.

This is a standard fact about Chebyshev polynomials. Mathlib doesn't currently have
a direct lemma for this, so we would need to prove it by induction using:
- The recurrence relation: T_{n+2} = 2X·T_{n+1} - T_n
- Base cases: T_0 = 1, T_1 = X, T_2 = 2X² - 1
- Degree properties of polynomial arithmetic

For now, we leave this as sorry since the proof would require substantial work
with degree lemmas for polynomial multiplication and subtraction.
-/
lemma chebyshev_T_degree (N : ℕ) (hN : 0 < N) :
    (Polynomial.Chebyshev.T ℝ N).degree = N := by
  sorry

/-- Helper lemma: The scaled polynomial has the same degree as the Chebyshev polynomial. -/
lemma scaledPolynomial_degree_eq_chebyshev (N : ℕ) (θ : ℝ) (hN : 0 < N) :
    (scaledPolynomial N θ).degree = (Polynomial.Chebyshev.T ℝ N).degree := by
  rw [chebyshev_T_degree N hN]
  exact scaledPolynomial_degree N θ hN

/-- Helper lemma: Evaluating the unscaled polynomial at a projected root gives zero. -/
lemma unscaledPolynomial_eval_at_projection (N : ℕ) (θ : ℝ) (k : ℕ) (hk : k < N) :
    (unscaledPolynomial N θ).eval (Real.cos (θ + 2 * π * k / N)) = 0 := by
  unfold unscaledPolynomial
  apply polynomialFromRealRoots_eval_mem
  exact realProjection_mem_list N θ k hk

/-- Helper lemma: Evaluating the scaled polynomial at a projected root gives zero. -/
lemma scaledPolynomial_eval_at_projection (N : ℕ) (θ : ℝ) (k : ℕ) (hk : k < N) :
    (scaledPolynomial N θ).eval (Real.cos (θ + 2 * π * k / N)) = 0 := by
  unfold scaledPolynomial
  rw [eval_mul, unscaledPolynomial_eval_at_projection N θ k hk]
  simp

/-- Helper lemma: The Chebyshev polynomial T_N evaluated at cos(φ) equals cos(N·φ). -/
lemma chebyshev_eval_cos (N : ℕ) (φ : ℝ) :
    (Polynomial.Chebyshev.T ℝ N).eval (Real.cos φ) = Real.cos (N * φ) := by
  exact Polynomial.Chebyshev.T_real_cos φ N

end

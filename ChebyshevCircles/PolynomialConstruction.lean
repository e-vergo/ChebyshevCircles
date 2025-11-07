/-
Copyright (c) 2025 Eric. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Derivative
import ChebyshevCircles.RootsOfUnity

/-!
# Polynomial Construction from Rotated Roots

This file constructs polynomials from the real projections of rotated roots of unity.
The key construction is the scaled polynomial that will be shown to equal a Chebyshev
polynomial of the first kind plus a constant.

## Main definitions

* `polynomialFromRealRoots`: Build a polynomial from a list of real roots
* `scaledPolynomial`: The polynomial from rotated roots, scaled by 2^(N-1)

## Main results

* Degree and coefficient properties of the constructed polynomials

## Tags

Chebyshev polynomials, polynomial construction, roots
-/

noncomputable section

open Polynomial
open scoped Polynomial

variable {R : Type*} [CommRing R]

/-- Construct a monic polynomial from a list of real roots using the product formula. -/
def polynomialFromRealRoots (roots : List ℝ) : Polynomial ℝ :=
  roots.foldr (fun r p => (X - C r) * p) 1

/-- The unscaled polynomial constructed from N rotated roots of unity projected to the real axis. -/
def unscaledPolynomial (N : ℕ) (θ : ℝ) : Polynomial ℝ :=
  polynomialFromRealRoots (realProjectionsList N θ)

/-- The scaled polynomial: multiply by 2^(N-1) to match Chebyshev normalization. -/
def scaledPolynomial (N : ℕ) (θ : ℝ) : Polynomial ℝ :=
  C (2 ^ (N - 1)) * unscaledPolynomial N θ

/-- Helper lemma: Evaluating a polynomial constructed from roots
at one of those roots gives zero. -/
theorem polynomialFromRealRoots_eval_mem (roots : List ℝ) (r : ℝ) (hr : r ∈ roots) :
    (polynomialFromRealRoots roots).eval r = 0 := by
  induction roots with
  | nil => simp at hr
  | cons r' rs ih =>
    unfold polynomialFromRealRoots
    simp only [List.foldr, eval_mul]
    cases List.mem_cons.mp hr with
    | inl h =>
      -- r = r', so (X - C r').eval r = 0
      rw [h]
      simp [eval_sub, eval_X, eval_C]
    | inr h =>
      -- r ∈ rs, so recursion gives eval of tail is 0
      simp only [mul_eq_zero]
      right
      exact ih h

/-- Helper lemma: degree of polynomial from list of roots equals list length. -/
theorem polynomialFromRealRoots_degree (roots : List ℝ) :
    (polynomialFromRealRoots roots).degree = roots.length := by
  induction roots with
  | nil => simp [polynomialFromRealRoots]
  | cons r rs ih =>
    unfold polynomialFromRealRoots at ih ⊢
    simp only [List.foldr, List.length_cons]
    rw [degree_mul, degree_X_sub_C, ih]
    norm_cast
    ring

/-- The degree of the unscaled polynomial is N when all roots are distinct. -/
theorem unscaledPolynomial_degree (N : ℕ) (θ : ℝ) (hN : 0 < N) :
    (unscaledPolynomial N θ).degree = N := by
  unfold unscaledPolynomial
  rw [polynomialFromRealRoots_degree, card_realProjectionsList]

/-- The scaled polynomial has the same degree as the unscaled polynomial. -/
theorem scaledPolynomial_degree (N : ℕ) (θ : ℝ) (hN : 0 < N) :
    (scaledPolynomial N θ).degree = N := by
  unfold scaledPolynomial
  rw [degree_C_mul, unscaledPolynomial_degree N θ hN]
  exact pow_ne_zero (N - 1) two_ne_zero

/-- Helper lemma: the unscaled polynomial is monic (leading coefficient is 1). -/
theorem unscaledPolynomial_monic (N : ℕ) (θ : ℝ) :
    (unscaledPolynomial N θ).leadingCoeff = 1 := by
  unfold unscaledPolynomial polynomialFromRealRoots
  induction (realProjectionsList N θ) with
  | nil => simp [List.foldr]
  | cons r rs ih =>
    simp only [List.foldr]
    rw [leadingCoeff_mul, leadingCoeff_X_sub_C, ih, mul_one]

/-- The leading coefficient of the scaled polynomial. -/
theorem scaledPolynomial_leadingCoeff (N : ℕ) (θ : ℝ) (hN : 0 < N) :
    (scaledPolynomial N θ).leadingCoeff = 2 ^ (N - 1) := by
  unfold scaledPolynomial
  rw [leadingCoeff_mul, leadingCoeff_C, unscaledPolynomial_monic, mul_one]

/-- Extract the coefficient of X^k from the scaled polynomial. -/
def scaledPolynomial_coeff (N : ℕ) (θ : ℝ) (k : ℕ) : ℝ :=
  (scaledPolynomial N θ).coeff k

/-- The constant term (coefficient of X^0) of the scaled polynomial depends on θ. -/
theorem scaledPolynomial_constantTerm_varies (N : ℕ) :
    ∃ θ₁ θ₂ : ℝ, scaledPolynomial_coeff N θ₁ 0 ≠ scaledPolynomial_coeff N θ₂ 0 := by
  -- We show that the constant terms for θ = 0 and θ = π differ when N is odd and ≥ 3
  -- The key insight: cos(π + x) = -cos(x), so for θ = π, each root is negated
  -- For N odd, the product of N roots changes sign: (-1)^N = -1
  -- For N even, we need a different approach (or different angles)
  --
  -- Since the original statement didn't specify N, we use the simplest case:
  -- For any N ≥ 1, we can find two angles that give different constant terms.
  use 0, Real.pi / 2
  unfold scaledPolynomial_coeff scaledPolynomial unscaledPolynomial polynomialFromRealRoots
  -- The detailed calculation requires expanding the product structure
  -- and showing that the lists of roots differ in a way that affects the constant term
  sorry

end

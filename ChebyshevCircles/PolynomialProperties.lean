/-
Copyright (c) 2025 Eric. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric
-/
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev
import Mathlib.RingTheory.Polynomial.Vieta
import ChebyshevCircles.PolynomialConstruction
import ChebyshevCircles.RootsOfUnity
import ChebyshevCircles.TrigonometricIdentities
import ChebyshevCircles.NewtonIdentities

/-!
# Polynomial Properties and Coefficient Invariance

Lemmas about degree, evaluation, and coefficient structure of both the scaledPolynomial
and Chebyshev polynomials. The key result is that non-constant coefficients are φ-invariant.

## Main results

* `constant_term_only_varies`: The constant term is the only coefficient that varies with φ
* `chebyshev_T_degree`: The Chebyshev polynomial T_N has degree N for N ≥ 1
* `scaledPolynomial_degree_eq_chebyshev`: Scaled polynomial has same degree as Chebyshev

## Tags

polynomial coefficients, Chebyshev polynomials, Vieta's formulas
-/

noncomputable section

open Polynomial Real Complex
open scoped Polynomial

section PolynomialProperties

/-- The constant term is the only coefficient that varies with φ. -/
theorem constant_term_only_varies (N : ℕ) (φ₁ φ₂ : ℝ) (k : ℕ) (hN : 0 < N)
    (hk : 0 < k) : (scaledPolynomial N φ₁).coeff k = (scaledPolynomial N φ₂).coeff k := by
  unfold scaledPolynomial unscaledPolynomial polynomialFromRealRoots
  simp only [coeff_C_mul]
  congr 1
  -- Convert to multiset form
  rw [list_foldr_eq_multiset_prod, list_foldr_eq_multiset_prod]
  -- Factor out the card lemma
  have h_card (φ : ℝ) : ((realProjectionsList N φ : Multiset ℝ)).card = N := by
    rw [Multiset.coe_card, card_realProjectionsList]
  -- Split cases
  by_cases hk_le : k ≤ N
  · -- k ≤ N: use Vieta's formula
    rw [Multiset.prod_X_sub_C_coeff (realProjectionsList N φ₁ : Multiset ℝ) (by rwa [h_card]),
        Multiset.prod_X_sub_C_coeff (realProjectionsList N φ₂ : Multiset ℝ) (by rwa [h_card])]
    congr 1
    · rw [h_card, h_card]
    · by_cases hk_eq : k = N
      · rw [hk_eq, h_card, h_card]; norm_num [Multiset.esymm, Multiset.powersetCard_zero_left]
      · rw [h_card, h_card]
        exact esymm_rotated_roots_invariant N (N - k) φ₁ φ₂ hN (by omega) (by omega)
  · -- k > N: both coefficients are 0
    have deg (φ : ℝ) : (Multiset.map (fun r => X - C r)
        (realProjectionsList N φ : Multiset ℝ)).prod.natDegree = N := by
      rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, h_card]
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt, Polynomial.coeff_eq_zero_of_natDegree_lt]
    · rw [deg]; omega
    · rw [deg]; omega

/-- The Chebyshev polynomial T_N has degree N for N ≥ 1. -/
lemma chebyshev_T_degree (N : ℕ) (hN : 0 < N) :
    (Polynomial.Chebyshev.T ℝ N).degree = N := by
  induction N using Nat.strong_induction_on with
  | h n IH =>
    cases n with
    | zero => omega
    | succ n' =>
      cases n' with
      | zero => norm_num
      | succ m =>
        have h_rec : Chebyshev.T ℝ (↑(m + 2) : ℤ) =
            2 * X * Chebyshev.T ℝ (↑(m + 1) : ℤ) - Chebyshev.T ℝ (↑m : ℤ) := by
          have := Polynomial.Chebyshev.T_add_two ℝ (↑m : ℤ)
          convert this using 2
        simp only [] at *
        rw [h_rec]
        have IH_m1 : (Chebyshev.T ℝ ↑(m + 1)).degree = ↑(m + 1) := by
          apply IH (m + 1) <;> omega
        have h_deg_prod : (2 * X * Chebyshev.T ℝ ↑(m + 1)).degree = ↑(m + 2) := by
          have h_rearrange : (2 : ℝ[X]) * X * Chebyshev.T ℝ ↑(m + 1) =
              2 * (X * Chebyshev.T ℝ ↑(m + 1)) := by ring
          rw [h_rearrange]
          simp only [Polynomial.degree_mul, IH_m1, Polynomial.degree_X]
          have : (2 : ℝ[X]).degree = 0 := Polynomial.degree_C (show (2 : ℝ) ≠ 0 by norm_num)
          simp [this]; ring
        have h_deg_smaller : (Chebyshev.T ℝ ↑m).degree <
            (2 * X * Chebyshev.T ℝ ↑(m + 1)).degree := by
          rw [h_deg_prod]
          by_cases hm : m = 0
          · simp [hm]
          · have IH_m : (Chebyshev.T ℝ ↑m).degree = ↑m := by apply IH m <;> omega
            rw [IH_m]; norm_cast; omega
        rw [Polynomial.degree_sub_eq_left_of_degree_lt h_deg_smaller, h_deg_prod]

/-- The scaled polynomial has the same degree as the Chebyshev polynomial. -/
lemma scaledPolynomial_degree_eq_chebyshev (N : ℕ) (φ : ℝ) (hN : 0 < N) :
    (scaledPolynomial N φ).degree = (Polynomial.Chebyshev.T ℝ N).degree := by
  rw [chebyshev_T_degree N hN]
  exact scaledPolynomial_degree N φ hN

/-- Evaluating the unscaled polynomial at a projected root gives zero. -/
lemma unscaledPolynomial_eval_at_projection (N : ℕ) (φ : ℝ) (k : ℕ) (hk : k < N) :
    (unscaledPolynomial N φ).eval (Real.cos (φ + 2 * π * k / N)) = 0 := by
  unfold unscaledPolynomial
  apply polynomialFromRealRoots_eval_mem
  exact realProjection_mem_list N φ k hk

/-- Evaluating the scaled polynomial at a projected root gives zero. -/
lemma scaledPolynomial_eval_at_projection (N : ℕ) (φ : ℝ) (k : ℕ) (hk : k < N) :
    (scaledPolynomial N φ).eval (Real.cos (φ + 2 * π * k / N)) = 0 := by
  unfold scaledPolynomial
  rw [eval_mul, unscaledPolynomial_eval_at_projection N φ k hk]
  simp

/-- The Chebyshev polynomial T_N evaluated at cos(φ) equals cos(N·φ). -/
lemma chebyshev_eval_cos (N : ℕ) (φ : ℝ) :
    (Polynomial.Chebyshev.T ℝ N).eval (Real.cos φ) = Real.cos (N * φ) := by
  exact Polynomial.Chebyshev.T_real_cos φ N

end PolynomialProperties

end

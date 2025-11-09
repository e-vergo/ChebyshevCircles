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

set_option linter.style.longLine false

/-!
# Polynomial Properties and Coefficient Invariance

Lemmas about degree, evaluation, and coefficient structure of both the scaledPolynomial
and Chebyshev polynomials. The key result is that non-constant coefficients are θ-invariant.

## Main results

* `constant_term_only_varies`: The constant term is the only coefficient that varies with θ
* `chebyshev_T_degree`: The Chebyshev polynomial T_N has degree N for N ≥ 1
* `scaledPolynomial_degree_eq_chebyshev`: Scaled polynomial has same degree as Chebyshev

## Tags

polynomial coefficients, Chebyshev polynomials, Vieta's formulas
-/

noncomputable section

open Polynomial Real Complex
open scoped Polynomial

section PolynomialProperties

/-- The constant term is the only coefficient that varies with θ. -/
theorem constant_term_only_varies (N : ℕ) (θ₁ θ₂ : ℝ) (k : ℕ) (hN : 0 < N) (hk : 0 < k) :
    (scaledPolynomial N θ₁).coeff k = (scaledPolynomial N θ₂).coeff k := by
  unfold scaledPolynomial
  rw [coeff_C_mul, coeff_C_mul]
  congr 1
  unfold unscaledPolynomial polynomialFromRealRoots
  -- Convert List.foldr to Multiset.prod
  rw [list_foldr_eq_multiset_prod, list_foldr_eq_multiset_prod]
  -- Simplify to use realProjectionsList coerced to multiset
  have h1 : (↑(realProjectionsList N θ₁) : Multiset ℝ) = ↑(realProjectionsList N θ₁) := rfl
  have h2 : (↑(realProjectionsList N θ₂) : Multiset ℝ) = ↑(realProjectionsList N θ₂) := rfl
  -- Case split on whether k ≤ N
  by_cases hk_le : k ≤ N
  · -- When k ≤ N, use Vieta's formula
    rw [Multiset.prod_X_sub_C_coeff]
    · rw [Multiset.prod_X_sub_C_coeff]
      · -- The (-1) power terms are identical, and we need to show esymm are equal
        congr 1
        · -- First goal: (-1) powers are equal (follows from card being N)
          have h_card1 : ((realProjectionsList N θ₁ : Multiset ℝ)).card = N := by
            rw [Multiset.coe_card, card_realProjectionsList]
          have h_card2 : ((realProjectionsList N θ₂ : Multiset ℝ)).card = N := by
            rw [Multiset.coe_card, card_realProjectionsList]
          rw [h_card1, h_card2]
        · -- Second goal: esymm are equal
          -- Handle two subcases: k = N and k < N
          by_cases hk_eq : k = N
          · -- When k = N, esymm 0 = 1 for both sides
            have h_card1 : ((realProjectionsList N θ₁ : Multiset ℝ)).card = N := by
              rw [Multiset.coe_card, card_realProjectionsList]
            have h_card2 : ((realProjectionsList N θ₂ : Multiset ℝ)).card = N := by
              rw [Multiset.coe_card, card_realProjectionsList]
            rw [h_card1, h_card2, hk_eq]
            norm_num [Multiset.esymm, Multiset.powersetCard_zero_left]
          · -- When k < N, apply esymm_rotated_roots_invariant
            have h_card1 : ((realProjectionsList N θ₁ : Multiset ℝ)).card = N := by
              rw [Multiset.coe_card, card_realProjectionsList]
            have h_card2 : ((realProjectionsList N θ₂ : Multiset ℝ)).card = N := by
              rw [Multiset.coe_card, card_realProjectionsList]
            rw [h_card1, h_card2]
            have hk_lt : k < N := Nat.lt_of_le_of_ne hk_le hk_eq
            exact esymm_rotated_roots_invariant N (N - k) θ₁ θ₂ hN (by omega) (by omega)
      · rw [Multiset.coe_card, card_realProjectionsList]; exact hk_le
    · rw [Multiset.coe_card, card_realProjectionsList]
      exact hk_le
  · -- When k > N, both coefficients are 0 (natDegree is N)
    have deg1 : (Multiset.map (fun r => X - C r) (realProjectionsList N θ₁ : Multiset ℝ)).prod.natDegree = N := by
      rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, Multiset.coe_card, card_realProjectionsList]
    have deg2 : (Multiset.map (fun r => X - C r) (realProjectionsList N θ₂ : Multiset ℝ)).prod.natDegree = N := by
      rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, Multiset.coe_card, card_realProjectionsList]
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt, Polynomial.coeff_eq_zero_of_natDegree_lt]
    · rw [deg2]; omega
    · rw [deg1]; omega

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
lemma scaledPolynomial_degree_eq_chebyshev (N : ℕ) (θ : ℝ) (hN : 0 < N) :
    (scaledPolynomial N θ).degree = (Polynomial.Chebyshev.T ℝ N).degree := by
  rw [chebyshev_T_degree N hN]
  exact scaledPolynomial_degree N θ hN

/-- Evaluating the unscaled polynomial at a projected root gives zero. -/
lemma unscaledPolynomial_eval_at_projection (N : ℕ) (θ : ℝ) (k : ℕ) (hk : k < N) :
    (unscaledPolynomial N θ).eval (Real.cos (θ + 2 * π * k / N)) = 0 := by
  unfold unscaledPolynomial
  apply polynomialFromRealRoots_eval_mem
  exact realProjection_mem_list N θ k hk

/-- Evaluating the scaled polynomial at a projected root gives zero. -/
lemma scaledPolynomial_eval_at_projection (N : ℕ) (θ : ℝ) (k : ℕ) (hk : k < N) :
    (scaledPolynomial N θ).eval (Real.cos (θ + 2 * π * k / N)) = 0 := by
  unfold scaledPolynomial
  rw [eval_mul, unscaledPolynomial_eval_at_projection N θ k hk]
  simp

/-- The Chebyshev polynomial T_N evaluated at cos(φ) equals cos(N·φ). -/
lemma chebyshev_eval_cos (N : ℕ) (φ : ℝ) :
    (Polynomial.Chebyshev.T ℝ N).eval (Real.cos φ) = Real.cos (N * φ) := by
  exact Polynomial.Chebyshev.T_real_cos φ N

end PolynomialProperties

end

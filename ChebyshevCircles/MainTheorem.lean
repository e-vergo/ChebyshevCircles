/-
Copyright (c) 2025 Eric. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric
-/
import Mathlib.Algebra.BigOperators.Field
import ChebyshevCircles.PolynomialConstruction
import ChebyshevCircles.RootsOfUnity
import ChebyshevCircles.TrigonometricIdentities
import ChebyshevCircles.ChebyshevRoots
import ChebyshevCircles.PowerSums
import ChebyshevCircles.NewtonIdentities
import ChebyshevCircles.PolynomialProperties
import ChebyshevCircles.PowerSumEquality

/-!
# Main Theorem: Rotated Roots Yield Chebyshev Polynomials

This module contains the main theorem proving that rotated N-th roots of unity,
when projected onto the real axis and used as polynomial roots (scaled by 2^(N-1)),
yield the N-th Chebyshev polynomial of the first kind plus a constant.

## Key Results
- `rotated_roots_yield_chebyshev`: Main theorem statement
- `rotated_roots_coeffs_match_chebyshev`: Coefficient-level result
- `constant_term_only_varies`: Only constant term depends on rotation angle

## References
- [Blueprint §1](https://e-vergo.github.io/ChebyshevCircles/blueprint/sect0001.html) - Theorem statement and proof structure
- [Research Paper](https://e-vergo.github.io/ChebyshevCircles/paper/chebyshev_circles.pdf) - Theorem 1.1 (page 2)
- [Source Code](https://github.com/e-vergo/ChebyshevCircles/blob/main/ChebyshevCircles/MainTheorem.lean)

## Tags

Chebyshev polynomials, roots of unity, polynomial coefficients
-/

noncomputable section

open Polynomial Real Complex
open scoped Polynomial

/-! ## Main Theorems

The culminating results connecting rotated roots of unity to Chebyshev polynomials.
Two sorries remain: one trivial ring tactic fix in N=3 case, and the general N≥4 case
which requires deep harmonic analysis to prove power sum equality for Chebyshev roots.
-/

/-- The leading coefficient of Chebyshev T_N is 2^(N-1) for N ≥ 1.

This can be proven by induction using the recurrence T_{n+2} = 2X·T_{n+1} - T_n,
but the proof is tedious and requires careful manipulation of leading coefficients.
The result is standard in the literature on Chebyshev polynomials.
-/
lemma chebyshev_T_leadingCoeff (N : ℕ) (hN : 0 < N) :
    (Polynomial.Chebyshev.T ℝ N).leadingCoeff = 2 ^ (N - 1) := by
  induction N using Nat.strong_induction_on with
  | h n IH =>
    cases n with
    | zero => omega
    | succ n' =>
      cases n' with
      | zero =>
        -- Base case: N = 1, T_1 = X has leading coeff 1 = 2^0
        norm_num [Polynomial.Chebyshev.T_one, Polynomial.leadingCoeff_X]
      | succ m =>
        -- N = m + 2 ≥ 2, use recurrence T_{n+2} = 2X·T_{n+1} - T_n
        have h_rec : Chebyshev.T ℝ (↑(m + 2) : ℤ) =
            2 * X * Chebyshev.T ℝ (↑(m + 1) : ℤ) - Chebyshev.T ℝ (↑m : ℤ) := by
          have := Polynomial.Chebyshev.T_add_two ℝ (↑m : ℤ)
          convert this using 2

        -- Apply IH to get leadingCoeff of T_{m+1}
        have IH_m1 : (Chebyshev.T ℝ ↑(m + 1)).leadingCoeff = 2 ^ m := by
          have h := IH (m + 1) (by omega : m + 1 < m + 2) (by omega : 0 < m + 1)
          simp only [Nat.add_sub_cancel] at h
          exact h

        -- Show degree(T_m) < degree(2*X*T_{m+1})
        have deg_T_m1 : (Chebyshev.T ℝ ↑(m + 1)).degree = ↑(m + 1) := by
          apply chebyshev_T_degree (m + 1)
          omega

        have deg_prod : (2 * X * Chebyshev.T ℝ ↑(m + 1)).degree = ↑(m + 2) := by
          have h_rearrange : (2 : ℝ[X]) * X * Chebyshev.T ℝ ↑(m + 1) =
              2 * (X * Chebyshev.T ℝ ↑(m + 1)) := by ring
          rw [h_rearrange]
          simp only [Polynomial.degree_mul, deg_T_m1, Polynomial.degree_X]
          have : (2 : ℝ[X]).degree = 0 := Polynomial.degree_C (show (2 : ℝ) ≠ 0 by norm_num)
          simp [this]; ring

        have deg_T_m :
            (Chebyshev.T ℝ ↑m).degree < (2 * X * Chebyshev.T ℝ ↑(m + 1)).degree := by
          rw [deg_prod]
          by_cases hm : m = 0
          · simp [hm]
          · have deg_m : (Chebyshev.T ℝ ↑m).degree = ↑m := by
              apply chebyshev_T_degree m
              omega
            rw [deg_m]
            norm_cast
            omega

        -- Apply leadingCoeff_sub_of_degree_lt
        have lc_rec : (2 * X * Chebyshev.T ℝ ↑(m + 1) - Chebyshev.T ℝ ↑m).leadingCoeff =
            (2 * X * Chebyshev.T ℝ ↑(m + 1)).leadingCoeff := by
          apply Polynomial.leadingCoeff_sub_of_degree_lt deg_T_m

        -- Calculate leadingCoeff(2*X*T_{m+1})
        have lc_prod : (2 * X * Chebyshev.T ℝ ↑(m + 1)).leadingCoeff = 2 * 2 ^ m := by
          have h_two : (2 : ℝ[X]) = C (2 : ℝ) := by rfl
          conv_lhs => rw [h_two]
          rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_mul,
              Polynomial.leadingCoeff_C, Polynomial.leadingCoeff_X, IH_m1]
          ring

        -- Finish the proof
        simp only [Nat.add_sub_cancel]
        calc (Chebyshev.T ℝ ↑(m + 2)).leadingCoeff
            = (2 * X * Chebyshev.T ℝ ↑(m + 1) -
                Chebyshev.T ℝ ↑m).leadingCoeff := by rw [← h_rec]
          _ = (2 * X * Chebyshev.T ℝ ↑(m + 1)).leadingCoeff := lc_rec
          _ = 2 * 2 ^ m := lc_prod
          _ = 2 ^ (m + 1) := by ring

private lemma scaledPolynomial_matches_chebyshev_N_eq_1 (k : ℕ) (hk : 0 < k) :
    (scaledPolynomial 1 0).coeff k = (Polynomial.Chebyshev.T ℝ 1).coeff k := by
  by_cases hk_eq : k = 1
  · rw [hk_eq]
    have h_cheb : (Chebyshev.T ℝ 1).coeff 1 = 1 := by
      rw [show (Chebyshev.T ℝ 1) = X by simp [Chebyshev.T_one]]; simp
    have h_scaled : (scaledPolynomial 1 0).coeff 1 = 1 := by
      have deg : (scaledPolynomial 1 0).degree = 1 := scaledPolynomial_degree 1 0 (by omega)
      have lc : (scaledPolynomial 1 0).leadingCoeff = 1 := by
        rw [scaledPolynomial_leadingCoeff]; norm_num
      have deg_nat : (scaledPolynomial 1 0).natDegree = 1 := by
        rw [← Polynomial.degree_eq_iff_natDegree_eq_of_pos (by omega : 0 < 1)]; exact deg
      rw [Polynomial.leadingCoeff, deg_nat] at lc; exact lc
    rw [h_scaled, h_cheb]
  · have deg_cheb : (Chebyshev.T ℝ 1).natDegree = 1 := by
      simp [Chebyshev.T_one, Polynomial.natDegree_X]
    have deg_scaled : (scaledPolynomial 1 0).natDegree = 1 := by
      have deg : (scaledPolynomial 1 0).degree = 1 := scaledPolynomial_degree 1 0 (by omega)
      rw [← Polynomial.degree_eq_iff_natDegree_eq_of_pos (by omega : 0 < 1)]; exact deg
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt, Polynomial.coeff_eq_zero_of_natDegree_lt]
    · rw [deg_cheb]; omega
    · rw [deg_scaled]; omega

private lemma scaledPolynomial_matches_chebyshev_N_eq_2 (k : ℕ) (hk : 0 < k) :
    (scaledPolynomial 2 0).coeff k = (Polynomial.Chebyshev.T ℝ 2).coeff k := by
  by_cases hk_eq : k = 1
  · rw [hk_eq]
    have h_cheb : (Chebyshev.T ℝ 2).coeff 1 = 0 := by
      rw [show (Chebyshev.T ℝ 2) = Chebyshev.T ℝ (2 : ℤ) by norm_num, Chebyshev.T_two]
      simp only [Polynomial.coeff_sub, Polynomial.coeff_one]
      rw [show (2 : ℝ[X]) = Polynomial.C 2 by rfl]
      simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
    have h_scaled : (scaledPolynomial 2 0).coeff 1 = 0 := by
      unfold scaledPolynomial unscaledPolynomial
      rw [Polynomial.coeff_C_mul]
      have roots_eq : realProjectionsList 2 0 = [1, -1] := by
        unfold realProjectionsList
        simp only [List.range]
        conv_lhs => arg 2; rw [show List.range.loop 2 [] = [0, 1] by rfl]
        simp only [List.map]; norm_num [Real.cos_zero, Real.cos_pi]
      rw [roots_eq]; unfold polynomialFromRealRoots
      simp only [List.foldr]
      rw [mul_one, show C (-1 : ℝ) = -C 1 by simp [Polynomial.C_neg], sub_neg_eq_add]
      norm_num
      have eq1 : (X - (1:ℝ[X])) * (X + 1) = X^2 - 1 := by ring
      rw [eq1]; simp [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_one]
    rw [h_scaled, h_cheb]
  · by_cases hk_eq2 : k = 2
    · rw [hk_eq2]
      have h_cheb : (Chebyshev.T ℝ 2).coeff 2 = 2 := by
        rw [show (Chebyshev.T ℝ 2) = Chebyshev.T ℝ (2 : ℤ) by norm_num, Chebyshev.T_two]
        simp only [Polynomial.coeff_sub, Polynomial.coeff_one]
        rw [show (2 : ℝ[X]) = Polynomial.C 2 by rfl]
        simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      have h_scaled : (scaledPolynomial 2 0).coeff 2 = 2 := by
        have deg : (scaledPolynomial 2 0).degree = 2 := scaledPolynomial_degree 2 0 (by omega)
        have lc : (scaledPolynomial 2 0).leadingCoeff = 2 := by
          rw [scaledPolynomial_leadingCoeff]; norm_num
        have deg_nat : (scaledPolynomial 2 0).natDegree = 2 := by
          rw [← Polynomial.degree_eq_iff_natDegree_eq_of_pos (by omega : 0 < 2)]; exact deg
        rw [Polynomial.leadingCoeff, deg_nat] at lc; exact lc
      rw [h_scaled, h_cheb]
    · have deg_cheb : (Chebyshev.T ℝ 2).natDegree = 2 := by
        have deg : (Chebyshev.T ℝ 2).degree = 2 := chebyshev_T_degree 2 (by omega)
        rw [← Polynomial.degree_eq_iff_natDegree_eq_of_pos (by omega : 0 < 2)]; exact deg
      have deg_scaled : (scaledPolynomial 2 0).natDegree = 2 := by
        have deg : (scaledPolynomial 2 0).degree = 2 := scaledPolynomial_degree 2 0 (by omega)
        rw [← Polynomial.degree_eq_iff_natDegree_eq_of_pos (by omega : 0 < 2)]; exact deg
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt, Polynomial.coeff_eq_zero_of_natDegree_lt]
      · rw [deg_cheb]; omega
      · rw [deg_scaled]; omega

private lemma scaledPolynomial_matches_chebyshev_N_eq_3 (k : ℕ) (hk : 0 < k) :
    (scaledPolynomial 3 0).coeff k = (Polynomial.Chebyshev.T ℝ 3).coeff k := by
  by_cases hk_eq : k = 1
  · rw [hk_eq]
    have h_cheb : (Chebyshev.T ℝ 3).coeff 1 = -3 := by
      have h_eq : Polynomial.Chebyshev.T ℝ (3 : ℤ) =
          2 * X * (Polynomial.Chebyshev.T ℝ 2) - Polynomial.Chebyshev.T ℝ 1 := by
        have := Polynomial.Chebyshev.T_add_two ℝ (1 : ℤ); exact this
      rw [show (Chebyshev.T ℝ 3) = Chebyshev.T ℝ (3 : ℤ) by norm_num]
      rw [h_eq, Polynomial.Chebyshev.T_two, Polynomial.Chebyshev.T_one]
      have : (2 * X * (2 * X ^ 2 - 1) - X : ℝ[X]) = 4 * X ^ 3 - 3 * X := by ring
      rw [this]; norm_num [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_X]
    have h_scaled : (scaledPolynomial 3 0).coeff 1 = -3 := by
      unfold scaledPolynomial unscaledPolynomial
      have roots_eq : realProjectionsList 3 0 = [1, -1/2, -1/2] := by
        unfold realProjectionsList
        simp only [List.range]
        conv_lhs => arg 2; rw [show List.range.loop 3 [] = [0, 1, 2] by rfl]
        simp only [List.map, zero_add]; norm_num [Real.cos_zero]
        constructor
        · have h2 : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by field_simp; ring
          rw [h2, Real.cos_pi_sub]; norm_num
        · have h1 : 2 * Real.pi * 2 / 3 = 4 * Real.pi / 3 := by ring
          rw [h1]
          have h2 : 4 * Real.pi / 3 = Real.pi + Real.pi / 3 := by field_simp; ring
          rw [h2, show Real.pi + Real.pi / 3 = Real.pi / 3 + Real.pi by ring, Real.cos_add_pi]
          norm_num
      rw [roots_eq]; unfold polynomialFromRealRoots
      simp only [List.foldr, mul_one]
      conv_lhs => arg 1; arg 2; rw [show ((X : ℝ[X]) - C 1) *
          ((X - C (-1/2)) * (X - C (-1/2))) =
            ([(1 : ℝ), -1/2, -1/2].map (fun r => X - C r)).prod from by
              simp only [List.map, List.prod_cons, List.prod_nil, mul_one]]
      rw [Polynomial.coeff_C_mul]
      rw [show ([(1 : ℝ), -1/2, -1/2].map (fun r => X - C r)).prod =
               (([(1 : ℝ), -1/2, -1/2] : Multiset ℝ).map (fun r => X - C r)).prod by
                 rw [Multiset.map_coe]; rfl]
      rw [Multiset.prod_X_sub_C_coeff]
      · simp only [Multiset.coe_card, List.length_cons, List.length_nil]
        norm_num [Multiset.esymm, Multiset.powersetCard]
      · simp only [Multiset.coe_card, List.length_cons, List.length_nil]; omega
    rw [h_scaled, h_cheb]
  · by_cases hk_eq2 : k = 2
    · rw [hk_eq2]
      have h_cheb : (Chebyshev.T ℝ 3).coeff 2 = 0 := by
        have h_eq : Polynomial.Chebyshev.T ℝ (3 : ℤ) =
          2 * X * (Polynomial.Chebyshev.T ℝ 2) - Polynomial.Chebyshev.T ℝ 1 := by
          have := Polynomial.Chebyshev.T_add_two ℝ (1 : ℤ); exact this
        rw [show (Chebyshev.T ℝ 3) = Chebyshev.T ℝ (3 : ℤ) by norm_num]
        rw [h_eq, Polynomial.Chebyshev.T_two, Polynomial.Chebyshev.T_one]
        have : (2 * X * (2 * X ^ 2 - 1) - X : ℝ[X]) = 4 * X ^ 3 - 3 * X := by ring
        rw [this]; norm_num [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_X]
      have h_scaled : (scaledPolynomial 3 0).coeff 2 = 0 := by
        unfold scaledPolynomial unscaledPolynomial
        have roots_eq : realProjectionsList 3 0 = [1, -1/2, -1/2] := by
          unfold realProjectionsList
          simp only [List.range]
          conv_lhs => arg 2; rw [show List.range.loop 3 [] = [0, 1, 2] by rfl]
          simp only [List.map, zero_add]; norm_num [Real.cos_zero]
          constructor
          · have h2 : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by field_simp; ring
            rw [h2, Real.cos_pi_sub]; norm_num
          · have h1 : 2 * Real.pi * 2 / 3 = 4 * Real.pi / 3 := by ring
            rw [h1]
            have h2 : 4 * Real.pi / 3 = Real.pi + Real.pi / 3 := by field_simp; ring
            rw [h2, show Real.pi + Real.pi / 3 = Real.pi / 3 + Real.pi by ring, Real.cos_add_pi]
            norm_num
        rw [roots_eq]; unfold polynomialFromRealRoots
        simp only [List.foldr, mul_one]
        conv_lhs => arg 1; arg 2; rw [show ((X : ℝ[X]) - C 1) *
            ((X - C (-1/2)) * (X - C (-1/2))) =
              ([(1 : ℝ), -1/2, -1/2].map (fun r => X - C r)).prod from by
                simp only [List.map, List.prod_cons, List.prod_nil, mul_one]]
        rw [Polynomial.coeff_C_mul]
        rw [show ([(1 : ℝ), -1/2, -1/2].map (fun r => X - C r)).prod =
                 (([(1 : ℝ), -1/2, -1/2] : Multiset ℝ).map (fun r => X - C r)).prod by
                   rw [Multiset.map_coe]; rfl]
        rw [Multiset.prod_X_sub_C_coeff]
        · simp only [Multiset.coe_card, List.length_cons, List.length_nil]
          norm_num [Multiset.esymm, Multiset.powersetCard]
        · simp only [Multiset.coe_card, List.length_cons, List.length_nil]; omega
      rw [h_scaled, h_cheb]
    · by_cases hk_eq3 : k = 3
      · rw [hk_eq3]
        have h_cheb : (Chebyshev.T ℝ 3).coeff 3 = 4 := by
          have h_eq : Polynomial.Chebyshev.T ℝ (3 : ℤ) =
          2 * X * (Polynomial.Chebyshev.T ℝ 2) - Polynomial.Chebyshev.T ℝ 1 := by
            have := Polynomial.Chebyshev.T_add_two ℝ (1 : ℤ); exact this
          rw [show (Chebyshev.T ℝ 3) = Chebyshev.T ℝ (3 : ℤ) by norm_num]
          rw [h_eq, Polynomial.Chebyshev.T_two, Polynomial.Chebyshev.T_one]
          have : (2 * X * (2 * X ^ 2 - 1) - X : ℝ[X]) = 4 * X ^ 3 - 3 * X := by ring
          rw [this]; norm_num [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_X]
        have h_scaled : (scaledPolynomial 3 0).coeff 3 = 4 := by
          have deg : (scaledPolynomial 3 0).degree = 3 := scaledPolynomial_degree 3 0 (by omega)
          have lc : (scaledPolynomial 3 0).leadingCoeff = 4 := by
            rw [scaledPolynomial_leadingCoeff]; norm_num
          have deg_nat : (scaledPolynomial 3 0).natDegree = 3 := by
            rw [← Polynomial.degree_eq_iff_natDegree_eq_of_pos (by omega : 0 < 3)]; exact deg
          rw [Polynomial.leadingCoeff, deg_nat] at lc; exact lc
        rw [h_scaled, h_cheb]
      · have deg_cheb : (Chebyshev.T ℝ 3).natDegree = 3 := by
          have deg : (Chebyshev.T ℝ 3).degree = 3 := chebyshev_T_degree 3 (by omega)
          rw [← Polynomial.degree_eq_iff_natDegree_eq_of_pos (by omega : 0 < 3)]; exact deg
        have deg_scaled : (scaledPolynomial 3 0).natDegree = 3 := by
          have deg : (scaledPolynomial 3 0).degree = 3 := scaledPolynomial_degree 3 0 (by omega)
          rw [← Polynomial.degree_eq_iff_natDegree_eq_of_pos (by omega : 0 < 3)]; exact deg
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt, Polynomial.coeff_eq_zero_of_natDegree_lt]
        · rw [deg_cheb]; omega
        · rw [deg_scaled]; omega

private lemma scaledPolynomial_matches_chebyshev_N_ge_4
    (N : ℕ) (k : ℕ) (hN : 4 ≤ N) (hk : 0 < k) :
    (scaledPolynomial N 0).coeff k = (Polynomial.Chebyshev.T ℝ N).coeff k := by
  let rotated_roots : Multiset ℝ := ↑(realProjectionsList N 0)
  let cheb_roots : Multiset ℝ := ↑(chebyshevRootsList N)

  have h_card_rot : rotated_roots.card = N := by rw [Multiset.coe_card, card_realProjectionsList]
  have h_card_cheb : cheb_roots.card = N := by
    unfold cheb_roots chebyshevRootsList; rw [Multiset.coe_card, List.length_ofFn]

  have h_psum : ∀ j, 0 < j → j < N →
      (rotated_roots.map (· ^ j)).sum = (cheb_roots.map (· ^ j)).sum := by
    intro j hj hjN
    rw [multiset_powersum_realProjectionsList N 0 j]
    unfold cheb_roots chebyshevRootsList
    rw [Multiset.map_coe, Multiset.sum_coe]
    simp only [List.sum_ofFn, List.map_ofFn, Function.comp, zero_add, chebyshevRoot]
    have h_convert : (∑ x : Fin N, Real.cos ((2 * ↑↑x + 1) * π / (2 * ↑N)) ^ j) =
        (∑ k ∈ Finset.range N, Real.cos ((2 * ↑k + 1) * π / (2 * ↑N)) ^ j) := by
      exact Fin.sum_univ_eq_sum_range (fun k => Real.cos ((2 * k + 1) * π / (2 * N)) ^ j) N
    rw [h_convert]; exact general_powersum_equality N j (by omega) hj hjN

  have h_esymm : ∀ m, m < rotated_roots.card → rotated_roots.esymm m = cheb_roots.esymm m := by
    apply esymm_eq_of_psum_eq rotated_roots cheb_roots
    · rw [h_card_rot, h_card_cheb]
    · intro j hj hjN; exact h_psum j hj (by rwa [← h_card_rot])

  have h_coeff_eq : ∀ (k' : ℕ), 0 < k' → k' ≤ N →
      (C (2^(N - 1)) * (rotated_roots.map (fun r => X - C r)).prod).coeff k' =
      (C (2^(N - 1)) * (cheb_roots.map (fun r => X - C r)).prod).coeff k' := by
    intro k' hk' hk'_le
    apply polynomial_coeff_eq_of_esymm_eq rotated_roots cheb_roots (2^(N - 1))
    · norm_num
    · exact h_esymm
    · rw [h_card_rot, h_card_cheb]
    · exact hk'
    · show k' ≤ rotated_roots.card; rw [h_card_rot]; exact hk'_le

  have h_scaled_eq : scaledPolynomial N 0 =
      C (2^(N - 1)) * (rotated_roots.map (fun r => X - C r)).prod := by
    unfold scaledPolynomial unscaledPolynomial polynomialFromRealRoots rotated_roots
    rw [list_foldr_eq_multiset_prod]

  have h_cheb_eq : Chebyshev.T ℝ N =
      C (2^(N - 1)) * (cheb_roots.map (fun r => X - C r)).prod := by
    have hN_pos : 0 < N := by omega
    have h_cheb_roots_subset : ∀ r ∈ cheb_roots, (Chebyshev.T ℝ N).eval r = 0 := by
      intro r hr
      unfold cheb_roots chebyshevRootsList at hr
      rw [Multiset.mem_coe] at hr
      simp only [List.mem_ofFn] at hr
      obtain ⟨k, rfl⟩ := hr
      exact chebyshev_T_eval_chebyshevRoot N k.val hN_pos k.isLt
    have h_cheb_roots_nodup : cheb_roots.Nodup := by
      unfold cheb_roots chebyshevRootsList
      rw [Multiset.coe_nodup, List.nodup_ofFn]
      intro i j hij
      exact Fin.ext (chebyshevRoots_distinct N hN_pos i.val j.val i.isLt j.isLt hij)
    have h_deg : (Chebyshev.T ℝ N).natDegree = N := by
      have : (Chebyshev.T ℝ N).degree = N := chebyshev_T_degree N hN_pos
      rw [← Polynomial.degree_eq_iff_natDegree_eq_of_pos (by omega : 0 < N)]; exact this
    have h_card_le : (Chebyshev.T ℝ N).roots.card ≤ (Chebyshev.T ℝ N).natDegree :=
      Polynomial.card_roots' _
    have h_card_ge : N ≤ (Chebyshev.T ℝ N).roots.card := by
      let S := cheb_roots.toFinset
      have hS_card : S.card = N := by
        rw [Multiset.toFinset_card_of_nodup h_cheb_roots_nodup, h_card_cheb]
      have hS_subset : S.val ⊆ (Chebyshev.T ℝ N).roots := by
        intro r hr
        have : r ∈ cheb_roots := Multiset.mem_toFinset.mp hr
        have eval_zero := h_cheb_roots_subset r this
        apply Polynomial.mem_roots'.mpr
        constructor
        · intro h_zero
          have : (Chebyshev.T ℝ N).degree = N := chebyshev_T_degree N hN_pos
          rw [h_zero] at this; simp at this
        · exact eval_zero
      calc N = S.card := hS_card.symm
        _ ≤ (Chebyshev.T ℝ N).natDegree := Polynomial.card_le_degree_of_subset_roots hS_subset
        _ = (Chebyshev.T ℝ N).roots.card := by
            have : S.card ≤ (Chebyshev.T ℝ N).natDegree :=
              Polynomial.card_le_degree_of_subset_roots hS_subset
            have h1 : (Chebyshev.T ℝ N).natDegree = N := h_deg
            have h2 : S.card = N := hS_card
            have h3 : (Chebyshev.T ℝ N).roots.card ≤ (Chebyshev.T ℝ N).natDegree := h_card_le
            have hS_le : S.val ≤ (Chebyshev.T ℝ N).roots :=
              (Multiset.le_iff_subset S.nodup).mpr hS_subset
            have h4 : S.card ≤ (Chebyshev.T ℝ N).roots.card := Multiset.card_le_card hS_le
            have h_le1 : (Chebyshev.T ℝ N).natDegree ≤ (Chebyshev.T ℝ N).roots.card := by
              calc (Chebyshev.T ℝ N).natDegree = N := h1
                _ = S.card := h2.symm
                _ ≤ (Chebyshev.T ℝ N).roots.card := h4
            have h_le2 : (Chebyshev.T ℝ N).roots.card ≤ (Chebyshev.T ℝ N).natDegree := h3
            exact Nat.le_antisymm h_le1 h_le2
    have h_card_eq : (Chebyshev.T ℝ N).roots.card = (Chebyshev.T ℝ N).natDegree := by
      rw [h_deg] at h_card_le; omega
    have h_leading : (Chebyshev.T ℝ N).leadingCoeff = 2 ^ (N - 1) :=
      chebyshev_T_leadingCoeff N hN_pos
    conv_rhs => rw [← h_leading]
    have h_roots_eq : cheb_roots = (Chebyshev.T ℝ N).roots := by
      refine Multiset.eq_of_le_of_card_le ?_ ?_
      · apply Multiset.le_iff_count.mpr
        intro a
        by_cases ha : a ∈ cheb_roots
        · have ha_root : a ∈ (Chebyshev.T ℝ N).roots := by
            have eval_zero := h_cheb_roots_subset a ha
            apply Polynomial.mem_roots'.mpr
            constructor
            · intro h_zero
              have : (Chebyshev.T ℝ N).degree = N := chebyshev_T_degree N hN_pos
              rw [h_zero] at this; simp at this
            · exact eval_zero
          rw [Multiset.count_eq_one_of_mem h_cheb_roots_nodup ha]
          exact Nat.one_le_iff_ne_zero.mpr (Multiset.count_ne_zero.mpr ha_root)
        · rw [Multiset.count_eq_zero.mpr ha]; exact Nat.zero_le _
      · rw [h_card_cheb, h_card_eq, h_deg]
    rw [h_roots_eq]; exact (Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C h_card_eq).symm

  by_cases hk_le : k ≤ N
  · calc (scaledPolynomial N 0).coeff k
        = (C (2^(N - 1)) *
            (rotated_roots.map (fun r => X - C r)).prod).coeff k := by rw [h_scaled_eq]
      _ = (C (2^(N - 1)) *
            (cheb_roots.map (fun r => X - C r)).prod).coeff k := by
              exact h_coeff_eq k hk hk_le
      _ = (Chebyshev.T ℝ N).coeff k := by rw [← h_cheb_eq]
  · have hk_gt : N < k := by omega
    have deg_scaled : (scaledPolynomial N 0).natDegree = N := by
      have : (scaledPolynomial N 0).degree = N := scaledPolynomial_degree N 0 (by omega)
      rw [← Polynomial.degree_eq_iff_natDegree_eq_of_pos (by omega : 0 < N)]; exact this
    have deg_cheb : (Chebyshev.T ℝ N).natDegree = N := by
      have : (Chebyshev.T ℝ N).degree = N := chebyshev_T_degree N (by omega)
      rw [← Polynomial.degree_eq_iff_natDegree_eq_of_pos (by omega : 0 < N)]; exact this
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt, Polynomial.coeff_eq_zero_of_natDegree_lt]
    · rw [deg_cheb]; exact hk_gt
    · rw [deg_scaled]; exact hk_gt

/-- For θ=0, the scaled polynomial coefficients match Chebyshev for k > 0. -/
theorem scaledPolynomial_matches_chebyshev_at_zero (N : ℕ) (k : ℕ) (hN : 0 < N) (hk : 0 < k) :
    (scaledPolynomial N 0).coeff k = (Polynomial.Chebyshev.T ℝ N).coeff k := by
  match N with
  | 1 => exact scaledPolynomial_matches_chebyshev_N_eq_1 k hk
  | 2 => exact scaledPolynomial_matches_chebyshev_N_eq_2 k hk
  | 3 => exact scaledPolynomial_matches_chebyshev_N_eq_3 k hk
  | n + 4 => exact scaledPolynomial_matches_chebyshev_N_ge_4 (n + 4) k (by omega) hk

/-- The scaled polynomial equals the N-th Chebyshev polynomial plus a θ-dependent constant. -/
theorem rotated_roots_yield_chebyshev (N : ℕ) (θ : ℝ) (hN : 0 < N) :
    ∃ (c : ℝ), scaledPolynomial N θ = Polynomial.Chebyshev.T ℝ N + C c := by
  use (scaledPolynomial N θ).coeff 0 - (Chebyshev.T ℝ N).coeff 0
  ext n
  simp only [coeff_add, coeff_C]
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn]
    have h_pos : 0 < n := Nat.pos_of_ne_zero hn
    calc (scaledPolynomial N θ).coeff n
        = (scaledPolynomial N 0).coeff n := constant_term_only_varies N θ 0 n hN h_pos
      _ = (Chebyshev.T ℝ N).coeff n := scaledPolynomial_matches_chebyshev_at_zero N n hN h_pos

/-- All polynomial coefficients of degree k > 0 match the Chebyshev polynomial. -/
theorem rotated_roots_coeffs_match_chebyshev (N : ℕ) (θ : ℝ) (k : ℕ)
    (hN : 0 < N) (hk : 0 < k) :
    (scaledPolynomial N θ).coeff k = (Polynomial.Chebyshev.T ℝ N).coeff k := by
  obtain ⟨c, h_eq⟩ := rotated_roots_yield_chebyshev N θ hN
  calc (scaledPolynomial N θ).coeff k
      = (Chebyshev.T ℝ N + C c).coeff k := by rw [h_eq]
    _ = (Chebyshev.T ℝ N).coeff k + (C c).coeff k := by rw [coeff_add]
    _ = (Chebyshev.T ℝ N).coeff k + 0 := by
        simp only [coeff_C]
        have : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk
        simp [this]
    _ = (Chebyshev.T ℝ N).coeff k := by ring

end

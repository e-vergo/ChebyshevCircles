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

set_option linter.style.longLine false

/-!
# Main Theorem: Rotated Roots of Unity Yield Chebyshev Polynomials

This file proves that the polynomial constructed from N rotated roots of unity
projected onto the real axis, when scaled by 2^(N-1), equals the N-th Chebyshev
polynomial of the first kind plus a constant that depends on the rotation angle.

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

        have deg_T_m : (Chebyshev.T ℝ ↑m).degree < (2 * X * Chebyshev.T ℝ ↑(m + 1)).degree := by
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
            = (2 * X * Chebyshev.T ℝ ↑(m + 1) - Chebyshev.T ℝ ↑m).leadingCoeff := by rw [← h_rec]
          _ = (2 * X * Chebyshev.T ℝ ↑(m + 1)).leadingCoeff := lc_rec
          _ = 2 * 2 ^ m := lc_prod
          _ = 2 ^ (m + 1) := by ring

/-- For θ=0, the scaled polynomial coefficients match Chebyshev for k > 0. -/
theorem scaledPolynomial_matches_chebyshev_at_zero (N : ℕ) (k : ℕ) (hN : 0 < N) (hk : 0 < k) :
    (scaledPolynomial N 0).coeff k = (Polynomial.Chebyshev.T ℝ N).coeff k := by
  -- For N = 1, 2, prove explicitly to avoid the general case
  cases N with
  | zero => omega
  | succ N' =>
    cases N' with
    | zero =>
      -- N = 1: Both scaledPolynomial 1 0 and Chebyshev.T ℝ 1 have degree 1 and leading coeff 1
      -- Chebyshev T_1 = X, so coeff_1 = 1, coeff_k = 0 for k ≥ 2
      -- scaledPolynomial 1 0 = (X - 1), so coeff_1 = 1, coeff_k = 0 for k ≥ 2
      by_cases hk_eq : k = 1
      · -- k = 1: coeff of X is 1 for both
        rw [hk_eq]
        have h_cheb : (Chebyshev.T ℝ (1 : ℕ)).coeff 1 = 1 := by
          rw [show (Chebyshev.T ℝ (1 : ℕ)) = X by simp [Chebyshev.T_one]]
          simp
        have h_scaled : (scaledPolynomial 1 0).coeff 1 = 1 := by
          -- scaledPolynomial 1 0 has degree 1 and leading coeff 2^0 = 1
          have deg : (scaledPolynomial 1 0).degree = 1 := scaledPolynomial_degree 1 0 (by omega)
          have lc : (scaledPolynomial 1 0).leadingCoeff = 1 := by
            rw [scaledPolynomial_leadingCoeff]; norm_num
          have deg_nat : (scaledPolynomial 1 0).natDegree = 1 := by
            rw [← Polynomial.degree_eq_iff_natDegree_eq_of_pos (by omega : 0 < 1)]
            exact deg
          rw [Polynomial.leadingCoeff, deg_nat] at lc
          exact lc
        rw [h_scaled, h_cheb]
      · -- k ≥ 2: both have degree 1, so coefficients are 0
        have hk_ge : 2 ≤ k := by omega
        have deg_cheb : (Chebyshev.T ℝ (1 : ℕ)).natDegree = 1 := by
          simp [Chebyshev.T_one, Polynomial.natDegree_X]
        have deg_scaled : (scaledPolynomial 1 0).natDegree = 1 := by
          have deg : (scaledPolynomial 1 0).degree = 1 := scaledPolynomial_degree 1 0 (by omega)
          rw [← Polynomial.degree_eq_iff_natDegree_eq_of_pos (by omega : 0 < 1)]
          exact deg
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt, Polynomial.coeff_eq_zero_of_natDegree_lt]
        · rw [deg_cheb]; omega
        · rw [deg_scaled]; omega
    | succ N'' =>
      -- N ≥ 2: Prove N=2 explicitly, then defer general case
      cases N'' with
      | zero =>
        -- N = 2: Prove by direct computation
        -- scaledPolynomial 2 0 = 2(X - 1)(X + 1) = 2X² - 2
        -- Chebyshev T_2 = 2X² - 1
        -- For k > 0: both have matching coefficients (k=1 gives 0, k=2 gives 2)
        by_cases hk_eq : k = 1
        · -- k = 1: both have coefficient 0
          rw [hk_eq]
          -- T_2 = 2X² - 1, so coeff of X is 0
          have h_cheb : (Chebyshev.T ℝ (2 : ℕ)).coeff 1 = 0 := by
            rw [show (2 : ℕ) = (2 : ℤ) by norm_num, Chebyshev.T_two]
            simp only [Polynomial.coeff_sub, Polynomial.coeff_one]
            rw [show (2 : ℝ[X]) = Polynomial.C 2 by rfl]
            simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
          -- scaledPolynomial 2 0 also has coefficient 0 for X
          -- This follows from the leading coefficient being 2, degree being 2
          -- and the polynomial being even (symmetric roots at ±1)
          have h_scaled : (scaledPolynomial 2 0).coeff 1 = 0 := by
            -- For N=2, the roots are cos(0) = 1 and cos(π) = -1
            -- So the polynomial is C·(X-1)(X+1) = C·(X²-1)
            -- With C = 2, we get 2X² - 2, which has coeff 1 = 0
            unfold scaledPolynomial
            rw [Polynomial.coeff_C_mul]
            unfold unscaledPolynomial
            -- Need to show (polynomialFromRealRoots (realProjectionsList 2 0)).coeff 1 = 0
            -- realProjectionsList 2 0 = [cos(0), cos(π)] = [1, -1]
            have roots_eq : realProjectionsList 2 0 = [1, -1] := by
              unfold realProjectionsList
              simp only [List.range]
              conv_lhs =>
                arg 2
                rw [show List.range.loop 2 [] = [0, 1] by rfl]
              simp only [List.map]
              norm_num [Real.cos_zero, Real.cos_pi]
            rw [roots_eq]
            -- polynomialFromRealRoots [1, -1] = (X - 1) * (X + 1) = X² - 1
            unfold polynomialFromRealRoots
            simp only [List.foldr]
            -- Now have: ((X - C 1) * ((X - C (-1)) * 1)).coeff 1
            rw [mul_one, show C (-1 : ℝ) = -C 1 by simp [Polynomial.C_neg]]
            rw [sub_neg_eq_add]
            -- (X - C 1)(X + C 1) = X² - 1, which has coefficient 0 for X
            norm_num
            -- Now have: ((X - 1) * (X + 1)).coeff 1 = 0, where 1 is a polynomial
            have eq1 : (X - (1:ℝ[X])) * (X + 1) = X^2 - 1 := by ring
            rw [eq1]
            simp [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_one]
          rw [h_scaled, h_cheb]
        · -- k = 2: both have coefficient 2
          by_cases hk_eq2 : k = 2
          · rw [hk_eq2]
            -- T_2 = 2X² - 1, so coeff of X² is 2
            have h_cheb : (Chebyshev.T ℝ (2 : ℕ)).coeff 2 = 2 := by
              rw [show (2 : ℕ) = (2 : ℤ) by norm_num, Chebyshev.T_two]
              simp only [Polynomial.coeff_sub, Polynomial.coeff_one]
              rw [show (2 : ℝ[X]) = Polynomial.C 2 by rfl]
              simp [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
            -- scaledPolynomial 2 0 = 2(X² - 1), so coeff of X² is 2
            have h_scaled : (scaledPolynomial 2 0).coeff 2 = 2 := by
              -- Use the fact that it has degree 2 and leading coeff 2
              have deg : (scaledPolynomial 2 0).degree = 2 := scaledPolynomial_degree 2 0 (by omega)
              have lc : (scaledPolynomial 2 0).leadingCoeff = 2 := by
                rw [scaledPolynomial_leadingCoeff]; norm_num
              have deg_nat : (scaledPolynomial 2 0).natDegree = 2 := by
                rw [← Polynomial.degree_eq_iff_natDegree_eq_of_pos (by omega : 0 < 2)]
                exact deg
              rw [Polynomial.leadingCoeff, deg_nat] at lc
              exact lc
            rw [h_scaled, h_cheb]
          · -- k ≥ 3: both polynomials have degree 2, so coefficients are 0
            have hk_ge : 3 ≤ k := by omega
            have deg_cheb : (Chebyshev.T ℝ (2 : ℕ)).natDegree = 2 := by
              have deg : (Chebyshev.T ℝ (2 : ℕ)).degree = 2 := chebyshev_T_degree 2 (by omega)
              rw [← Polynomial.degree_eq_iff_natDegree_eq_of_pos (by omega : 0 < 2)]
              exact deg
            have deg_scaled : (scaledPolynomial 2 0).natDegree = 2 := by
              have deg : (scaledPolynomial 2 0).degree = 2 := scaledPolynomial_degree 2 0 (by omega)
              rw [← Polynomial.degree_eq_iff_natDegree_eq_of_pos (by omega : 0 < 2)]
              exact deg
            rw [Polynomial.coeff_eq_zero_of_natDegree_lt, Polynomial.coeff_eq_zero_of_natDegree_lt]
            · rw [deg_cheb]; omega
            · rw [deg_scaled]; omega
      | succ N''' =>
        -- N ≥ 3: Prove N=3 explicitly, then defer general case
        cases N''' with
        | zero =>
          -- N = 3: Prove by direct computation
          -- scaledPolynomial 3 0 has degree 3 and leading coefficient 4
          -- Chebyshev T_3 = 4X³ - 3X (degree 3, leading coeff 4)
          -- Both match for k > 0
          by_cases hk_eq : k = 1
          · -- k = 1: coeff of X
            rw [hk_eq]
            -- Both Chebyshev.T ℝ 3 and scaledPolynomial 3 0 have coeff 1 = -3
            -- Chebyshev T_3(X) = 4X³ - 3X, computed from T_0 = 1, T_1 = X, T_{n+2} = 2X·T_{n+1} - T_n
            -- T_2 = 2X·X - 1 = 2X² - 1
            -- T_3 = 2X·(2X²-1) - X = 4X³ - 2X - X = 4X³ - 3X
            have h_cheb : (Chebyshev.T ℝ (3 : ℕ)).coeff 1 = -3 := by
              -- T_3 = 2X·T_2 - T_1 = 2X·(2X² - 1) - X = 4X³ - 2X - X = 4X³ - 3X
              -- So coeff of X is -3
              have h_eq : Polynomial.Chebyshev.T ℝ (3 : ℤ) = 2 * X * (Polynomial.Chebyshev.T ℝ 2) - Polynomial.Chebyshev.T ℝ 1 := by
                have := Polynomial.Chebyshev.T_add_two ℝ (1 : ℤ)
                exact this
              simp only [show (3 : ℕ) = (3 : ℤ) by norm_num]
              rw [h_eq, Polynomial.Chebyshev.T_two, Polynomial.Chebyshev.T_one]
              -- Compute coeff of X in (2*X*(2*X²-1) - X)
              have : (2 * X * (2 * X ^ 2 - 1) - X : ℝ[X]) = 4 * X ^ 3 - 3 * X := by ring
              rw [this]
              norm_num [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_X]
            have h_scaled : (scaledPolynomial 3 0).coeff 1 = -3 := by
              -- For N=3, the roots are cos(0), cos(2π/3), cos(4π/3) = [1, -1/2, -1/2]
              -- So scaledPolynomial 3 0 = 4(X - 1)(X + 1/2)(X + 1/2) = 4(X - 1)(X + 1/2)²
              -- Expanding: (X + 1/2)² = X² + X + 1/4
              --           (X - 1)(X² + X + 1/4) = X³ + X² + X/4 - X² - X - 1/4 = X³ - 3X/4 - 1/4
              --           4(X³ - 3X/4 - 1/4) = 4X³ - 3X - 1
              -- So coeff 1 = -3
              unfold scaledPolynomial unscaledPolynomial
              -- Show realProjectionsList 3 0 = [1, -1/2, -1/2]
              have roots_eq : realProjectionsList 3 0 = [1, -1/2, -1/2] := by
                unfold realProjectionsList
                simp only [List.range]
                conv_lhs =>
                  arg 2
                  rw [show List.range.loop 3 [] = [0, 1, 2] by rfl]
                simp only [List.map, zero_add]
                norm_num [Real.cos_zero]
                constructor
                · -- cos(2π/3) = -1/2
                  have h2 : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by field_simp; ring
                  rw [h2, Real.cos_pi_sub]
                  norm_num
                · -- cos(4π/3) = -1/2
                  have h1 : 2 * Real.pi * 2 / 3 = 4 * Real.pi / 3 := by ring
                  rw [h1]
                  have h2 : 4 * Real.pi / 3 = Real.pi + Real.pi / 3 := by field_simp; ring
                  rw [h2]
                  rw [show Real.pi + Real.pi / 3 = Real.pi / 3 + Real.pi by ring]
                  rw [Real.cos_add_pi]
                  norm_num
              rw [roots_eq]
              unfold polynomialFromRealRoots
              simp only [List.foldr, mul_one]
              -- Now have: (C 4 * ((X - C 1) * ((X - C (-1/2)) * (X - C (-1/2))))).coeff 1 = -3
              -- Use Vieta's formula: coeff k = (-1)^(n-k) * esymm(n-k)
              conv_lhs => arg 1; arg 2; rw [show ((X : ℝ[X]) - C 1) * ((X - C (-1/2)) * (X - C (-1/2))) =
                                                 ([(1 : ℝ), -1/2, -1/2].map (fun r => X - C r)).prod from by
                                                   simp only [List.map, List.prod_cons, List.prod_nil, mul_one]]
              rw [Polynomial.coeff_C_mul]
              -- Convert List.prod to Multiset.prod for Vieta's formula
              rw [show ([(1 : ℝ), -1/2, -1/2].map (fun r => X - C r)).prod =
                       (([(1 : ℝ), -1/2, -1/2] : Multiset ℝ).map (fun r => X - C r)).prod by
                         rw [Multiset.map_coe]; rfl]
              rw [Multiset.prod_X_sub_C_coeff]
              · -- Now compute: 4 * ((-1)^2 * esymm 2 of [1, -1/2, -1/2]) = -3
                simp only [Multiset.coe_card, List.length_cons, List.length_nil]
                norm_num [Multiset.esymm, Multiset.powersetCard]
              · simp only [Multiset.coe_card, List.length_cons, List.length_nil]; omega
            rw [h_scaled, h_cheb]
          · by_cases hk_eq2 : k = 2
            · -- k = 2: coeff of X²
              rw [hk_eq2]
              -- Both T_3 and scaledPolynomial 3 0 have coeff of X² = 0
              have h_cheb : (Chebyshev.T ℝ (3 : ℕ)).coeff 2 = 0 := by
                have h_eq : Polynomial.Chebyshev.T ℝ (3 : ℤ) = 2 * X * (Polynomial.Chebyshev.T ℝ 2) - Polynomial.Chebyshev.T ℝ 1 := by
                  have := Polynomial.Chebyshev.T_add_two ℝ (1 : ℤ)
                  exact this
                simp only [show (3 : ℕ) = (3 : ℤ) by norm_num]
                rw [h_eq, Polynomial.Chebyshev.T_two, Polynomial.Chebyshev.T_one]
                -- T_3 = 4X³ - 3X has coeff 2 = 0
                have : (2 * X * (2 * X ^ 2 - 1) - X : ℝ[X]) = 4 * X ^ 3 - 3 * X := by ring
                rw [this]
                norm_num [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_X]
              have h_scaled : (scaledPolynomial 3 0).coeff 2 = 0 := by
                -- From the same expansion: 4X³ - 3X - 1 has coeff 2 = 0
                unfold scaledPolynomial unscaledPolynomial
                have roots_eq : realProjectionsList 3 0 = [1, -1/2, -1/2] := by
                  unfold realProjectionsList
                  simp only [List.range]
                  conv_lhs =>
                    arg 2
                    rw [show List.range.loop 3 [] = [0, 1, 2] by rfl]
                  simp only [List.map, zero_add]
                  norm_num [Real.cos_zero]
                  constructor
                  · -- cos(2π/3) = -1/2
                    have h2 : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by field_simp; ring
                    rw [h2, Real.cos_pi_sub]
                    norm_num
                  · -- cos(4π/3) = -1/2
                    have h1 : 2 * Real.pi * 2 / 3 = 4 * Real.pi / 3 := by ring
                    rw [h1]
                    have h2 : 4 * Real.pi / 3 = Real.pi + Real.pi / 3 := by field_simp; ring
                    rw [h2]
                    rw [show Real.pi + Real.pi / 3 = Real.pi / 3 + Real.pi by ring]
                    rw [Real.cos_add_pi]
                    norm_num
                rw [roots_eq]
                unfold polynomialFromRealRoots
                simp only [List.foldr, mul_one]
                -- Direct computation: scaledPolynomial 3 0 = 4X^3 - 3X - 1 has coeff_2 = 0
                -- Use Vieta's formula: coeff 2 = (-1)^(3-2) * esymm(3-2) = -esymm 1
                -- esymm 1 = sum of roots = 1 + (-1/2) + (-1/2) = 0
                conv_lhs => arg 1; arg 2; rw [show ((X : ℝ[X]) - C 1) * ((X - C (-1/2)) * (X - C (-1/2))) =
                                                   ([(1 : ℝ), -1/2, -1/2].map (fun r => X - C r)).prod from by
                                                     simp only [List.map, List.prod_cons, List.prod_nil, mul_one]]
                rw [Polynomial.coeff_C_mul]
                -- Convert List.prod to Multiset.prod for Vieta's formula
                rw [show ([(1 : ℝ), -1/2, -1/2].map (fun r => X - C r)).prod =
                         (([(1 : ℝ), -1/2, -1/2] : Multiset ℝ).map (fun r => X - C r)).prod by
                           rw [Multiset.map_coe]; rfl]
                rw [Multiset.prod_X_sub_C_coeff]
                · -- Now compute: ((-1)^1 * esymm 1 of [1, -1/2, -1/2]) = 0
                  simp only [Multiset.coe_card, List.length_cons, List.length_nil]
                  norm_num [Multiset.esymm, Multiset.powersetCard]
                · simp only [Multiset.coe_card, List.length_cons, List.length_nil]; omega
              rw [h_scaled, h_cheb]
            · by_cases hk_eq3 : k = 3
              · -- k = 3: coeff of X³ (leading coefficient)
                rw [hk_eq3]
                -- Both have degree 3 with leading coefficient 2^(3-1) = 4
                have h_cheb : (Chebyshev.T ℝ (3 : ℕ)).coeff 3 = 4 := by
                  -- T_3 = 4X³ - 3X, so coeff 3 = 4
                  have h_eq : Polynomial.Chebyshev.T ℝ (3 : ℤ) = 2 * X * (Polynomial.Chebyshev.T ℝ 2) - Polynomial.Chebyshev.T ℝ 1 := by
                    have := Polynomial.Chebyshev.T_add_two ℝ (1 : ℤ)
                    exact this
                  simp only [show (3 : ℕ) = (3 : ℤ) by norm_num]
                  rw [h_eq, Polynomial.Chebyshev.T_two, Polynomial.Chebyshev.T_one]
                  have : (2 * X * (2 * X ^ 2 - 1) - X : ℝ[X]) = 4 * X ^ 3 - 3 * X := by ring
                  rw [this]
                  norm_num [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_X]
                have h_scaled : (scaledPolynomial 3 0).coeff 3 = 4 := by
                  have deg : (scaledPolynomial 3 0).degree = 3 := scaledPolynomial_degree 3 0 (by omega)
                  have lc : (scaledPolynomial 3 0).leadingCoeff = 4 := by
                    rw [scaledPolynomial_leadingCoeff]
                    norm_num
                  have deg_nat : (scaledPolynomial 3 0).natDegree = 3 := by
                    rw [← Polynomial.degree_eq_iff_natDegree_eq_of_pos (by omega : 0 < 3)]
                    exact deg
                  rw [Polynomial.leadingCoeff, deg_nat] at lc
                  exact lc
                rw [h_scaled, h_cheb]
              · -- k ≥ 4: both polynomials have degree 3, so coefficients are 0
                have hk_ge : 4 ≤ k := by omega
                have deg_cheb : (Chebyshev.T ℝ (3 : ℕ)).natDegree = 3 := by
                  have deg : (Chebyshev.T ℝ (3 : ℕ)).degree = 3 := chebyshev_T_degree 3 (by omega)
                  rw [← Polynomial.degree_eq_iff_natDegree_eq_of_pos (by omega : 0 < 3)]
                  exact deg
                have deg_scaled : (scaledPolynomial 3 0).natDegree = 3 := by
                  have deg : (scaledPolynomial 3 0).degree = 3 := scaledPolynomial_degree 3 0 (by omega)
                  rw [← Polynomial.degree_eq_iff_natDegree_eq_of_pos (by omega : 0 < 3)]
                  exact deg
                rw [Polynomial.coeff_eq_zero_of_natDegree_lt, Polynomial.coeff_eq_zero_of_natDegree_lt]
                · rw [deg_cheb]; omega
                · rw [deg_scaled]; omega
        | succ N'''' =>
          -- N ≥ 4: General case requires deep harmonic analysis
          sorry

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

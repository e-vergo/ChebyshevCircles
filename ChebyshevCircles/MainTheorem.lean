/-
Copyright (c) 2025 Eric. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric
-/
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Algebra.BigOperators.Field
import ChebyshevCircles.PolynomialConstruction

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

/-- For θ=0, the scaled polynomial coefficients match Chebyshev for k > 0. -/
theorem scaledPolynomial_matches_chebyshev_at_zero (N : ℕ) (k : ℕ) (hN : 0 < N) (hk : 0 < k) :
    (scaledPolynomial N 0).coeff k = (Polynomial.Chebyshev.T ℝ N).coeff k := by
  sorry

/-- Coefficients for k > 0 don't vary with θ. Depends on `esymm_rotated_roots_invariant`. -/
theorem constant_term_only_varies_axiom (N : ℕ) (θ₁ θ₂ : ℝ) (k : ℕ) (hN : 0 < N) (hk : 0 < k) :
    (scaledPolynomial N θ₁).coeff k = (scaledPolynomial N θ₂).coeff k := by
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
        = (scaledPolynomial N 0).coeff n := constant_term_only_varies_axiom N θ 0 n hN h_pos
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


/-- Sum of cosines at N equally spaced angles equals zero for N ≥ 2. -/
lemma sum_cos_roots_of_unity (N : ℕ) (θ : ℝ) (hN : 2 ≤ N) :
    ∑ k ∈ Finset.range N, Real.cos (θ + 2 * π * k / N) = 0 := by
  conv_lhs =>
    arg 2
    ext k
    rw [← Complex.exp_ofReal_mul_I_re (θ + 2 * π * k / N)]
  rw [← Complex.re_sum]
  simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast]
  conv_lhs =>
    arg 1
    arg 2
    ext k
    rw [add_mul, Complex.exp_add]
  rw [← Finset.mul_sum]
  have hN' : N ≠ 0 := by omega
  let ζ := Complex.exp (2 * π * I / N)
  have hζ : IsPrimitiveRoot ζ N := Complex.isPrimitiveRoot_exp N hN'
  have geom_sum : ∑ i ∈ Finset.range N, ζ ^ i = 0 := hζ.geom_sum_eq_zero (by omega : 1 < N)
  suffices ∑ i ∈ Finset.range N, Complex.exp (↑2 * ↑π * ↑i / ↑N * I) = 0 by
    simp [this]
  calc ∑ i ∈ Finset.range N, Complex.exp (↑2 * ↑π * ↑i / ↑N * I)
      = ∑ i ∈ Finset.range N, ζ ^ i := by
        congr 1 with i
        simp only [ζ]
        rw [← Complex.exp_nat_mul]
        congr 1
        field_simp
    _ = 0 := geom_sum

/-- List.foldr for polynomial construction equals Multiset.prod. -/
lemma list_foldr_eq_multiset_prod (l : List ℝ) :
    List.foldr (fun r p => (X - C r) * p) 1 l =
    (Multiset.map (fun r => X - C r) (l : Multiset ℝ)).prod := by
  induction l with
  | nil =>
    simp [Multiset.map_zero]
  | cons head tail ih =>
    simp only [List.foldr]
    have h_coe : ((head :: tail) : Multiset ℝ) = head ::ₘ (tail : Multiset ℝ) := rfl
    rw [h_coe]
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [ih]

/-- For 0 < m < N, the sum ∑_{k=0}^{N-1} cos(m(θ + 2πk/N)) = 0. -/
lemma sum_cos_multiple_rotated_roots (N : ℕ) (m : ℕ) (θ : ℝ)
    (hN : 0 < N) (hm : 0 < m) (hm' : m < N) :
    ∑ k ∈ Finset.range N, Real.cos (m * (θ + 2 * π * k / N)) = 0 := by
  conv_lhs =>
    arg 2
    ext k
    rw [← Complex.exp_ofReal_mul_I_re (m * (θ + 2 * π * k / N))]
  rw [← Complex.re_sum]
  simp only [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_natCast]
  have hN' : N ≠ 0 := Nat.pos_iff_ne_zero.mp hN
  let ζ := Complex.exp (2 * π * I / N)
  have hζ : IsPrimitiveRoot ζ N := Complex.isPrimitiveRoot_exp N hN'
  suffices h_sum_zero : ∑ k ∈ Finset.range N, cexp (↑m * (↑2 * ↑π * ↑k / ↑N) * I) = 0 by
    simp only [mul_add, add_mul]
    conv_lhs =>
      arg 1
      arg 2
      ext x
      rw [Complex.exp_add]
    rw [← Finset.mul_sum]
    have : ∑ i ∈ Finset.range N, cexp (↑m * (↑2 * ↑π * ↑i / ↑N) * I) = 0 := h_sum_zero
    simp [this]
  calc ∑ k ∈ Finset.range N, cexp (↑m * (↑2 * ↑π * ↑k / ↑N) * I)
      = ∑ k ∈ Finset.range N, ζ ^ (m * k) := by
        congr 1 with k
        simp only [ζ]
        rw [← Complex.exp_nat_mul]
        congr 1
        field_simp
        norm_cast
    _ = ∑ k ∈ Finset.range N, (ζ ^ m) ^ k := by
        congr 1 with k
        rw [← pow_mul]
    _ = 0 := by
        have h_ne_one : ζ ^ m ≠ 1 := by
          intro h_eq
          have h_div : N ∣ m := by
            have := hζ.pow_eq_one_iff_dvd m
            exact this.mp h_eq
          have : N ≤ m := Nat.le_of_dvd (by omega) h_div
          omega
        have h_pow_N : (ζ ^ m) ^ N = 1 := by
          rw [← pow_mul, mul_comm m N, pow_mul]
          simp [hζ.pow_eq_one]
        have h_geom : (ζ ^ m - 1) * ∑ k ∈ Finset.range N, (ζ ^ m) ^ k = (ζ ^ m) ^ N - 1 :=
          mul_geom_sum (ζ ^ m) N
        rw [h_pow_N] at h_geom
        have : (ζ ^ m - 1) * ∑ k ∈ Finset.range N, (ζ ^ m) ^ k = 0 := by
          rw [h_geom]; ring
        exact eq_zero_of_ne_zero_of_mul_left_eq_zero (sub_ne_zero_of_ne h_ne_one) this

/-- cos³(x) in terms of cos(3x) and cos(x). -/
lemma cos_cube_formula (x : ℝ) :
    Real.cos x ^ 3 = (Real.cos (3 * x) + 3 * Real.cos x) / 4 := by
  have h := Real.cos_three_mul x
  have h1 : 4 * Real.cos x ^ 3 = Real.cos (3 * x) + 3 * Real.cos x := by linarith
  have h2 : Real.cos x ^ 3 = (Real.cos (3 * x) + 3 * Real.cos x) / 4 := by linarith
  exact h2

/-- Power sum of squared cosines is θ-invariant for N > 2. -/
lemma powerSumCos_invariant_j2 (N : ℕ) (θ₁ θ₂ : ℝ) (hN : 2 < N) :
    ∑ k ∈ Finset.range N, (Real.cos (θ₁ + 2 * π * k / N)) ^ 2 =
    ∑ k ∈ Finset.range N, (Real.cos (θ₂ + 2 * π * k / N)) ^ 2 := by
  have cos_sq_formula : ∀ x, Real.cos x ^ 2 = (1 + Real.cos (2 * x)) / 2 := by
    intro x
    have h1 : Real.cos (2 * x) = 2 * Real.cos x ^ 2 - 1 := by rw [Real.cos_two_mul]
    linarith [h1]
  simp_rw [cos_sq_formula, add_div, Finset.sum_add_distrib]
  have h1_raw := sum_cos_multiple_rotated_roots N 2 θ₁ (by omega) (by omega) (by omega)
  have h2_raw := sum_cos_multiple_rotated_roots N 2 θ₂ (by omega) (by omega) (by omega)
  have h1 : ∑ x ∈ Finset.range N, Real.cos (2 * (θ₁ + 2 * π * ↑x / ↑N)) = 0 := by
    convert h1_raw using 2
  have h2 : ∑ x ∈ Finset.range N, Real.cos (2 * (θ₂ + 2 * π * ↑x / ↑N)) = 0 := by
    convert h2_raw using 2
  congr 1
  rw [← Finset.sum_div, ← Finset.sum_div, h1, h2]

/-- Power sum of cubed cosines is θ-invariant for N > 3. -/
lemma powerSumCos_invariant_j3 (N : ℕ) (θ₁ θ₂ : ℝ) (hN : 3 < N) :
    ∑ k ∈ Finset.range N, (Real.cos (θ₁ + 2 * π * k / N)) ^ 3 =
    ∑ k ∈ Finset.range N, (Real.cos (θ₂ + 2 * π * k / N)) ^ 3 := by
  simp_rw [cos_cube_formula, add_div, Finset.sum_add_distrib]
  have h1a : ∑ k ∈ Finset.range N, Real.cos (3 * (θ₁ + 2 * π * k / N)) / 4 = 0 := by
    rw [← Finset.sum_div]
    have : ∑ k ∈ Finset.range N, Real.cos (3 * (θ₁ + 2 * π * k / N)) = 0 :=
      sum_cos_multiple_rotated_roots N 3 θ₁ (by omega) (by omega) (by omega)
    rw [this]; norm_num
  have h1b : ∑ k ∈ Finset.range N, Real.cos (3 * (θ₂ + 2 * π * k / N)) / 4 = 0 := by
    rw [← Finset.sum_div]
    have : ∑ k ∈ Finset.range N, Real.cos (3 * (θ₂ + 2 * π * k / N)) = 0 :=
      sum_cos_multiple_rotated_roots N 3 θ₂ (by omega) (by omega) (by omega)
    rw [this]; norm_num
  have h2a : ∑ k ∈ Finset.range N, 3 * Real.cos (θ₁ + 2 * π * k / N) / 4 = 0 := by
    rw [← Finset.sum_div, ← Finset.mul_sum]
    have : ∑ k ∈ Finset.range N, Real.cos (θ₁ + 2 * π * k / N) = 0 :=
      sum_cos_roots_of_unity N θ₁ (by omega)
    rw [this]; norm_num
  have h2b : ∑ k ∈ Finset.range N, 3 * Real.cos (θ₂ + 2 * π * k / N) / 4 = 0 := by
    rw [← Finset.sum_div, ← Finset.mul_sum]
    have : ∑ k ∈ Finset.range N, Real.cos (θ₂ + 2 * π * k / N) = 0 :=
      sum_cos_roots_of_unity N θ₂ (by omega)
    rw [this]; norm_num
  rw [h1a, h1b, h2a, h2b]

/-- cos⁴(x) power-reduction formula. -/
lemma cos_four_formula (x : ℝ) :
    Real.cos x ^ 4 = (3 + 4 * Real.cos (2 * x) + Real.cos (4 * x)) / 8 := by
  have h1 : Real.cos x ^ 4 = (Real.cos x ^ 2) ^ 2 := by ring
  rw [h1]
  have h2 : Real.cos x ^ 2 = (1 + Real.cos (2 * x)) / 2 := by rw [Real.cos_sq]; ring
  rw [h2]
  have h3 : ((1 + Real.cos (2 * x)) / 2) ^ 2 =
      (1 + 2 * Real.cos (2 * x) + Real.cos (2 * x) ^ 2) / 4 := by field_simp; ring
  rw [h3]
  have h4 : Real.cos (2 * x) ^ 2 = (1 + Real.cos (4 * x)) / 2 := by
    rw [Real.cos_sq]; ring
  rw [h4]
  field_simp; ring

/-- Power sum of fourth powers of cosines is θ-invariant for N > 4. -/
lemma powerSumCos_invariant_j4 (N : ℕ) (θ₁ θ₂ : ℝ) (hN : 4 < N) :
    ∑ k ∈ Finset.range N, (Real.cos (θ₁ + 2 * π * k / N)) ^ 4 =
    ∑ k ∈ Finset.range N, (Real.cos (θ₂ + 2 * π * k / N)) ^ 4 := by
  simp_rw [cos_four_formula, add_div, Finset.sum_add_distrib]
  have h1_raw := sum_cos_multiple_rotated_roots N 2 θ₁ (by omega) (by omega) (by omega)
  have h2_raw := sum_cos_multiple_rotated_roots N 2 θ₂ (by omega) (by omega) (by omega)
  have h3_raw := sum_cos_multiple_rotated_roots N 4 θ₁ (by omega) (by omega) (by omega)
  have h4_raw := sum_cos_multiple_rotated_roots N 4 θ₂ (by omega) (by omega) (by omega)
  have h1 : ∑ k ∈ Finset.range N, Real.cos (2 * (θ₁ + 2 * π * ↑k / ↑N)) = 0 := by
    convert h1_raw using 2
  have h2 : ∑ k ∈ Finset.range N, Real.cos (2 * (θ₂ + 2 * π * ↑k / ↑N)) = 0 := by
    convert h2_raw using 2
  have h3 : ∑ k ∈ Finset.range N, Real.cos (4 * (θ₁ + 2 * π * ↑k / ↑N)) = 0 := by
    convert h3_raw using 2
  have h4 : ∑ k ∈ Finset.range N, Real.cos (4 * (θ₂ + 2 * π * ↑k / ↑N)) = 0 := by
    convert h4_raw using 2
  have eq1 : ∑ k ∈ Finset.range N, (4 * Real.cos (2 * (θ₁ + 2 * π * k / N))) / 8 = 0 := by
    rw [← Finset.sum_div, ← Finset.mul_sum, h1]; norm_num
  have eq2 : ∑ k ∈ Finset.range N, (4 * Real.cos (2 * (θ₂ + 2 * π * k / N))) / 8 = 0 := by
    rw [← Finset.sum_div, ← Finset.mul_sum, h2]; norm_num
  have eq3 : ∑ k ∈ Finset.range N, Real.cos (4 * (θ₁ + 2 * π * k / N)) / 8 = 0 := by
    rw [← Finset.sum_div, h3]; norm_num
  have eq4 : ∑ k ∈ Finset.range N, Real.cos (4 * (θ₂ + 2 * π * k / N)) / 8 = 0 := by
    rw [← Finset.sum_div, h4]; norm_num
  rw [eq1, eq2, eq3, eq4]

/-- Quintuple-angle formula for cosine. -/
lemma cos_five_mul (x : ℝ) :
    Real.cos (5 * x) = 16 * Real.cos x ^ 5 - 20 * Real.cos x ^ 3 + 5 * Real.cos x := by
  have h1 : (5 : ℝ) * x = 2 * x + 3 * x := by ring
  rw [h1, Real.cos_add, Real.cos_two_mul, Real.sin_two_mul, Real.cos_three_mul,
      Real.sin_three_mul]
  have h_sin2 : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by
    have := Real.sin_sq_add_cos_sq x; linarith
  have h_sin3 : Real.sin x ^ 3 = Real.sin x * (1 - Real.cos x ^ 2) := by
    rw [pow_succ, h_sin2]; ring
  rw [h_sin3]
  calc (2 * Real.cos x ^ 2 - 1) * (4 * Real.cos x ^ 3 - 3 * Real.cos x) -
        2 * Real.sin x * Real.cos x * (3 * Real.sin x -
        4 * (Real.sin x * (1 - Real.cos x ^ 2)))
      = (2 * Real.cos x ^ 2 - 1) * (4 * Real.cos x ^ 3 - 3 * Real.cos x) -
        2 * Real.sin x ^ 2 * Real.cos x * (4 * Real.cos x ^ 2 - 1) := by ring
    _ = (2 * Real.cos x ^ 2 - 1) * (4 * Real.cos x ^ 3 - 3 * Real.cos x) -
        2 * (1 - Real.cos x ^ 2) * Real.cos x * (4 * Real.cos x ^ 2 - 1) := by rw [h_sin2]
    _ = 16 * Real.cos x ^ 5 - 20 * Real.cos x ^ 3 + 5 * Real.cos x := by ring

/-- cos⁵(x) power-reduction formula. -/
lemma cos_five_formula (x : ℝ) :
    Real.cos x ^ 5 = (Real.cos (5 * x) + 5 * Real.cos (3 * x) + 10 * Real.cos x) / 16 := by
  have h_five : Real.cos (5 * x) =
      16 * Real.cos x ^ 5 - 20 * Real.cos x ^ 3 + 5 * Real.cos x := cos_five_mul x
  have h_cube : Real.cos x ^ 3 = (Real.cos (3 * x) + 3 * Real.cos x) / 4 :=
      cos_cube_formula x
  rw [h_cube] at h_five
  have h_simplified :
      Real.cos (5 * x) = 16 * Real.cos x ^ 5 - 5 * Real.cos (3 * x) - 10 * Real.cos x := by
    calc Real.cos (5 * x)
        = 16 * Real.cos x ^ 5 - 20 * ((Real.cos (3 * x) + 3 * Real.cos x) / 4) +
          5 * Real.cos x := h_five
      _ = 16 * Real.cos x ^ 5 - 5 * (Real.cos (3 * x) + 3 * Real.cos x) +
          5 * Real.cos x := by ring
      _ = 16 * Real.cos x ^ 5 - 5 * Real.cos (3 * x) - 10 * Real.cos x := by ring
  linarith [h_simplified]

/-- Power sum of fifth powers of cosines is θ-invariant for N > 5. -/
lemma powerSumCos_invariant_j5 (N : ℕ) (θ₁ θ₂ : ℝ) (hN : 5 < N) :
    ∑ k ∈ Finset.range N, (Real.cos (θ₁ + 2 * π * k / N)) ^ 5 =
    ∑ k ∈ Finset.range N, (Real.cos (θ₂ + 2 * π * k / N)) ^ 5 := by
  simp_rw [cos_five_formula, add_div, Finset.sum_add_distrib]
  have h1_5_raw := sum_cos_multiple_rotated_roots N 5 θ₁ (by omega) (by omega) (by omega)
  have h2_5_raw := sum_cos_multiple_rotated_roots N 5 θ₂ (by omega) (by omega) (by omega)
  have h1_3_raw := sum_cos_multiple_rotated_roots N 3 θ₁ (by omega) (by omega) (by omega)
  have h2_3_raw := sum_cos_multiple_rotated_roots N 3 θ₂ (by omega) (by omega) (by omega)
  have h1_1_raw := sum_cos_roots_of_unity N θ₁ (by omega)
  have h2_1_raw := sum_cos_roots_of_unity N θ₂ (by omega)
  have h1_5 : ∑ k ∈ Finset.range N, Real.cos (5 * (θ₁ + 2 * π * ↑k / ↑N)) = 0 := by
    convert h1_5_raw using 2
  have h2_5 : ∑ k ∈ Finset.range N, Real.cos (5 * (θ₂ + 2 * π * ↑k / ↑N)) = 0 := by
    convert h2_5_raw using 2
  have h1_3 : ∑ k ∈ Finset.range N, Real.cos (3 * (θ₁ + 2 * π * ↑k / ↑N)) = 0 := by
    convert h1_3_raw using 2
  have h2_3 : ∑ k ∈ Finset.range N, Real.cos (3 * (θ₂ + 2 * π * ↑k / ↑N)) = 0 := by
    convert h2_3_raw using 2
  have h1_1 : ∑ k ∈ Finset.range N, Real.cos (θ₁ + 2 * π * ↑k / ↑N) = 0 := by
    convert h1_1_raw using 2
  have h2_1 : ∑ k ∈ Finset.range N, Real.cos (θ₂ + 2 * π * ↑k / ↑N) = 0 := by
    convert h2_1_raw using 2
  have eq1 : ∑ k ∈ Finset.range N, Real.cos (5 * (θ₁ + 2 * π * k / N)) / 16 = 0 := by
    rw [← Finset.sum_div, h1_5]; norm_num
  have eq2 : ∑ k ∈ Finset.range N, Real.cos (5 * (θ₂ + 2 * π * k / N)) / 16 = 0 := by
    rw [← Finset.sum_div, h2_5]; norm_num
  have eq3 : ∑ k ∈ Finset.range N, (5 * Real.cos (3 * (θ₁ + 2 * π * k / N))) / 16 = 0 := by
    rw [← Finset.sum_div, ← Finset.mul_sum, h1_3]; norm_num
  have eq4 : ∑ k ∈ Finset.range N, (5 * Real.cos (3 * (θ₂ + 2 * π * k / N))) / 16 = 0 := by
    rw [← Finset.sum_div, ← Finset.mul_sum, h2_3]; norm_num
  have eq5 : ∑ k ∈ Finset.range N, (10 * Real.cos (θ₁ + 2 * π * k / N)) / 16 = 0 := by
    rw [← Finset.sum_div, ← Finset.mul_sum, h1_1]; norm_num
  have eq6 : ∑ k ∈ Finset.range N, (10 * Real.cos (θ₂ + 2 * π * k / N)) / 16 = 0 := by
    rw [← Finset.sum_div, ← Finset.mul_sum, h2_1]; norm_num
  rw [eq1, eq2, eq3, eq4, eq5, eq6]

/-- Power sum of cosines is θ-invariant for 0 < j < N. -/
lemma powerSumCos_invariant (N : ℕ) (j : ℕ) (θ₁ θ₂ : ℝ)
    (hN : 0 < N) (hj : 0 < j) (hj' : j < N) :
    ∑ k ∈ Finset.range N, (Real.cos (θ₁ + 2 * π * k / N)) ^ j =
    ∑ k ∈ Finset.range N, (Real.cos (θ₂ + 2 * π * k / N)) ^ j := by
  sorry

/-- Connection between Multiset.esymm and power sums via Newton's identity. -/
lemma multiset_esymm_from_psum (s : Multiset ℝ) (m : ℕ) (hm : 0 < m) (hm' : m < s.card) :
    ∃ (c : ℝ), m * c * s.esymm m =
      (Finset.range m).sum (fun i =>
        s.esymm i * (s.map (fun x => x ^ (m - i))).sum) := by
  sorry

/-- Elementary symmetric polynomials in rotated roots are θ-invariant for 0 < m < N. -/
lemma esymm_rotated_roots_invariant (N : ℕ) (m : ℕ) (θ₁ θ₂ : ℝ)
    (hN : 0 < N) (hm : 0 < m) (hm' : m < N) :
    let l1 := (realProjectionsList N θ₁ : Multiset ℝ)
    let l2 := (realProjectionsList N θ₂ : Multiset ℝ)
    l1.esymm m = l2.esymm m := by
  intro l1 l2
  induction m using Nat.strong_induction_on with
  | h k IH =>
    cases k with
    | zero => omega
    | succ k' =>
      cases k' with
      | zero => sorry
      | succ k'' =>
        have h_psum := multiset_esymm_from_psum l1 (k'' + 2) (by omega) (by
          simp only [l1]
          rw [Multiset.coe_card, card_realProjectionsList]
          have : k'' + 2 = k'' + 1 + 1 := by omega
          rw [this]
          exact hm')
        sorry

/-- The constant term is the only coefficient that varies with θ. -/
theorem constant_term_only_varies (N : ℕ) (θ₁ θ₂ : ℝ) (k : ℕ) (hN : 0 < N) (hk : 0 < k) :
    (scaledPolynomial N θ₁).coeff k = (scaledPolynomial N θ₂).coeff k := by
  unfold scaledPolynomial
  rw [coeff_C_mul, coeff_C_mul]
  congr 1
  unfold unscaledPolynomial polynomialFromRealRoots realProjectionsList
  sorry

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

end

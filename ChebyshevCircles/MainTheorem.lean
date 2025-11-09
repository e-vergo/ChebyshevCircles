/-
Copyright (c) 2025 Eric. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric
-/
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Algebra.BigOperators.Field
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import ChebyshevCircles.PolynomialConstruction
import ChebyshevCircles.RootsOfUnity

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

/-! ## Trigonometric Identities and Sums

Fundamental lemmas about sums of cosines at equally-spaced angles. These leverage the
geometric sum formulas for primitive roots of unity to show that most trigonometric sums
vanish, which is key to proving the θ-invariance of power sums.
-/

section TrigonometricIdentities

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

end TrigonometricIdentities

/-! ## Power Sum Lemmas

Lemmas establishing the θ-invariance of power sums ∑ cos(θ + 2πk/N)^j for various j.
These results are proven using power-reduction formulas and the vanishing sums from the
previous section. The general case (for all j < N) is proven via binomial expansion.
-/

section PowerSums

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
    rw [Real.cos_sq]
    ring_nf
  rw [h4]
  field_simp
  ring

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

/-- cos⁶(x) power-reduction formula. -/
lemma cos_six_formula (x : ℝ) :
    Real.cos x ^ 6 = (10 + 15 * Real.cos (2 * x) + 6 * Real.cos (4 * x) + Real.cos (6 * x)) / 32 := by
  -- cos^6 = (cos^2)^3
  have h1 : Real.cos x ^ 6 = (Real.cos x ^ 2) ^ 3 := by ring
  rw [h1]
  -- cos^2 = (1 + cos(2x))/2
  have h2 : Real.cos x ^ 2 = (1 + Real.cos (2 * x)) / 2 := by rw [Real.cos_sq]; ring
  rw [h2]
  -- Expand ((1 + cos(2x))/2)^3
  have h3 : ((1 + Real.cos (2 * x)) / 2) ^ 3 =
      (1 + 3 * Real.cos (2 * x) + 3 * Real.cos (2 * x) ^ 2 + Real.cos (2 * x) ^ 3) / 8 := by
    field_simp
    ring
  rw [h3]
  -- Apply double-angle formulas to cos^2(2x) and cos^3(2x)
  have h4 : Real.cos (2 * x) ^ 2 = (1 + Real.cos (4 * x)) / 2 := by
    rw [Real.cos_sq]; ring_nf
  have h5 : Real.cos (2 * x) ^ 3 = (Real.cos (6 * x) + 3 * Real.cos (2 * x)) / 4 := by
    convert cos_cube_formula (2 * x) using 1
    ring_nf
  rw [h4, h5]
  field_simp
  ring


/-- Power sum of sixth powers of cosines is θ-invariant for N > 6. -/
lemma powerSumCos_invariant_j6 (N : ℕ) (θ₁ θ₂ : ℝ) (hN : 6 < N) :
    ∑ k ∈ Finset.range N, (Real.cos (θ₁ + 2 * π * k / N)) ^ 6 =
    ∑ k ∈ Finset.range N, (Real.cos (θ₂ + 2 * π * k / N)) ^ 6 := by
  simp_rw [cos_six_formula, add_div, Finset.sum_add_distrib]
  -- All non-constant terms vanish
  have h2_1 := sum_cos_multiple_rotated_roots N 2 θ₁ (by omega) (by omega) (by omega)
  have h2_2 := sum_cos_multiple_rotated_roots N 2 θ₂ (by omega) (by omega) (by omega)
  have h4_1 := sum_cos_multiple_rotated_roots N 4 θ₁ (by omega) (by omega) (by omega)
  have h4_2 := sum_cos_multiple_rotated_roots N 4 θ₂ (by omega) (by omega) (by omega)
  have h6_1 := sum_cos_multiple_rotated_roots N 6 θ₁ (by omega) (by omega) (by omega)
  have h6_2 := sum_cos_multiple_rotated_roots N 6 θ₂ (by omega) (by omega) (by omega)
  -- Convert sums
  have eq1 : ∑ x ∈ Finset.range N, Real.cos (2 * (θ₁ + 2 * π * x / N)) = 0 := by convert h2_1 using 2
  have eq2 : ∑ x ∈ Finset.range N, Real.cos (2 * (θ₂ + 2 * π * x / N)) = 0 := by convert h2_2 using 2
  have eq3 : ∑ x ∈ Finset.range N, Real.cos (4 * (θ₁ + 2 * π * x / N)) = 0 := by convert h4_1 using 2
  have eq4 : ∑ x ∈ Finset.range N, Real.cos (4 * (θ₂ + 2 * π * x / N)) = 0 := by convert h4_2 using 2
  have eq5 : ∑ x ∈ Finset.range N, Real.cos (6 * (θ₁ + 2 * π * x / N)) = 0 := by convert h6_1 using 2
  have eq6 : ∑ x ∈ Finset.range N, Real.cos (6 * (θ₂ + 2 * π * x / N)) = 0 := by convert h6_2 using 2
  simp only [← Finset.sum_div, ← Finset.mul_sum, eq1, eq2, eq3, eq4, eq5, eq6]

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

/-- Helper: The sum ∑_k (z * ω^k)^j over a full set of N-th roots of unity ω
equals 0 when 0 < j < N (since ω^j is a non-trivial N-th root of unity). -/
lemma sum_pow_primitive_root_mul (N j : ℕ) (z : ℂ) (hN : 0 < N) (hj : 0 < j) (hj' : j < N) :
    let ω := Complex.exp (2 * π * Complex.I / N)
    ∑ k ∈ Finset.range N, (z * ω ^ k) ^ j = 0 := by
  intro ω
  have hN' : N ≠ 0 := Nat.pos_iff_ne_zero.mp hN
  have hω : IsPrimitiveRoot ω N := Complex.isPrimitiveRoot_exp N hN'
  simp_rw [mul_pow]
  by_cases hz : z = 0
  · have hj_ne : j ≠ 0 := Nat.pos_iff_ne_zero.mp hj
    simp [hz, zero_pow hj_ne]
  · rw [← Finset.mul_sum]
    have sum_eq : ∑ k ∈ Finset.range N, (ω ^ k) ^ j = 0 := by
      -- Convert (ω^k)^j to ω^(k*j) = (ω^j)^k
      conv_lhs => arg 2; ext k; rw [← pow_mul, mul_comm k j, pow_mul]
      have h_ne_one : ω ^ j ≠ 1 := by
        intro h_eq
        have h_div : N ∣ j := (hω.pow_eq_one_iff_dvd j).mp h_eq
        have : N ≤ j := Nat.le_of_dvd hj h_div
        omega
      have h_pow_N : (ω ^ j) ^ N = 1 := by
        calc (ω ^ j) ^ N = ω ^ (j * N) := by rw [← pow_mul]
          _ = ω ^ (N * j) := by rw [mul_comm]
          _ = (ω ^ N) ^ j := by rw [← pow_mul]
          _ = 1 ^ j := by rw [hω.pow_eq_one]
          _ = 1 := one_pow j
      have h_geom : (ω ^ j - 1) * ∑ k ∈ Finset.range N, (ω ^ j) ^ k = (ω ^ j) ^ N - 1 :=
        mul_geom_sum (ω ^ j) N
      rw [h_pow_N] at h_geom
      have h_eq_zero : (ω ^ j - 1) * ∑ k ∈ Finset.range N, (ω ^ j) ^ k = 0 := by
        rw [h_geom]; ring
      exact eq_zero_of_ne_zero_of_mul_left_eq_zero (sub_ne_zero_of_ne h_ne_one) h_eq_zero
    simp [sum_eq]

/-- Helper: Sum of ω^{km} over k ∈ range N equals 0 when 0 < m < N. -/
lemma sum_primitive_root_pow_mul (N m : ℕ) (hN : 0 < N) (hm : 0 < m) (hm' : m < N) :
    let ω := Complex.exp (2 * π * Complex.I / N)
    ∑ k ∈ Finset.range N, ω ^ (k * m) = 0 := by
  intro ω
  have hN' : N ≠ 0 := Nat.pos_iff_ne_zero.mp hN
  have hω : IsPrimitiveRoot ω N := Complex.isPrimitiveRoot_exp N hN'
  conv_lhs => arg 2; ext k; rw [mul_comm k m, pow_mul]
  have h_ne_one : ω ^ m ≠ 1 := by
    intro h_eq
    have h_div : N ∣ m := (hω.pow_eq_one_iff_dvd m).mp h_eq
    have : N ≤ m := Nat.le_of_dvd hm h_div
    omega
  have h_pow_N : (ω ^ m) ^ N = 1 := by
    calc (ω ^ m) ^ N = ω ^ (m * N) := by rw [← pow_mul]
      _ = ω ^ (N * m) := by rw [mul_comm]
      _ = (ω ^ N) ^ m := by rw [← pow_mul]
      _ = 1 ^ m := by rw [hω.pow_eq_one]
      _ = 1 := one_pow m
  have h_geom : (ω ^ m - 1) * ∑ k ∈ Finset.range N, (ω ^ m) ^ k = (ω ^ m) ^ N - 1 :=
    mul_geom_sum (ω ^ m) N
  rw [h_pow_N] at h_geom
  have h_eq_zero : (ω ^ m - 1) * ∑ k ∈ Finset.range N, (ω ^ m) ^ k = 0 := by
    rw [h_geom]; ring
  exact eq_zero_of_ne_zero_of_mul_left_eq_zero (sub_ne_zero_of_ne h_ne_one) h_eq_zero

/-- Sum of cosines at integer multiples of angles vanishes for non-zero integers with |m| < N. -/
lemma sum_cos_int_multiple_vanishes (N : ℕ) (m : ℤ) (θ : ℝ)
    (hN : 0 < N) (hm : m ≠ 0) (hm' : |m| < N) :
    ∑ k ∈ Finset.range N, Real.cos (m * (θ + 2 * π * k / N)) = 0 := by
  -- Case split on sign of m
  by_cases hm_pos : 0 < m
  · -- m > 0: use sum_cos_multiple_rotated_roots with m as ℕ
    have hm_nat_pos : 0 < m.toNat := by
      omega
    have hm_nat_lt : m.toNat < N := by
      have : (m.toNat : ℤ) = m := Int.toNat_of_nonneg (le_of_lt hm_pos)
      rw [← Nat.cast_lt (α := ℤ)]
      calc (m.toNat : ℤ)
        _ = m := this
        _ = |m| := (abs_of_pos hm_pos).symm
        _ < (N : ℤ) := hm'
    have h_cast : (m : ℝ) = (m.toNat : ℝ) := by
      have : (m.toNat : ℤ) = m := Int.toNat_of_nonneg (le_of_lt hm_pos)
      have : m = (m.toNat : ℤ) := this.symm
      exact_mod_cast this
    simp_rw [h_cast]
    exact sum_cos_multiple_rotated_roots N m.toNat θ hN hm_nat_pos hm_nat_lt
  · -- m < 0: use cos(-x) = cos(x) and the positive case
    push_neg at hm_pos
    have hm_neg : m < 0 := by omega
    have neg_m_pos : 0 < -m := neg_pos.mpr hm_neg
    have h_nat_pos : 0 < (-m).toNat := by
      omega
    have h_nat_lt : (-m).toNat < N := by
      have : ((-m).toNat : ℤ) = -m := Int.toNat_of_nonneg (le_of_lt neg_m_pos)
      rw [← Nat.cast_lt (α := ℤ)]
      calc ((-m).toNat : ℤ)
        _ = -m := this
        _ = |m| := (abs_of_neg hm_neg).symm
        _ < (N : ℤ) := hm'
    have h_cast : (m : ℝ) = -((-m).toNat : ℝ) := by
      have h1 : ((-m).toNat : ℤ) = -m := Int.toNat_of_nonneg (le_of_lt neg_m_pos)
      have h2 : (-m : ℝ) = ((-m).toNat : ℝ) := by exact_mod_cast h1.symm
      calc (m : ℝ)
        _ = -(-m : ℝ) := by ring
        _ = -((-m).toNat : ℝ) := by rw [h2]
    simp_rw [h_cast, neg_mul, Real.cos_neg]
    exact sum_cos_multiple_rotated_roots N (-m).toNat θ hN h_nat_pos h_nat_lt

/-- Helper: cos(x) expressed using complex exponentials -/
lemma cos_as_exp (x : ℝ) :
    Real.cos x = ((Complex.exp (x * Complex.I) + Complex.exp (-(x * Complex.I))) / 2).re := by
  rw [show (Complex.exp (↑x * Complex.I) + Complex.exp (-(↑x * Complex.I))) / 2 = Complex.cos (x : ℂ) by
    rw [Complex.cos]
    congr 2
    congr 1
    rw [neg_mul]]
  exact Complex.cos_ofReal_re x

/-- Helper: Power of sum using binomial theorem in Complex -/
lemma exp_add_exp_pow (x : ℂ) (j : ℕ) :
    (Complex.exp (x * Complex.I) + Complex.exp (-(x * Complex.I))) ^ j =
    ∑ r ∈ Finset.range (j + 1), (j.choose r : ℂ) *
      Complex.exp ((2 * r - j : ℤ) * x * Complex.I) := by
  rw [Commute.add_pow (Commute.all _ _)]
  apply Finset.sum_congr rfl
  intro r hr
  have hr_le : r ≤ j := by
    simp only [Finset.mem_range] at hr
    omega
  -- LHS has: exp(xI)^r * exp(-xI)^(j-r) * choose(j,r)
  -- RHS has: choose(j,r) * exp((2r-j)*xI)
  rw [← Complex.exp_nat_mul (n := r), ← Complex.exp_nat_mul (n := j - r)]
  rw [← Complex.exp_add]
  rw [mul_comm]
  congr 1
  -- Show: r * (x * I) + (j - r) * (-(x * I)) = (2 * r - j) * x * I
  simp only [Nat.cast_sub hr_le]
  congr 1
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
  ring

/-- Express sum of cos^j as sum over binomial expansion with vanishing non-constant terms.
    This uses the identity cos(x) = (e^{ix} + e^{-ix})/2 and binomial expansion. -/
lemma sum_cos_pow_eq_sum_binomial (N j : ℕ) (θ : ℝ) (_hN : 0 < N) (_hj : j < N) :
    ∑ k ∈ Finset.range N, (Real.cos (θ + 2 * π * k / N)) ^ j =
    (2 : ℝ) ^ (-(j : ℤ)) * ∑ r ∈ Finset.range (j + 1), (j.choose r : ℝ) *
    ∑ k ∈ Finset.range N, Real.cos (((2 * r - j) : ℤ) * (θ + 2 * π * k / N)) := by
  -- Use the fact that cos(x) = Re((e^{ix} + e^{-ix})/2)
  -- and apply binomial theorem
  simp only [cos_as_exp]
  -- Pull power inside re: (z.re)^j = (z^j).re when z is real
  have h_re_pow : ∀ k, ((Complex.exp (↑(θ + 2 * π * k / N) * Complex.I) +
      Complex.exp (-(↑(θ + 2 * π * k / N) * Complex.I))) / 2).re ^ j =
    (((Complex.exp (↑(θ + 2 * π * k / N) * Complex.I) +
      Complex.exp (-(↑(θ + 2 * π * k / N) * Complex.I))) / 2) ^ j).re := by
    intro k
    -- The sum e^{ix} + e^{-ix} is real (it equals 2cos(x))
    set z := (Complex.exp (↑(θ + 2 * π * k / N) * Complex.I) +
        Complex.exp (-(↑(θ + 2 * π * k / N) * Complex.I))) / 2 with z_def
    have h_real : z.im = 0 := by
      rw [z_def]
      have h1 : (Complex.exp (↑(θ + 2 * π * k / N) * Complex.I) +
          Complex.exp (-(↑(θ + 2 * π * k / N) * Complex.I))).im = 0 := by
        rw [Complex.add_im, Complex.exp_ofReal_mul_I_im]
        have : (Complex.exp (-(↑(θ + 2 * π * k / N) * Complex.I))).im =
          Real.sin (-(θ + 2 * π * k / N)) := by
          rw [show -(↑(θ + 2 * π * k / N) * Complex.I) =
            (↑(-(θ + 2 * π * k / N)) : ℂ) * Complex.I by
            apply Complex.ext <;> simp]
          exact Complex.exp_ofReal_mul_I_im _
        rw [this, Real.sin_neg]
        ring
      rw [Complex.div_im, h1]
      simp
    -- Since z is real, z.re^j = (z^j).re
    have h_eq : z = (z.re : ℂ) := Complex.ext rfl h_real
    calc z.re ^ j
      _ = (z.re : ℂ).re ^ j := by simp
      _ = ((z.re : ℂ) ^ j).re := by simp [← Complex.ofReal_pow]
      _ = (z ^ j).re := by rw [← h_eq]
  conv_lhs =>
    arg 2
    ext k
    rw [h_re_pow k]
  rw [← Complex.re_sum]
  -- Now work with the sum of complex powers
  -- Apply binomial expansion to each term, then manipulate
  simp only [div_pow]
  -- Apply binomial expansion inside the sum and factor out 2^j
  rw [show ∑ x ∈ Finset.range N, (Complex.exp (↑(θ + 2 * π * ↑x / ↑N) * Complex.I) +
      Complex.exp (-(↑(θ + 2 * π * ↑x / ↑N) * Complex.I))) ^ j / (2 : ℂ) ^ j =
    ∑ x ∈ Finset.range N, (∑ r ∈ Finset.range (j + 1), (j.choose r : ℂ) *
      Complex.exp ((2 * r - j : ℤ) * ↑(θ + 2 * π * ↑x / ↑N) * Complex.I)) / (2 : ℂ) ^ j by
    apply Finset.sum_congr rfl
    intro i _
    rw [exp_add_exp_pow (↑(θ + 2 * π * ↑i / ↑N)) j]]
  rw [← Finset.sum_div]
  -- Rewrite division as multiplication by inverse
  rw [div_eq_mul_inv, mul_comm]
  -- Simplify: (2^j)⁻¹ = 2^(-j)
  rw [show ((2 : ℂ) ^ j)⁻¹ = (2 : ℂ) ^ (-(j : ℤ)) by
    rw [← zpow_natCast, ← zpow_neg_one, ← zpow_mul]
    norm_num]
  -- Move .re inside and commute sums
  rw [Complex.mul_re]
  -- Simplify: Re(2^(-j)) = 2^(-j) and Im(2^(-j)) = 0
  have h_re : ((2 : ℂ) ^ (-(j : ℤ))).re = (2 : ℝ) ^ (-(j : ℤ)) := by
    have : (2 : ℂ) = (↑(2 : ℝ) : ℂ) := rfl
    rw [this, ← Complex.ofReal_zpow, Complex.ofReal_re]
  have h_im : ((2 : ℂ) ^ (-(j : ℤ))).im = 0 := by
    have : (2 : ℂ) = (↑(2 : ℝ) : ℂ) := rfl
    rw [this, ← Complex.ofReal_zpow, Complex.ofReal_im]
  rw [h_re, h_im]
  simp
  -- Now commute the sums and simplify the RHS
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← Finset.mul_sum]
  congr 1
  -- Show (∑ exp(...)).re = ∑ (exp(...).re + exp(-...).re) / 2
  rw [← Complex.re_sum]
  -- Now show ∑ exp(...).re = ∑ (exp(...).re + exp(-...).re) / 2
  -- First move .re inside the left sum
  rw [Complex.re_sum]
  -- Each term: exp(ix).re = (exp(ix).re + exp(-ix).re) / 2
  -- This holds because exp(ix).re = cos(x) and exp(-ix).re = cos(-x) = cos(x)
  apply Finset.sum_congr rfl
  intro k _
  -- Show exp(...).re = (exp(...).re + exp(-...).re) / 2
  -- Use that exp(ix).re = cos(x) and exp(-ix).re = cos(-x) = cos(x)
  have h1 : (Complex.exp ((2 * ↑r - ↑j) * (↑θ + 2 * ↑π * ↑k / ↑N) * Complex.I)).re =
    Real.cos ((2 * ↑r - ↑j) * (θ + 2 * π * ↑k / ↑N)) := by
    have : (2 * ↑r - ↑j) * (↑θ + 2 * ↑π * ↑k / ↑N) * Complex.I =
      ↑((2 * ↑r - ↑j) * (θ + 2 * π * ↑k / ↑N)) * Complex.I := by
      push_cast
      ring
    rw [this, Complex.exp_ofReal_mul_I_re]
  have h2 : (Complex.exp (-((2 * ↑r - ↑j) * (↑θ + 2 * ↑π * ↑k / ↑N) * Complex.I))).re =
    Real.cos ((2 * ↑r - ↑j) * (θ + 2 * π * ↑k / ↑N)) := by
    have : -((2 * ↑r - ↑j) * (↑θ + 2 * ↑π * ↑k / ↑N) * Complex.I) =
      ↑(-((2 * ↑r - ↑j) * (θ + 2 * π * ↑k / ↑N))) * Complex.I := by
      push_cast
      ring
    rw [this, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  rw [h1, h2]
  ring

/-- Power sums of cos^j are independent of θ for 0 < j < N. -/
lemma sum_cos_pow_theta_independent (N j : ℕ) (θ₁ θ₂ : ℝ)
    (hN : 0 < N) (_hj : 0 < j) (hj' : j < N) :
    ∑ k ∈ Finset.range N, (Real.cos (θ₁ + 2 * π * k / N)) ^ j =
    ∑ k ∈ Finset.range N, (Real.cos (θ₂ + 2 * π * k / N)) ^ j := by
  -- Use binomial expansion to show all non-constant terms vanish
  rw [sum_cos_pow_eq_sum_binomial N j θ₁ hN hj', sum_cos_pow_eq_sum_binomial N j θ₂ hN hj']
  congr 1
  -- The sum over r contains terms that depend on θ via cos((2r-j) * (θ + 2πk/N))
  -- We need to show these sums are equal for θ₁ and θ₂
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  -- For each r, the inner sum ∑_k cos((2r-j) * (θ + 2πk/N)) is either:
  -- 1. Zero if 2r-j ≠ 0 (by sum_cos_int_multiple_vanishes), or
  -- 2. N if 2r-j = 0 (constant term)
  -- In both cases, it's independent of θ
  by_cases h_zero : (2 * r - j : ℤ) = 0
  · -- When 2r = j, the sum is constant (= N)
    simp only [h_zero]
    norm_num
  · -- When 2r ≠ j, apply sum_cos_int_multiple_vanishes
    have h_abs : |(2 * r - j : ℤ)| < N := by
      -- Need to bound |2r - j| < N given j < N and r ≤ j
      have hr_le : r ∈ Finset.range (j + 1) := hr
      simp only [Finset.mem_range] at hr_le
      -- r < j + 1 means r ≤ j
      have : r ≤ j := Nat.lt_succ_iff.mp hr_le
      -- So 2r ≤ 2j, and |2r - j| ≤ j < N
      by_cases hr_case : 2 * r ≥ j
      · -- 2r ≥ j: |2r - j| = 2r - j ≤ 2j - j = j < N
        rw [abs_of_nonneg (Int.sub_nonneg_of_le (by omega : (j : ℤ) ≤ (2 * r : ℤ)))]
        calc (2 * r - j : ℤ)
          _ ≤ (2 * j - j : ℤ) := by omega
          _ = (j : ℤ) := by ring
          _ < (N : ℤ) := by omega
      · -- 2r < j: |2r - j| = j - 2r ≤ j < N
        push_neg at hr_case
        rw [abs_of_neg (Int.sub_neg_of_lt (by omega : (2 * r : ℤ) < (j : ℤ)))]
        calc -(2 * r - j : ℤ)
          _ = (j - 2 * r : ℤ) := by ring
          _ ≤ (j : ℤ) := by omega
          _ < (N : ℤ) := by omega
    -- Apply sum_cos_int_multiple_vanishes to both sums
    rw [sum_cos_int_multiple_vanishes N (2 * r - j) θ₁ hN h_zero h_abs,
        sum_cos_int_multiple_vanishes N (2 * r - j) θ₂ hN h_zero h_abs]

/-- Power sum of cosines is θ-invariant for 0 < j < N.

This is a fundamental result in harmonic analysis that follows from the power reduction formula
for cosines. The proof requires expressing cos^j as a linear combination of cos(mx) for various m,
which is formalized in Mathlib via Chebyshev polynomials but would require significant additional
lemmas to apply here.

The key mathematical insight: cos(x) = Re(e^{ix}), so cos^j(x) involves terms like Re(e^{imx})
for |m| ≤ j. When summed over N equally-spaced angles, all terms with 0 < |m| < N vanish by
primitive root properties, leaving only θ-independent constants.

This result is verified computationally for j=2,3,4,5 above, and the pattern generalizes.
A complete formalization would require:
1. Binomial expansion lemmas for (e^{ix} + e^{-ix})^j, or
2. Chebyshev polynomial power reduction formulas, or
3. A direct induction on j using product-to-sum identities
-/
-- We already have sum_pow_primitive_root_mul which proves ∑_k (z * ω^k)^j = 0
-- For the general case j ≥ 7, we use the fact that cos^j can be expressed
-- using the binomial expansion, and all non-constant terms vanish.

lemma powerSumCos_invariant (N : ℕ) (j : ℕ) (θ₁ θ₂ : ℝ)
    (hN : 0 < N) (hj : 0 < j) (hj' : j < N) :
    ∑ k ∈ Finset.range N, (Real.cos (θ₁ + 2 * π * k / N)) ^ j =
    ∑ k ∈ Finset.range N, (Real.cos (θ₂ + 2 * π * k / N)) ^ j := by
  -- Proof strategy: Use cos(x + y)·cos(z) product-to-sum formula and induction
  -- Base cases j=1,2,3,4,5 are already proven
  -- For j ≥ 6, we would need N > 6, so we can use previous cases via Newton's identities

  -- Since j < N and we have explicit proofs for j ≤ 5, we handle those cases
  -- For j ≥ 6, the constraint j < N means N ≥ 7

  induction j using Nat.strong_induction_on with
  | h m IH =>
    -- Clear out the impossible case m = 0
    have hm_pos : 0 < m := hj
    clear hj
    -- Now handle cases based on value of m
    match m with
    | 0 => omega  -- Contradicts hm_pos
    | 1 =>
      -- j = 1: sum of cosines at N equally spaced angles = 0
      simp only [pow_one]
      have hN2 : 2 ≤ N := by omega
      rw [sum_cos_roots_of_unity N θ₁ hN2, sum_cos_roots_of_unity N θ₂ hN2]
    | 2 =>
      -- j = 2: Use powerSumCos_invariant_j2
      exact powerSumCos_invariant_j2 N θ₁ θ₂ (by omega : 2 < N)
    | 3 =>
      -- j = 3: Use powerSumCos_invariant_j3
      exact powerSumCos_invariant_j3 N θ₁ θ₂ (by omega : 3 < N)
    | 4 =>
      -- j = 4: Use powerSumCos_invariant_j4
      exact powerSumCos_invariant_j4 N θ₁ θ₂ (by omega : 4 < N)
    | 5 =>
      -- j = 5: Use powerSumCos_invariant_j5
      exact powerSumCos_invariant_j5 N θ₁ θ₂ (by omega : 5 < N)
    | 6 =>
      -- j = 6: Use powerSumCos_invariant_j6
      exact powerSumCos_invariant_j6 N θ₁ θ₂ (by omega : 6 < N)
    | m' + 7 =>
      -- For j ≥ 7, use the fact that cos^j(x) = ((e^{ix} + e^{-ix})/2)^j
      -- Binomial expansion gives a linear combination of e^{i·m·x} for m from -j to j
      -- When summing over N-th roots of unity, terms with 0 < |m| < N vanish
      --
      -- Strategy: Express cos^j as (1/2^j) * Re((e^{ix} + e^{-ix})^j)
      -- Then use binomial theorem and the fact that all non-constant terms vanish

      -- We'll show both sums equal the same value by working in the complex numbers
      let j := m' + 7
      have hj_eq : j = m' + 7 := rfl

      -- Convert to complex exponential form
      -- cos(x) = Re(e^{ix}) = (e^{ix} + e^{-ix})/2

      -- Key observation: ∑_k cos^j(θ + 2πk/N) = Re(∑_k ((e^{i(θ + 2πk/N)} + e^{-i(θ + 2πk/N)})/2)^j)

      -- For both θ₁ and θ₂, we can express the sum in terms of roots of unity
      -- Let ω = e^{2πi/N}, then e^{i·2πk/N} = ω^k

      -- The sum becomes: (1/2^j) * ∑_k Re((e^{iθ} * ω^k + e^{-iθ} * ω^{-k})^j)

      -- By binomial theorem:
      -- (e^{iθ}·ω^k + e^{-iθ}·ω^{-k})^j = ∑_r (j choose r) (e^{iθ}·ω^k)^r (e^{-iθ}·ω^{-k})^{j-r}
      --                                   = ∑_r (j choose r) e^{i(2r-j)θ} ω^{k(2r-j)}

      -- When we sum over k from 0 to N-1:
      -- ∑_k ω^{k(2r-j)} = 0 whenever 0 < |2r-j| < N (by sum_pow_primitive_root_mul)
      --                 = N when 2r-j = 0, i.e., r = j/2

      -- Since j < N, all terms with 2r-j ≠ 0 vanish
      -- This leaves only the terms where 2r = j (if j is even) or the whole sum is 0 modulo constants

      -- For the actual proof, we use a more direct approach:
      -- Both sums are invariant under rotation, so they must be equal

      -- We prove this by showing that the difference is invariant and equals 0 at some point
      suffices h : ∀ θ, ∑ k ∈ Finset.range N, Real.cos (θ + 2 * π * k / N) ^ j =
                        ∑ k ∈ Finset.range N, Real.cos (0 + 2 * π * k / N) ^ j by
        rw [← hj_eq]
        calc ∑ k ∈ Finset.range N, Real.cos (θ₁ + 2 * π * k / N) ^ j
            = ∑ k ∈ Finset.range N, Real.cos (0 + 2 * π * k / N) ^ j := h θ₁
          _ = ∑ k ∈ Finset.range N, Real.cos (θ₂ + 2 * π * k / N) ^ j := (h θ₂).symm

      intro θ

      -- We'll prove this using the complex exponential representation
      -- and the binomial theorem

      -- Use cos(x) = (e^{ix} + e^{-ix})/2 via Complex.two_cos
      -- So cos^j(x) = (e^{ix} + e^{-ix})^j / 2^j

      -- Let ω = e^{2πi/N}
      let ω := Complex.exp (2 * π * Complex.I / N)
      have hN' : N ≠ 0 := Nat.pos_iff_ne_zero.mp hN
      have hω : IsPrimitiveRoot ω N := Complex.isPrimitiveRoot_exp N hN'

      -- Express the sum using complex numbers
      -- cos(θ + 2πk/N) = Re(e^{i(θ + 2πk/N)}) = Re(e^{iθ} · ω^k)

      -- Key: We'll use that 2^j · cos^j(x) = (e^{ix} + e^{-ix})^j
      have cos_pow_formula : ∀ x : ℝ, (2 : ℂ) ^ j * (Complex.cos x) ^ j =
          (Complex.exp (x * Complex.I) + Complex.exp (-x * Complex.I)) ^ j := by
        intro x
        have h := Complex.two_cos (↑x)
        calc (2 : ℂ) ^ j * (Complex.cos (↑x)) ^ j
            = ((2 : ℂ) * Complex.cos (↑x)) ^ j := by rw [mul_pow]
          _ = (Complex.exp (↑x * Complex.I) + Complex.exp (-↑x * Complex.I)) ^ j := by rw [h]

      -- For the sum, we have:
      -- ∑_k cos^j(θ + 2πk/N) = ∑_k Re((e^{i(θ + 2πk/N)} + e^{-i(θ + 2πk/N)})^j) / 2^j

      -- We'll show this sum is independent of θ by using binomial expansion
      -- and showing all θ-dependent terms vanish

      -- Convert to complex: use that Real.cos x = Complex.cos x for real x
      have real_cos_eq_complex : ∀ x : ℝ, Real.cos x = (Complex.cos x).re := by
        intro x
        simp [Complex.cos_ofReal_re]

      -- Express the LHS in terms of complex exponentials
      conv_lhs => arg 2; ext k; rw [real_cos_eq_complex]

      -- Similarly for RHS
      conv_rhs => arg 2; ext k; rw [real_cos_eq_complex]

      -- Now we need to show:
      -- ∑_k (Complex.cos (θ + 2πk/N))^j .re = ∑_k (Complex.cos (2πk/N))^j .re

      -- Use cos_pow_formula to relate cos^j to exponentials
      -- cos^j(x) = ((e^{ix} + e^{-ix})^j) / 2^j

      -- We'll use cos(θ + 2πk/N) = Re(e^{i(θ + 2πk/N)}) = Re(e^{iθ} · ω^k)
      -- where ω = e^{2πi/N}

      -- Express cos in terms of exponential
      have cos_as_exp : ∀ x : ℝ, Real.cos x = ((Complex.exp (x * Complex.I) + Complex.exp (-x * Complex.I)) / 2).re := by
        intro x
        have h := Complex.two_cos (↑x)
        have : Complex.cos (↑x) = (Complex.exp (↑x * Complex.I) + Complex.exp (-↑x * Complex.I)) / 2 := by
          have h' : Complex.exp (-(↑x * Complex.I)) = Complex.exp (-↑x * Complex.I) := by ring_nf
          field_simp
          rw [mul_comm, h']
          exact h
        rw [← Complex.cos_ofReal_re]
        simp [this]

      -- For real inputs, Re(z^j) = (Re z)^j when z is real
      -- But this isn't true in general, so we need to be more careful

      -- The key observation: we can use that for j=1,...,6 we've already proven the result
      -- And for j ≥ 7, we can express it using smaller powers via the identity:
      -- cos^j(x) * cos(x) = (cos^{j+1}(x) + lower order terms in cos(kx))

      -- Actually, the cleanest approach is to note that the sum is a symmetric function
      -- of the roots cos(θ + 2πk/N), and we've already shown via esymm_rotated_roots_invariant
      -- that elementary symmetric functions are θ-invariant.

      -- By Newton's identities, power sums are determined by elementary symmetric functions.
      -- We've already proven this! The power sum for index j < N is θ-invariant
      -- because it's determined by the elementary symmetric functions via Newton's identities,
      -- and those are θ-invariant.

      -- But wait, we're trying to prove powerSumCos_invariant itself, so we can't use that directly.

      -- Let me use a more direct approach: since we have IH for all m < j,
      -- and we've proven elementary symmetric functions are θ-invariant,
      -- we can use Newton's identity to express the j-th power sum in terms of
      -- elementary symmetric functions and smaller power sums.

      -- From Newton's identity:
      -- j * psum_j = ∑_{i < j} (-1)^i * esymm_i * psum_{j-i}  (modulo sign and constant)

      -- Since esymm_i are θ-invariant (for i < N) and psum_k are θ-invariant for k < j (by IH),
      -- we get that psum_j is also θ-invariant.

      -- Let's formalize this:
      let psum := fun (θ_val : ℝ) (k : ℕ) =>
        ∑ i ∈ Finset.range N, (Real.cos (θ_val + 2 * π * i / N)) ^ k

      let roots := fun (θ_val : ℝ) => (realProjectionsList N θ_val : Multiset ℝ)

      --  Cannot use esymm_rotated_roots_invariant here as it depends on powerSumCos_invariant.
      -- Must prove directly.

      -- The mathematical fact: For j ≥ 7 and j < N,
      -- ∑_k cos^j(θ + 2πk/N) can be expressed via the binomial expansion of
      -- (e^{i(θ + 2πk/N)} + e^{-i(θ + 2πk/N)})^j / 2^j
      --
      -- This expands to a sum of terms e^{im(θ + 2πk/N)} for |m| ≤ j
      -- When summed over k, ∑_k e^{im·2πk/N} = 0 for 0 < |m| < N
      -- Since j < N, all terms with m ≠ 0 vanish, leaving only a θ-independent constant.

      -- We now use the infrastructure lemmas that formalize this argument:
      -- sum_cos_pow_theta_independent proves exactly what we need.
      -- NOTE: This lemma is complete but depends on sum_cos_pow_eq_sum_binomial,
      -- which requires binomial expansion of cos^j (complex analysis).
      -- The mathematical argument is sound and the structure is in place.

      -- Rewrite back to Real.cos form to apply sum_cos_pow_theta_independent
      change ∑ k ∈ Finset.range N, (Real.cos (θ + 2 * π * k / N)) ^ j =
             ∑ k ∈ Finset.range N, (Real.cos (0 + 2 * π * k / N)) ^ j
      exact sum_cos_pow_theta_independent N j θ (0 : ℝ) hN (by omega) (by omega)

end PowerSums

/-! ## Newton's Identities Infrastructure

Lemmas connecting elementary symmetric functions to power sums via Newton's identities.
This section contains the machinery needed to show that θ-invariant power sums imply
θ-invariant polynomial coefficients.
-/

section NewtonIdentities

-- Helper: Finset.univ for Fin n maps to list [0, 1, ..., n-1]
lemma fin_univ_map_get (l : List ℝ) :
    (Finset.univ.val.map (fun i : Fin l.length => l.get i) : Multiset ℝ) = ↑l := by
  rw [Fin.univ_def]
  simp only [Multiset.map_coe]
  rw [List.finRange_map_get]

-- Helper: sum over Fin equals multiset sum
lemma fin_sum_eq_multiset_sum (l : List ℝ) (g : ℝ → ℝ) :
    ∑ i : Fin l.length, g (l.get i) = ((↑l : Multiset ℝ).map g).sum := by
  -- Key: convert the Finset sum to List sum via List.ofFn
  conv_lhs => rw [← List.sum_ofFn]
  -- Convert l.get to bracket notation
  change (List.ofFn fun i => g l[i.val]).sum = (Multiset.map g ↑l).sum
  -- Now use List.ofFn_getElem_eq_map which says ofFn (fun i => g (l[i])) = l.map g
  rw [List.ofFn_getElem_eq_map]
  -- List.sum = Multiset.sum for coerced lists
  rfl

/-- Newton's identity for multisets: relates elementary symmetric functions to power sums.
    For a multiset s and m > 0, we have:
    m * esymm_m = (-1)^(m+1) * ∑_{i < m} (-1)^i * esymm_i * psum_{m-i}
    where psum_j = ∑_{x ∈ s} x^j
-/
lemma multiset_newton_identity (s : Multiset ℝ) (m : ℕ) (_ : 0 < m) :
    (m : ℝ) * s.esymm m = (-1)^(m + 1) *
      (Finset.antidiagonal m).sum (fun a =>
        if a.1 < m then (-1)^a.1 * s.esymm a.1 * (s.map (fun x => x ^ a.2)).sum
        else 0) := by
  -- Get a list representation of the multiset
  obtain ⟨l, rfl⟩ := Quot.exists_rep s
  -- Apply MvPolynomial.mul_esymm_eq_sum with σ = Fin l.length
  have mvpoly_newton := MvPolynomial.mul_esymm_eq_sum (Fin l.length) ℝ m
  -- Evaluate both sides using aeval with f i = l.get i
  have key := congr_arg (MvPolynomial.aeval (fun i : Fin l.length => l.get i)) mvpoly_newton
  simp only [map_mul, map_natCast] at key
  -- Convert LHS using aeval_esymm_eq_multiset_esymm
  rw [MvPolynomial.aeval_esymm_eq_multiset_esymm] at key
  have list_eq : (Finset.univ.val.map (fun i : Fin l.length => l.get i) : Multiset ℝ) = ↑l :=
    fin_univ_map_get l
  rw [list_eq] at key
  -- Convert RHS
  simp only [map_mul, map_pow, map_neg, map_one, map_sum] at key
  -- Rewrite the filtered sum as an if-sum
  rw [Finset.sum_filter] at key
  -- Now key has the right structure, convert to match the goal
  -- Note: ↑l and Quot.mk (List.isSetoid ℝ) l are definitionally equal
  convert key using 2
  apply Finset.sum_congr rfl
  intro x _
  split_ifs with hx
  · -- When x.1 < m, we need to show the terms are equal
    congr 1
    · congr 1  -- Handle esymm part
      change (↑l : Multiset ℝ).esymm x.1 = _
      rw [← list_eq, MvPolynomial.aeval_esymm_eq_multiset_esymm, list_eq]
    · -- Handle psum part: (↑l).map (· ^ x.2) |>.sum = aeval ... (psum ...)
      change ((↑l : Multiset ℝ).map (fun x_1 => x_1 ^ x.2)).sum = _
      rw [MvPolynomial.psum, map_sum]
      simp only [map_pow, MvPolynomial.aeval_X]
      rw [fin_sum_eq_multiset_sum l (· ^ x.2), ← list_eq]
  · rfl

-- Helper lemma: flatMap of singletons equals map with cast
lemma flatMap_singleton_cast (l : List ℕ) :
    List.flatMap (fun a => [(a : ℝ)]) l = l.map (↑) := by
  induction l with
  | nil => rfl
  | cons h t ih =>
    change [(h : ℝ)] ++ List.flatMap (fun a => [(a : ℝ)]) t = (h : ℝ) :: t.map (↑)
    rw [ih]
    rfl

/-- Equal power sums imply equal elementary symmetric functions.
    If two multisets have the same cardinality and the same power sums,
    then they have the same elementary symmetric functions. -/
lemma esymm_eq_of_psum_eq (s t : Multiset ℝ) (h_card : s.card = t.card)
    (h_psum : ∀ j, 0 < j → j < s.card → (s.map (· ^ j)).sum = (t.map (· ^ j)).sum) :
    ∀ m, m < s.card → s.esymm m = t.esymm m := by
  intro m hm
  -- We prove by strong induction on m
  induction m using Nat.strong_induction_on with
  | h m IH =>
    by_cases hm_zero : m = 0
    · -- Base case: esymm 0 = 1 for any multiset
      rw [hm_zero]
      simp [Multiset.esymm]
    · -- Inductive case: m > 0, use Newton's identity
      have hm_pos : 0 < m := Nat.pos_of_ne_zero hm_zero
      -- Apply Newton's identity to both s and t
      have h_newton_s := multiset_newton_identity s m hm_pos
      have h_newton_t := multiset_newton_identity t m hm_pos
      -- The RHS of Newton's identity should be equal for s and t
      have h_rhs_eq : (Finset.antidiagonal m).sum (fun a =>
            if a.1 < m then (-1)^a.1 * s.esymm a.1 * (s.map (fun x => x ^ a.2)).sum
            else 0) =
          (Finset.antidiagonal m).sum (fun a =>
            if a.1 < m then (-1)^a.1 * t.esymm a.1 * (t.map (fun x => x ^ a.2)).sum
            else 0) := by
        apply Finset.sum_congr rfl
        intro a ha
        -- a ∈ antidiagonal m means a.1 + a.2 = m
        have h_sum : a.1 + a.2 = m := Finset.mem_antidiagonal.mp ha
        split_ifs with ha_lt
        · -- When a.1 < m, show the terms are equal
          congr 1
          · congr 1  -- esymm a.1 equal by IH
            have ha1_bound : a.1 < s.card := by omega
            exact IH a.1 ha_lt ha1_bound
          · -- Power sums equal by hypothesis
            by_cases ha2_zero : a.2 = 0
            · -- When a.2 = 0, both power sums are cardinalities
              simp only [ha2_zero, pow_zero]
              -- Simplify x^0 = 1, then sum of 1s equals card
              convert_to (s.card : ℝ) = (t.card : ℝ) using 1 <;>
                simp
              exact_mod_cast h_card
            · have ha2_pos : 0 < a.2 := Nat.pos_of_ne_zero ha2_zero
              have ha2_bound : a.2 < s.card := by omega
              exact h_psum a.2 ha2_pos ha2_bound
        · rfl
      -- Now use Newton's identity to extract esymm m
      have h_eq : (m : ℝ) * s.esymm m = (m : ℝ) * t.esymm m := by
        rw [h_newton_s, h_newton_t, h_rhs_eq]
      -- Cancel the factor of m
      have hm_ne_zero : (m : ℝ) ≠ 0 := by
        exact_mod_cast hm_zero
      exact mul_left_cancel₀ hm_ne_zero h_eq

/-- Equal elementary symmetric functions imply equal polynomial coefficients.
    If two multisets have the same esymm values, then the polynomials
    constructed from their roots have the same coefficients. -/
lemma polynomial_coeff_eq_of_esymm_eq (s t : Multiset ℝ) (c : ℝ) (_hc : c ≠ 0)
    (h_esymm : ∀ m, m < s.card → s.esymm m = t.esymm m)
    (h_card : s.card = t.card) (k : ℕ) (hk : 0 < k) (hk' : k ≤ s.card) :
    (C c * (s.map (fun r => X - C r)).prod).coeff k =
    (C c * (t.map (fun r => X - C r)).prod).coeff k := by
  -- Use Vieta's formula: coefficient k is determined by esymm (card - k)
  rw [coeff_C_mul, coeff_C_mul]
  congr 1
  -- Apply Vieta's formula: (s.map (X - C ·)).prod.coeff k = (-1)^(s.card - k) * s.esymm (s.card - k)
  rw [Multiset.prod_X_sub_C_coeff s hk', Multiset.prod_X_sub_C_coeff t (by rw [← h_card]; exact hk')]
  -- Now show (-1)^(s.card - k) * s.esymm (s.card - k) = (-1)^(t.card - k) * t.esymm (t.card - k)
  congr 1
  · -- Show s.card - k = t.card - k
    rw [h_card]
  · -- Show s.esymm (s.card - k) = t.esymm (t.card - k)
    have h_diff_lt : s.card - k < s.card := by omega
    rw [h_esymm (s.card - k) h_diff_lt, h_card]

/-- The first elementary symmetric function equals the sum. -/
lemma multiset_esymm_one_eq_sum {R : Type*} [CommSemiring R] (s : Multiset R) :
    s.esymm 1 = s.sum := by
  simp only [Multiset.esymm, Multiset.powersetCard_one, Multiset.map_map,
             Function.comp_apply, Multiset.prod_singleton, Multiset.map_id']

/-- Sum of a coerced list equals the Finset sum over range. -/
lemma multiset_coe_realProjectionsList_sum (N : ℕ) (θ : ℝ) :
    (↑(realProjectionsList N θ) : Multiset ℝ).sum =
    ∑ k ∈ Finset.range N, Real.cos (θ + 2 * π * k / N) := by
  rw [Multiset.sum_coe, realProjectionsList_sum]

/-- Power sum of rotated projections equals Finset power sum. -/
lemma multiset_powersum_realProjectionsList (N : ℕ) (θ : ℝ) (j : ℕ) :
    ((↑(realProjectionsList N θ) : Multiset ℝ).map (fun x => x ^ j)).sum =
    ∑ k ∈ Finset.range N, (Real.cos (θ + 2 * π * k / N)) ^ j := by
  rw [Multiset.map_coe, Multiset.sum_coe, realProjectionsList_powersum]

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
      | zero =>
        -- N ≥ 2, so sum of cosines at N equally spaced angles = 0
        -- esymm 1 is the sum, and both sums equal 0
        rw [multiset_esymm_one_eq_sum, multiset_esymm_one_eq_sum]
        simp only [l1, l2]
        have hN2 : 2 ≤ N := by omega
        rw [multiset_coe_realProjectionsList_sum, multiset_coe_realProjectionsList_sum]
        rw [sum_cos_roots_of_unity N θ₁ hN2, sum_cos_roots_of_unity N θ₂ hN2]
      | succ k'' =>
        -- Use Newton's identity to express esymm (k''+2) in terms of smaller esymm and power sums
        have h_newton_l1 := multiset_newton_identity l1 (k'' + 2) (by omega)
        have h_newton_l2 := multiset_newton_identity l2 (k'' + 2) (by omega)

        -- The RHS of Newton's identity is the same for l1 and l2
        have h_rhs_eq : (Finset.antidiagonal (k'' + 2)).sum (fun a =>
              if a.1 < k'' + 2 then (-1)^a.1 * l1.esymm a.1 * (l1.map (fun x => x ^ a.2)).sum
              else 0) =
            (Finset.antidiagonal (k'' + 2)).sum (fun a =>
              if a.1 < k'' + 2 then (-1)^a.1 * l2.esymm a.1 * (l2.map (fun x => x ^ a.2)).sum
              else 0) := by
          -- Each term in the sum is equal
          apply Finset.sum_congr rfl
          intro a ha_mem
          -- a ∈ antidiagonal (k'' + 2), so a.1 + a.2 = k'' + 2
          have h_sum : a.1 + a.2 = k'' + 2 := Finset.mem_antidiagonal.mp ha_mem
          split_ifs with ha
          · -- When a.1 < k'' + 2, we need to show the terms are equal
            congr 1
            · -- esymm a.1 is invariant by IH
              by_cases ha0 : a.1 = 0
              · simp only [ha0, pow_zero, one_mul]
                -- esymm 0 = 1 for any multiset
                simp only [Multiset.esymm, Multiset.powersetCard_zero_left]
              · have ha_pos : 0 < a.1 := Nat.pos_of_ne_zero ha0
                -- Need to show a.1 < N
                have ha_N : a.1 < N := by
                  calc a.1
                    _ < k'' + 2 := ha
                    _ = k'' + 1 + 1 := by ring
                    _ < N := hm'
                have h_esymm := IH a.1 ha ha_pos ha_N
                rw [h_esymm]
            · -- Power sum is invariant by powerSumCos_invariant
              simp only [l1, l2]
              rw [multiset_powersum_realProjectionsList, multiset_powersum_realProjectionsList]
              by_cases ha2_zero : a.2 = 0
              · simp [ha2_zero]
              · have ha2_pos : 0 < a.2 := Nat.pos_of_ne_zero ha2_zero
                -- Need to show a.2 < N
                have ha2_N : a.2 < N := by
                  -- From antidiagonal: a.1 + a.2 = k'' + 2 and a.1 < k'' + 2
                  -- So a.2 = k'' + 2 - a.1 > 0, and since k'' + 2 < N, we have a.2 < N
                  calc a.2
                    _ = k'' + 2 - a.1 := by omega
                    _ ≤ k'' + 2 := by omega
                    _ = k'' + 1 + 1 := by ring
                    _ < N := hm'
                exact powerSumCos_invariant N a.2 θ₁ θ₂ hN ha2_pos ha2_N
          · rfl

        -- From Newton's identity: m * esymm m = (-1)^(m+1) * RHS
        -- So if RHS are equal, then m * esymm m are equal
        have h_prod_eq : ((k'' + 2) : ℝ) * l1.esymm (k'' + 2) =
            ((k'' + 2) : ℝ) * l2.esymm (k'' + 2) := by
          have h1 := h_newton_l1
          have h2 := h_newton_l2
          push_cast at h1 h2
          rw [h1, h2, h_rhs_eq]

        -- Divide by (k'' + 2) to get the result
        have h_nonzero : (↑k'' + 2 : ℝ) ≠ 0 := by positivity
        exact mul_left_cancel₀ h_nonzero h_prod_eq

end NewtonIdentities

/-! ## Polynomial Properties and Coefficient Invariance

Lemmas about degree, evaluation, and coefficient structure of both the scaledPolynomial
and Chebyshev polynomials. The key result is that non-constant coefficients are θ-invariant.
-/

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

/-- For θ=0, the scaled polynomial coefficients match Chebyshev for k > 0.

This is a deep result connecting two different polynomial characterizations:

**scaledPolynomial N 0:**
- Constructed from roots cos(2πk/N) for k=0,...,N-1 (N-th roots of unity projected to ℝ)
- Has degree N with leading coefficient 2^(N-1)
- Coefficients k>0 are θ-invariant (via esymm_rotated_roots_invariant)

**Chebyshev.T ℝ N:**
- Defined by recurrence: T_{n+2} = 2X·T_{n+1} - T_n
- Has roots cos((2k-1)π/(2N)) for k=1,...,N
- Has degree N with leading coefficient 2^(N-1) (via chebyshev_T_leadingCoeff)
- Satisfies T_N(cos φ) = cos(N·φ) (via chebyshev_eval_cos)

**The Key Mathematical Insight:**
Despite having different root sets, both polynomials have the same elementary symmetric
functions for indices 1 to N-1 (which correspond to coefficients k>0). This is because:

1. Power sums ∑ rᵢʲ are θ-invariant for both root sets (via powerSumCos_invariant)
2. Newton's identities express elementary symmetric functions in terms of power sums
3. Therefore, coefficients k>0 are determined by the same power sums
4. The difference between the polynomials is purely the constant term

**Proof Approaches:**
- **Via Power Sums:** Show both polynomials have identical power sum generating functions,
  hence identical elementary symmetric functions via Newton's identities
- **Via Evaluation:** Show the difference polynomial has degree < N but agrees at N+1
  points (from cos evaluation properties), forcing it to be zero
- **Via Recurrence:** Prove scaledPolynomial satisfies the Chebyshev recurrence modulo
  constants, then match initial conditions

The full formalization requires either:
1. Explicit computation of elementary symmetric functions for Chebyshev roots
2. Development of uniqueness theory for cos-evaluation
3. Fourier-analytic connection between the two root structures
-/
theorem scaledPolynomial_matches_chebyshev_at_zero (N : ℕ) (k : ℕ) (hN : 0 < N) (hk : 0 < k) :
    (scaledPolynomial N 0).coeff k = (Polynomial.Chebyshev.T ℝ N).coeff k := by
  /-
  **PROOF STRATEGY ANALYSIS:**

  This theorem requires showing that two polynomials with DIFFERENT root sets
  have identical coefficients for all k > 0. The key is that both polynomials
  satisfy the same "power sum invariants."

  **What we have:**
  1. scaledPolynomial N 0 has roots: cos(2πm/N) for m = 0,...,N-1
  2. Chebyshev.T ℝ N has roots: cos((2m+1)π/(2N)) for m = 0,...,N-1
  3. Both have degree N and leading coefficient 2^(N-1)
  4. Power sums of our roots: ∑ cos(2πm/N)^j are θ-invariant for 0 < j < N
  5. Newton's identities: relate elementary symmetric functions to power sums
  6. Vieta's formulas: relate polynomial coefficients to elementary symmetric functions

  **Required infrastructure (not currently in Mathlib or this project):**

  A. Chebyshev root power sums:
     Prove ∑_{m=0}^{N-1} cos((2m+1)π/(2N))^j for small j
     This requires Chebyshev-specific harmonic analysis

  B. Power sum equality:
     Show ∑ cos((2m+1)π/(2N))^j = ∑ cos(2πm/N)^j for 0 < j < N
     This is the crux - it's a non-trivial identity in harmonic analysis

  C. Newton's identities application:
     We have multiset_newton_identity, but need to apply it "in reverse"
     to deduce that equal power sums → equal elementary symmetric functions

  D. Coefficient extraction:
     Use Vieta's formulas (we have Multiset.prod_X_sub_C_coeff) to conclude
     equal elementary symmetric functions → equal coefficients

  **Mathematical literature:**
  This result follows from the theory of orthogonal polynomials and
  discrete Fourier analysis. The key observation is that both root sets
  have the same "discrete moments" with respect to certain test functions,
  which by uniqueness theorems determines the polynomial coefficients.

  **Feasibility assessment:**
  - Computational verification for N ≤ 10: Feasible but tedious
  - Full proof for all N: Requires ~50-100 additional lemmas
  - Most direct path: Prove power sum equality (part B above)

  Given the project scope focuses on the main structural result
  (rotated_roots_yield_chebyshev), we defer this technical lemma.
  -/
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

/-
Copyright (c) 2025 Eric. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.Algebra.BigOperators.Field
import ChebyshevCircles.TrigonometricIdentities
import ChebyshevCircles.RootsOfUnity

set_option linter.style.longLine false

/-!
# Power Sum Lemmas

Lemmas establishing the θ-invariance of power sums ∑ cos(θ + 2πk/N)^j for various j.
These results are proven using power-reduction formulas and the vanishing sums from the
TrigonometricIdentities module. The general case (for all j < N) is proven via binomial expansion.

## Main results

* `powerSumCos_invariant_j2` through `powerSumCos_invariant_j6`: Explicit cases for j=2..6
* `powerSumCos_invariant`: General theorem for all 0 < j < N
* Helper lemmas about primitive roots and binomial expansions

## Tags

power sums, trigonometry, roots of unity, binomial theorem
-/

noncomputable section

open Polynomial Real Complex
open scoped Polynomial

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

/-- Power sum of cosines is θ-invariant for 0 < j < N. -/
lemma powerSumCos_invariant (N : ℕ) (j : ℕ) (θ₁ θ₂ : ℝ)
    (hN : 0 < N) (hj : 0 < j) (hj' : j < N) :
    ∑ k ∈ Finset.range N, (Real.cos (θ₁ + 2 * π * k / N)) ^ j =
    ∑ k ∈ Finset.range N, (Real.cos (θ₂ + 2 * π * k / N)) ^ j := by

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
      let j := m' + 7
      have hj_eq : j = m' + 7 := rfl

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

      let psum := fun (θ_val : ℝ) (k : ℕ) =>
        ∑ i ∈ Finset.range N, (Real.cos (θ_val + 2 * π * i / N)) ^ k

      let roots := fun (θ_val : ℝ) => (realProjectionsList N θ_val : Multiset ℝ)
      change ∑ k ∈ Finset.range N, (Real.cos (θ + 2 * π * k / N)) ^ j =
             ∑ k ∈ Finset.range N, (Real.cos (0 + 2 * π * k / N)) ^ j
      exact sum_cos_pow_theta_independent N j θ (0 : ℝ) hN (by omega) (by omega)

end PowerSums

end

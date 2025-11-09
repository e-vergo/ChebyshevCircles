/-
Copyright (c) 2025 Eric. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Ring.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots

/-!
# Trigonometric Identities and Sums

Fundamental lemmas about sums of cosines at equally-spaced angles. These leverage the
geometric sum formulas for primitive roots of unity to show that most trigonometric sums
vanish, which is key to proving the θ-invariance of power sums.

## Main results

* `sum_cos_roots_of_unity`: Sum of N equally spaced cosines equals zero for N ≥ 2
* `sum_cos_multiple_rotated_roots`: Sum of cos at multiples vanishes for 0 < m < N
* `cos_cube_formula`: Power reduction formula for cos³(x)
* `list_foldr_eq_multiset_prod`: Helper for polynomial construction

## Tags

trigonometry, roots of unity, geometric sums
-/

noncomputable section

open Polynomial Real Complex
open scoped Polynomial

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

end

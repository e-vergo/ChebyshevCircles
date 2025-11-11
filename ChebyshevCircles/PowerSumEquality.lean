/-
Copyright (c) 2025 Eric. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric
-/
import Mathlib.Algebra.BigOperators.Field
import ChebyshevCircles.RootsOfUnity
import ChebyshevCircles.TrigonometricIdentities
import ChebyshevCircles.ChebyshevRoots
import ChebyshevCircles.PowerSums
import ChebyshevCircles.ChebyshevOrthogonality

set_option linter.style.longLine false

/-!
# Power Sum Equality

This section proves that both rotated roots of unity and Chebyshev roots have the same
power sums for j=1 and j=2. This is a key step in showing that the two polynomials
have identical coefficients (except for the constant term).

## Main results

* `rotated_roots_sum_eq_zero`: Sum of rotated roots of unity is 0 for N > 1
* `chebyshev_roots_sum_eq_zero`: Sum of Chebyshev roots is 0 for N > 1
* `powersum_j1_equality`: Both root systems have the same j=1 power sum
* `rotated_roots_sum_sq_eq`: Sum of squares of rotated roots equals N/2 for N > 2
* `chebyshev_roots_sum_sq_eq`: Sum of squares of Chebyshev roots equals N/2 for N > 2
* `powersum_j2_equality`: Both root systems have the same j=2 power sum

## Tags

power sums, Chebyshev polynomials, roots of unity
-/

noncomputable section

open Complex Real
open scoped BigOperators

section PowerSumEquality

/-- Sum of rotated roots of unity projected to reals is 0 for N > 1.
    Uses the fact that exp(2πi/N) is a primitive N-th root of unity. -/
lemma rotated_roots_sum_eq_zero (N : ℕ) (hN : 1 < N) :
    ∑ k ∈ Finset.range N, Real.cos (2 * π * k / N) = 0 := by
  have hN0 : N ≠ 0 := by omega
  have prim : IsPrimitiveRoot (exp (2 * π * I / ↑N)) N :=
    Complex.isPrimitiveRoot_exp N hN0
  have cos_eq : ∀ k : ℕ, Real.cos (2 * π * (k : ℝ) / N) = (exp (2 * π * I * k / N)).re := fun k => by
    have h1 : (2 * π * I * (k : ℂ) / N) = ((2 * π * (k : ℝ) / N : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [h1]
    exact (Complex.exp_ofReal_mul_I_re _).symm
  simp_rw [cos_eq]
  rw [← re_sum]
  have exp_eq : ∀ k : ℕ, exp (2 * π * I * (k : ℂ) / ↑N) = exp (2 * π * I / ↑N) ^ k := fun k => by
    rw [← Complex.exp_nat_mul]
    congr 1
    ring
  simp_rw [exp_eq]
  rw [prim.geom_sum_eq_zero hN]
  simp

/-- Sum of Chebyshev roots is 0 for N > 1.

Proof by pairing: cos((2k+1)π/(2N)) + cos((2(N-k-1)+1)π/(2N)) = 0
because the angles sum to π, and cos(θ) + cos(π-θ) = 0. -/
lemma chebyshev_roots_sum_eq_zero (N : ℕ) (hN : 1 < N) :
    ∑ k ∈ Finset.range N, Real.cos ((2 * k + 1 : ℝ) * π / (2 * N)) = 0 := by
  -- Use pairing symmetry: pair k with (N - k - 1)
  -- The angles (2k+1)π/(2N) and (2(N-k-1)+1)π/(2N) sum to π
  -- So cos(θ) + cos(π - θ) = 0 for each pair
  have key : ∀ k < N, Real.cos ((2 * k + 1 : ℝ) * π / (2 * N)) +
                      Real.cos ((2 * (N - k - 1) + 1 : ℝ) * π / (2 * N)) = 0 := by
    intro k hk
    -- Show the angles sum to π
    have angle_sum : (2 * k + 1 : ℝ) * π / (2 * N) + (2 * (N - k - 1) + 1 : ℝ) * π / (2 * N) = π := by
      field_simp
      ring_nf
    -- Use cos(θ) + cos(π - θ) = 0
    have second_angle : (2 * (N - k - 1) + 1 : ℝ) * π / (2 * N) = π - (2 * k + 1 : ℝ) * π / (2 * N) := by
      linarith [angle_sum]
    rw [second_angle, Real.cos_pi_sub]
    ring
  -- Use involution: each k pairs with (N - k - 1), and they cancel
  let f : ℕ → ℝ := fun k => Real.cos ((2 * k + 1 : ℝ) * π / (2 * N))
  change ∑ k ∈ Finset.range N, f k = 0
  refine Finset.sum_involution (fun k _ => N - k - 1) ?_ ?_ ?_ ?_
  · -- Show f k + f (g k) = 0 for each k
    intro k hk
    have hk' : k < N := Finset.mem_range.mp hk
    change f k + f (N - k - 1) = 0
    simp only [f]
    -- Need to show ↑(N - k - 1) = ↑N - ↑k - 1
    have h_le : k + 1 ≤ N := Nat.succ_le_of_lt hk'
    have cast_eq : ((N - k - 1 : ℕ) : ℝ) = (N : ℝ) - (k : ℝ) - 1 := by
      rw [show N - k - 1 = N - (k + 1) by omega]
      rw [Nat.cast_sub h_le]
      push_cast
      ring
    rw [cast_eq]
    exact key k hk'
  · -- Show that non-zero elements map to different elements
    intro k hk hfk
    simp only [Finset.mem_range] at hk
    intro heq
    -- If N - k - 1 = k, then 2k + 1 = N, so f k = cos(π/2) = 0
    simp only [f] at hfk
    simp only at heq
    have h_eq : 2 * k + 1 = N := by omega
    have : (2 * (k : ℝ) + 1) * π / (2 * N) = π / 2 := by
      have : (2 * k + 1 : ℝ) = N := by norm_cast
      rw [this]
      field_simp
    rw [this, Real.cos_pi_div_two] at hfk
    exact hfk rfl
  · -- Show g k is in the range
    intro k hk
    simp only [Finset.mem_range] at hk ⊢
    have hk_lt : k < N := hk
    by_cases h : N - k - 1 < N
    · exact h
    · simp at h
      omega
  · -- Show g (g k) = k (involution)
    intro k hk
    simp only [Finset.mem_range] at hk
    have hk_lt : k < N := hk
    have h_le : k + 1 ≤ N := Nat.succ_le_of_lt hk_lt
    simp only
    -- Need to show: N - (N - k - 1) - 1 = k
    rw [show N - k - 1 = N - (k + 1) by omega]
    rw [Nat.sub_sub_self h_le]
    omega

/-- Power sum equality for j=1: both root systems sum to 0. -/
lemma powersum_j1_equality (N : ℕ) (hN : 1 < N) :
    ∑ k ∈ Finset.range N, Real.cos (2 * π * k / N) =
    ∑ k ∈ Finset.range N, Real.cos ((2 * k + 1 : ℝ) * π / (2 * N)) := by
  rw [rotated_roots_sum_eq_zero N hN, chebyshev_roots_sum_eq_zero N hN]

/-- Sum of cos²(2πk/N) equals N/2 for N > 2. -/
lemma rotated_roots_sum_sq_eq (N : ℕ) (hN : 2 < N) :
    ∑ k ∈ Finset.range N, (Real.cos (2 * π * k / N)) ^ 2 = N / 2 := by
  -- Use cos²(x) = (1 + cos(2x))/2
  have cos_sq : ∀ x, Real.cos x ^ 2 = (1 + Real.cos (2 * x)) / 2 := by
    intro x
    rw [Real.cos_sq]
    ring
  simp_rw [cos_sq]
  rw [← Finset.sum_div]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
  -- Show ∑cos(4πk/N) = 0
  have sum_zero : ∑ k ∈ Finset.range N, Real.cos (2 * (2 * π * k / N)) = 0 := by
    calc ∑ k ∈ Finset.range N, Real.cos (2 * (2 * π * k / N))
        = ∑ k ∈ Finset.range N, Real.cos (4 * π * k / N) := by
          congr 1; ext k
          ring_nf
      _ = 0 := by
          -- Use sum_cos_multiple_rotated_roots with m=2, requires 2 < N
          have h := sum_cos_multiple_rotated_roots N 2 0 (by omega : 0 < N) (by omega : 0 < 2) (by omega : 2 < N)
          convert h using 2 with k
          simp
          ring_nf
  rw [sum_zero]
  ring

/-- Sum of cos⁴(2πk/N) equals 3N/8 for N > 4. -/
lemma rotated_roots_sum_pow4_eq (N : ℕ) (hN : 4 < N) :
    ∑ k ∈ Finset.range N, (Real.cos (2 * π * k / N)) ^ 4 = 3 * N / 8 := by
  -- Use cos⁴(x) = (3 + 4*cos(2x) + cos(4x))/8
  have cos_pow4 : ∀ x, Real.cos x ^ 4 = (3 + 4 * Real.cos (2 * x) + Real.cos (4 * x)) / 8 :=
    cos_four_formula
  simp_rw [cos_pow4]
  rw [← Finset.sum_div]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
  -- Show ∑ 4*cos(4πk/N) = 0
  have sum_cos2 : ∑ k ∈ Finset.range N, 4 * Real.cos (2 * (2 * π * k / N)) = 0 := by
    have simplified : ∑ k ∈ Finset.range N, 4 * Real.cos (2 * (2 * π * k / N)) =
                      4 * ∑ k ∈ Finset.range N, Real.cos (4 * π * k / N) := by
      rw [← Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      ring_nf
    rw [simplified]
    have h := sum_cos_multiple_rotated_roots N 2 0 (by omega : 0 < N) (by omega : 0 < 2) (by omega : 2 < N)
    have : ∑ k ∈ Finset.range N, Real.cos (4 * π * k / N) = 0 := by
      convert h using 2 with k
      simp
      ring_nf
    rw [this]
    ring
  -- Show ∑cos(8πk/N) = 0
  have sum_cos4 : ∑ k ∈ Finset.range N, Real.cos (4 * (2 * π * k / N)) = 0 := by
    calc ∑ k ∈ Finset.range N, Real.cos (4 * (2 * π * k / N))
        = ∑ k ∈ Finset.range N, Real.cos (8 * π * k / N) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          ring_nf
      _ = 0 := by
          have h := sum_cos_multiple_rotated_roots N 4 0 (by omega : 0 < N) (by omega : 0 < 4) (by omega : 4 < N)
          convert h using 2 with k
          simp
          ring_nf
  rw [sum_cos2, sum_cos4]
  ring

/-- Sum of cos⁵(2πk/N) equals 0 for N > 5. -/
lemma rotated_roots_sum_pow5_eq (N : ℕ) (hN : 5 < N) :
    ∑ k ∈ Finset.range N, (Real.cos (2 * π * k / N)) ^ 5 = 0 := by
  -- Use cos⁵(x) = (cos(5x) + 5*cos(3x) + 10*cos(x))/16
  have cos_pow5 : ∀ x, Real.cos x ^ 5 = (Real.cos (5 * x) + 5 * Real.cos (3 * x) + 10 * Real.cos x) / 16 :=
    cos_five_formula
  simp_rw [cos_pow5]
  rw [← Finset.sum_div]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- Show ∑cos(10πk/N) = 0
  have sum_cos5 : ∑ k ∈ Finset.range N, Real.cos (5 * (2 * π * k / N)) = 0 := by
    calc ∑ k ∈ Finset.range N, Real.cos (5 * (2 * π * k / N))
        = ∑ k ∈ Finset.range N, Real.cos (10 * π * k / N) := by
          congr 1; ext k
          ring_nf
      _ = 0 := by
          have h := sum_cos_multiple_rotated_roots N 5 0 (by omega : 0 < N) (by omega : 0 < 5) (by omega : 5 < N)
          convert h using 2 with k
          simp
          ring_nf
  -- Show ∑5*cos(6πk/N) = 0
  have sum_cos3 : ∑ k ∈ Finset.range N, 5 * Real.cos (3 * (2 * π * k / N)) = 0 := by
    have simplified : ∑ k ∈ Finset.range N, 5 * Real.cos (3 * (2 * π * k / N)) =
                      5 * ∑ k ∈ Finset.range N, Real.cos (6 * π * k / N) := by
      rw [← Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      ring_nf
    rw [simplified]
    have h := sum_cos_multiple_rotated_roots N 3 0 (by omega : 0 < N) (by omega : 0 < 3) (by omega : 3 < N)
    have : ∑ k ∈ Finset.range N, Real.cos (6 * π * k / N) = 0 := by
      convert h using 2 with k
      simp
      ring_nf
    rw [this]
    ring
  -- Show ∑10*cos(2πk/N) = 0 using j=1
  have sum_cos1 : ∑ k ∈ Finset.range N, 10 * Real.cos (2 * π * k / N) = 0 := by
    have : ∑ k ∈ Finset.range N, 10 * Real.cos (2 * π * k / N) =
           10 * ∑ k ∈ Finset.range N, Real.cos (2 * π * k / N) := by
      rw [← Finset.mul_sum]
    rw [this]
    have : ∑ k ∈ Finset.range N, Real.cos (2 * π * k / N) = 0 :=
      rotated_roots_sum_eq_zero N (by omega : 1 < N)
    rw [this]
    ring
  rw [sum_cos5, sum_cos3, sum_cos1]
  ring

/-- Sum of cos⁴((2k+1)π/(2N)) equals 3N/8 for N > 4. -/
lemma chebyshev_roots_sum_pow4_eq (N : ℕ) (hN : 4 < N) :
    ∑ k ∈ Finset.range N, (Real.cos ((2 * k + 1 : ℝ) * π / (2 * N))) ^ 4 = 3 * N / 8 := by
  -- Use cos⁴(x) = (3 + 4*cos(2x) + cos(4x))/8
  have cos_pow4 : ∀ x, Real.cos x ^ 4 = (3 + 4 * Real.cos (2 * x) + Real.cos (4 * x)) / 8 :=
    cos_four_formula
  simp_rw [cos_pow4]
  rw [← Finset.sum_div]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
  -- Show ∑ 4*cos(2(2k+1)π/(2N)) = 0, which simplifies to ∑ 4*cos((2k+1)π/N) = 0
  have sum_cos2 : ∑ k ∈ Finset.range N, 4 * Real.cos (2 * ((2 * k + 1 : ℝ) * π / (2 * N))) = 0 := by
    have simplified : ∑ k ∈ Finset.range N, 4 * Real.cos (2 * ((2 * k + 1 : ℝ) * π / (2 * N))) =
                      4 * ∑ k ∈ Finset.range N, Real.cos ((2 * k + 1 : ℝ) * π / N) := by
      rw [← Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      ring_nf
    rw [simplified]
    -- Use complex exponentials to show ∑cos((2k+1)π/N) = 0
    have : ∑ k ∈ Finset.range N, Real.cos ((2 * k + 1 : ℝ) * π / N) = 0 := by
      have complex_sum : ∑ k ∈ Finset.range N, Complex.exp (Complex.I * (2 * k + 1 : ℝ) * π / N) = 0 := by
        calc ∑ k ∈ Finset.range N, Complex.exp (Complex.I * (2 * k + 1 : ℝ) * π / N)
            = ∑ k ∈ Finset.range N, Complex.exp (Complex.I * π / N) * Complex.exp (Complex.I * (2 * k : ℝ) * π / N) := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [← Complex.exp_add]
              congr 1; push_cast; ring
          _ = Complex.exp (Complex.I * π / N) * ∑ k ∈ Finset.range N, Complex.exp (Complex.I * (2 * k : ℝ) * π / N) := by
              rw [Finset.mul_sum]
          _ = Complex.exp (Complex.I * π / N) * ∑ k ∈ Finset.range N, Complex.exp (2 * (Complex.I * π * k / N)) := by
              congr 2
              funext k
              congr 1; push_cast; ring
          _ = Complex.exp (Complex.I * π / N) * 0 := by
              congr 1
              have prim : IsPrimitiveRoot (Complex.exp (2 * π * Complex.I / N)) N := by
                apply Complex.isPrimitiveRoot_exp; omega
              have geom := prim.geom_sum_eq_zero (by omega : 1 < N)
              convert geom using 2 with k
              rw [← Complex.exp_nat_mul]; congr 1; ring
          _ = 0 := by simp
      have cos_eq : ∀ k : ℕ, Real.cos ((2 * k + 1 : ℝ) * π / N) = (Complex.exp (Complex.I * (2 * k + 1 : ℝ) * π / N)).re := fun k => by
        have h1 : (Complex.I * ((2 * k + 1 : ℝ) : ℂ) * π / N) = (((2 * k + 1 : ℝ) * π / N : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [show (Complex.I * (2 * k + 1 : ℝ) * π / N : ℂ) = Complex.I * ((2 * k + 1 : ℝ) : ℂ) * π / N by push_cast; rfl]
        rw [h1]
        exact (Complex.exp_ofReal_mul_I_re _).symm
      simp_rw [cos_eq]
      rw [← Complex.re_sum, complex_sum]
      simp
    rw [this]; ring
  -- Show ∑cos(4(2k+1)π/(2N)) = ∑cos((4k+2)π/N) = 0
  have sum_cos4 : ∑ k ∈ Finset.range N, Real.cos (4 * ((2 * k + 1 : ℝ) * π / (2 * N))) = 0 := by
    have simplified : ∑ k ∈ Finset.range N, Real.cos (4 * ((2 * k + 1 : ℝ) * π / (2 * N))) =
                      ∑ k ∈ Finset.range N, Real.cos ((4 * k + 2 : ℝ) * π / N) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      ring_nf
    rw [simplified]
    -- Use complex exponentials
    have complex_sum : ∑ k ∈ Finset.range N, Complex.exp (Complex.I * (4 * k + 2 : ℝ) * π / N) = 0 := by
      calc ∑ k ∈ Finset.range N, Complex.exp (Complex.I * (4 * k + 2 : ℝ) * π / N)
          = ∑ k ∈ Finset.range N, Complex.exp (Complex.I * 2 * π / N) * Complex.exp (Complex.I * (4 * k : ℝ) * π / N) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [← Complex.exp_add]
            congr 1; push_cast; ring
        _ = Complex.exp (Complex.I * 2 * π / N) * ∑ k ∈ Finset.range N, Complex.exp (Complex.I * (4 * k : ℝ) * π / N) := by
            rw [Finset.mul_sum]
        _ = Complex.exp (Complex.I * 2 * π / N) * ∑ k ∈ Finset.range N, Complex.exp (4 * (Complex.I * π * k / N)) := by
            congr 2
            funext k
            congr 1; push_cast; ring
        _ = Complex.exp (Complex.I * 2 * π / N) * 0 := by
            congr 1
            have prim : IsPrimitiveRoot (Complex.exp (2 * π * Complex.I / N)) N := by
              apply Complex.isPrimitiveRoot_exp; omega
            -- exp(4*I*π*k/N) = exp(2*2*I*π*k/N) = ω^(2k) where ω = exp(2πi/N)
            have h_rewrite : ∑ k ∈ Finset.range N, Complex.exp (4 * (Complex.I * π * k / N)) =
                             ∑ k ∈ Finset.range N, (Complex.exp (2 * π * Complex.I / N)) ^ (2 * k) := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [← Complex.exp_nat_mul]
              congr 1
              push_cast
              ring
            rw [h_rewrite]
            -- Now ∑ ω^(2k) = ∑ (ω^2)^k, and we need ω^2 ≠ 1 and (ω^2)^N = 1
            conv_lhs =>
              arg 2
              ext k
              rw [pow_mul]
            have ω2_ne_one : Complex.exp (2 * π * Complex.I / N) ^ 2 ≠ 1 := by
              intro h_eq
              have h_div : N ∣ 2 := (prim.pow_eq_one_iff_dvd 2).mp h_eq
              have : N ≤ 2 := Nat.le_of_dvd (by omega) h_div
              omega
            have ω2_pow_N : (Complex.exp (2 * π * Complex.I / N) ^ 2) ^ N = 1 := by
              rw [← pow_mul]
              calc Complex.exp (2 * π * Complex.I / N) ^ (2 * N)
                  = Complex.exp (2 * π * Complex.I / N) ^ (N * 2) := by ring_nf
                _ = (Complex.exp (2 * π * Complex.I / N) ^ N) ^ 2 := by rw [pow_mul]
                _ = 1 ^ 2 := by rw [prim.pow_eq_one]
                _ = 1 := one_pow 2
            have h_geom : (Complex.exp (2 * π * Complex.I / N) ^ 2 - 1) *
                          ∑ k ∈ Finset.range N, (Complex.exp (2 * π * Complex.I / N) ^ 2) ^ k =
                          (Complex.exp (2 * π * Complex.I / N) ^ 2) ^ N - 1 :=
              mul_geom_sum (Complex.exp (2 * π * Complex.I / N) ^ 2) N
            rw [ω2_pow_N] at h_geom
            have : (Complex.exp (2 * π * Complex.I / N) ^ 2 - 1) *
                   ∑ k ∈ Finset.range N, (Complex.exp (2 * π * Complex.I / N) ^ 2) ^ k = 0 := by
              rw [h_geom]; ring
            exact eq_zero_of_ne_zero_of_mul_left_eq_zero (sub_ne_zero_of_ne ω2_ne_one) this
        _ = 0 := by simp
    have cos_eq : ∀ k : ℕ, Real.cos ((4 * k + 2 : ℝ) * π / N) = (Complex.exp (Complex.I * (4 * k + 2 : ℝ) * π / N)).re := fun k => by
      have h1 : (Complex.I * ((4 * k + 2 : ℝ) : ℂ) * π / N) = (((4 * k + 2 : ℝ) * π / N : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [show (Complex.I * (4 * k + 2 : ℝ) * π / N : ℂ) = Complex.I * ((4 * k + 2 : ℝ) : ℂ) * π / N by push_cast; rfl]
      rw [h1]
      exact (Complex.exp_ofReal_mul_I_re _).symm
    simp_rw [cos_eq]
    rw [← Complex.re_sum, complex_sum]
    simp
  rw [sum_cos2, sum_cos4]
  ring

/-- Sum of cos⁵((2k+1)π/(2N)) equals 0 for N > 5. -/
lemma chebyshev_roots_sum_pow5_eq (N : ℕ) (hN : 5 < N) :
    ∑ k ∈ Finset.range N, (Real.cos ((2 * k + 1 : ℝ) * π / (2 * N))) ^ 5 = 0 := by
  -- Use cos⁵(x) = (cos(5x) + 5*cos(3x) + 10*cos(x))/16
  have cos_pow5 : ∀ x, Real.cos x ^ 5 = (Real.cos (5 * x) + 5 * Real.cos (3 * x) + 10 * Real.cos x) / 16 :=
    cos_five_formula
  simp_rw [cos_pow5]
  rw [← Finset.sum_div]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- Show ∑cos(5(2k+1)π/(2N)) = ∑cos((10k+5)π/(2N)) = 0
  have sum_cos5 : ∑ k ∈ Finset.range N, Real.cos (5 * ((2 * k + 1 : ℝ) * π / (2 * N))) = 0 := by
    have simplified : ∑ k ∈ Finset.range N, Real.cos (5 * ((2 * k + 1 : ℝ) * π / (2 * N))) =
                      ∑ k ∈ Finset.range N, Real.cos ((10 * k + 5 : ℝ) * π / (2 * N)) := by
      congr 1
      ext k
      ring_nf
    rw [simplified]
    -- Use pairing: angles at k and (N-k-1) sum to 5π, so cosines cancel
    -- cos((10k+5)π/(2N)) + cos((10(N-k-1)+5)π/(2N)) = cos(θ) + cos(5π-θ) = 0
    have key : ∀ k < N, Real.cos ((10 * k + 5 : ℝ) * π / (2 * N)) +
                        Real.cos ((10 * (N - k - 1) + 5 : ℝ) * π / (2 * N)) = 0 := by
      intro k hk
      -- Show the angles sum to 5π
      have angle_sum : (10 * k + 5 : ℝ) * π / (2 * N) + (10 * (N - k - 1) + 5 : ℝ) * π / (2 * N) = 5 * π := by
        field_simp
        ring
      -- Use cos(θ) + cos(5π - θ) = 0
      have second_angle : (10 * (N - k - 1) + 5 : ℝ) * π / (2 * N) =
                          5 * π - (10 * k + 5 : ℝ) * π / (2 * N) := by
        linarith [angle_sum]
      rw [second_angle]
      -- cos(5π - θ) = cos(5π)cos(θ) + sin(5π)sin(θ) = (-1)cos(θ) + 0·sin(θ) = -cos(θ)
      have : Real.cos (5 * π - (10 * k + 5 : ℝ) * π / (2 * N)) = -Real.cos ((10 * k + 5 : ℝ) * π / (2 * N)) := by
        rw [Real.cos_sub]
        have cos_5pi : Real.cos (5 * π) = -1 := by
          have eq : (5 : ℝ) * π = (2 : ℕ) * (2 * π) + π := by push_cast; ring
          rw [eq]
          exact Real.cos_nat_mul_two_pi_add_pi 2
        have sin_5pi : Real.sin (5 * π) = 0 := by
          have eq : (5 : ℝ) * π = (3 : ℕ) * (2 * π) - π := by push_cast; ring
          rw [eq, Real.sin_nat_mul_two_pi_sub, Real.sin_pi]
          simp
        rw [cos_5pi, sin_5pi]
        ring
      rw [this]
      ring
    -- Use involution pairing
    let f : ℕ → ℝ := fun k => Real.cos ((10 * k + 5 : ℝ) * π / (2 * N))
    change ∑ k ∈ Finset.range N, f k = 0
    refine Finset.sum_involution (fun k _ => N - k - 1) ?_ ?_ ?_ ?_
    · -- Show f k + f (g k) = 0
      intro k hk
      have hk' : k < N := Finset.mem_range.mp hk
      change f k + f (N - k - 1) = 0
      simp only [f]
      -- Need to show ↑(N - k - 1) = ↑N - ↑k - 1
      have h_le : k + 1 ≤ N := Nat.succ_le_of_lt hk'
      have cast_eq : ((N - k - 1 : ℕ) : ℝ) = (N : ℝ) - (k : ℝ) - 1 := by
        rw [show N - k - 1 = N - (k + 1) by omega]
        rw [Nat.cast_sub h_le]
        push_cast
        ring
      rw [cast_eq]
      exact key k hk'
    · -- Show that non-zero elements map to different elements
      intro k hk hfk
      simp only [Finset.mem_range] at hk
      intro heq
      simp only [f] at hfk
      simp only at heq
      -- If N - k - 1 = k, then f k + f k = 0, so f k = 0
      -- This happens when 2k + 1 = N
      have h_eq : 2 * k + 1 = N := by omega
      -- Then (10k+5)π/(2N) = 5(2k+1)π/(2N) = 5π/2
      have : (10 * k + 5 : ℝ) * π / (2 * N) = 5 * π / 2 := by
        have : (10 * k + 5 : ℝ) = 5 * N := by norm_cast; omega
        rw [this]
        field_simp
      -- cos(5π/2) = cos(2π + π/2) = cos(π/2) = 0
      have cos_val : Real.cos (5 * π / 2) = 0 := by
        rw [show (5 : ℝ) * π / 2 = 2 * π + π / 2 by ring]
        rw [Real.cos_add]
        norm_num [Real.cos_two_pi, Real.sin_two_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]
      rw [this, cos_val] at hfk
      exact hfk rfl
    · -- Show g k is in range
      intro k hk
      simp only [Finset.mem_range] at hk ⊢
      omega
    · -- Show g (g k) = k (involution)
      intro k hk
      simp only [Finset.mem_range] at hk
      -- Need: N - (N - k - 1) - 1 = k
      have hk_lt : k < N := hk
      have h_le : k + 1 ≤ N := Nat.succ_le_of_lt hk_lt
      simp only
      rw [show N - k - 1 = N - (k + 1) by omega]
      have h_le2 : N - (k + 1) + 1 ≤ N := by omega
      rw [Nat.sub_sub_self h_le]
      omega
  -- Show ∑5*cos(3(2k+1)π/(2N)) = 0
  have sum_cos3 : ∑ k ∈ Finset.range N, 5 * Real.cos (3 * ((2 * k + 1 : ℝ) * π / (2 * N))) = 0 := by
    have : ∑ k ∈ Finset.range N, 5 * Real.cos (3 * ((2 * k + 1 : ℝ) * π / (2 * N))) =
           5 * ∑ k ∈ Finset.range N, Real.cos (3 * ((2 * k + 1 : ℝ) * π / (2 * N))) := by
      rw [← Finset.mul_sum]
    rw [this]
    -- This sum already appeared in chebyshev_roots_sum_cube_eq
    have simplified : ∑ k ∈ Finset.range N, Real.cos (3 * ((2 * k + 1 : ℝ) * π / (2 * N))) =
                      ∑ k ∈ Finset.range N, Real.cos ((6 * k + 3 : ℝ) * π / (2 * N)) := by
      congr 1
      ext k
      ring_nf
    rw [simplified]
    -- Show ∑ cos((6k+3)π/(2N)) = 0 first
    have sum_zero : ∑ k ∈ Finset.range N, Real.cos ((6 * k + 3 : ℝ) * π / (2 * N)) = 0 := by
      -- Use pairing: angles at k and (N-k-1) sum to 3π, so cosines cancel
      -- cos((6k+3)π/(2N)) + cos((6(N-k-1)+3)π/(2N)) = cos(θ) + cos(3π-θ) = 0
      have key : ∀ k < N, Real.cos ((6 * k + 3 : ℝ) * π / (2 * N)) +
                          Real.cos ((6 * (N - k - 1) + 3 : ℝ) * π / (2 * N)) = 0 := by
        intro k hk
        -- Show the angles sum to 3π
        have angle_sum : (6 * k + 3 : ℝ) * π / (2 * N) + (6 * (N - k - 1) + 3 : ℝ) * π / (2 * N) = 3 * π := by
          field_simp
          ring
        -- Use cos(θ) + cos(3π - θ) = 0
        have second_angle : (6 * (N - k - 1) + 3 : ℝ) * π / (2 * N) =
                            3 * π - (6 * k + 3 : ℝ) * π / (2 * N) := by
          linarith [angle_sum]
        rw [second_angle]
        -- cos(3π - θ) = cos(3π)cos(θ) + sin(3π)sin(θ) = (-1)cos(θ) + 0·sin(θ) = -cos(θ)
        have : Real.cos (3 * π - (6 * k + 3 : ℝ) * π / (2 * N)) = -Real.cos ((6 * k + 3 : ℝ) * π / (2 * N)) := by
          rw [Real.cos_sub]
          have cos_3pi : Real.cos (3 * π) = -1 := by
            rw [show (3 : ℝ) * π = 2 * π + π by ring]
            rw [Real.cos_add]
            norm_num [Real.cos_two_pi, Real.sin_two_pi, Real.cos_pi, Real.sin_pi]
          have sin_3pi : Real.sin (3 * π) = 0 := by
            rw [show (3 : ℝ) * π = 2 * π + π by ring]
            rw [Real.sin_add]
            norm_num [Real.cos_two_pi, Real.sin_two_pi, Real.cos_pi, Real.sin_pi]
          rw [cos_3pi, sin_3pi]
          ring
        rw [this]
        ring
      -- Use involution pairing
      let f : ℕ → ℝ := fun k => Real.cos ((6 * k + 3 : ℝ) * π / (2 * N))
      change ∑ k ∈ Finset.range N, f k = 0
      refine Finset.sum_involution (fun k _ => N - k - 1) ?_ ?_ ?_ ?_
      · -- Show f k + f (g k) = 0
        intro k hk
        have hk' : k < N := Finset.mem_range.mp hk
        change f k + f (N - k - 1) = 0
        simp only [f]
        -- Need to show ↑(N - k - 1) = ↑N - ↑k - 1
        have h_le : k + 1 ≤ N := Nat.succ_le_of_lt hk'
        have cast_eq : ((N - k - 1 : ℕ) : ℝ) = (N : ℝ) - (k : ℝ) - 1 := by
          rw [show N - k - 1 = N - (k + 1) by omega]
          rw [Nat.cast_sub h_le]
          push_cast
          ring
        rw [cast_eq]
        exact key k hk'
      · -- Show that non-zero elements map to different elements
        intro k hk hfk
        simp only [Finset.mem_range] at hk
        intro heq
        simp only [f] at hfk
        simp only at heq
        -- If N - k - 1 = k, then f k + f k = 0, so f k = 0
        -- This happens when 2k + 1 = N
        have h_eq : 2 * k + 1 = N := by omega
        -- Then (6k+3)π/(2N) = 3(2k+1)π/(2N) = 3π/2
        have : (6 * k + 3 : ℝ) * π / (2 * N) = 3 * π / 2 := by
          have : (6 * k + 3 : ℝ) = 3 * N := by norm_cast; omega
          rw [this]
          field_simp
        -- cos(3π/2) = 0 because 3π/2 = π + π/2, so cos(3π/2) = -cos(π/2) = 0
        have cos_val : Real.cos (3 * π / 2) = 0 := by
          rw [show (3 : ℝ) * π / 2 = π + π / 2 by ring]
          rw [Real.cos_add]
          norm_num [Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]
        rw [this, cos_val] at hfk
        exact hfk rfl
      · -- Show g k is in range
        intro k hk
        simp only [Finset.mem_range] at hk ⊢
        omega
      · -- Show g (g k) = k (involution)
        intro k hk
        simp only [Finset.mem_range] at hk
        -- Need: N - (N - k - 1) - 1 = k
        have hk_lt : k < N := hk
        have h_le : k + 1 ≤ N := Nat.succ_le_of_lt hk_lt
        simp only
        rw [show N - k - 1 = N - (k + 1) by omega]
        have h_le2 : N - (k + 1) + 1 ≤ N := by omega
        rw [Nat.sub_sub_self h_le]
        omega
    rw [sum_zero]
    ring
  -- Show ∑10*cos((2k+1)π/(2N)) = 0 using j=1
  have sum_cos1 : ∑ k ∈ Finset.range N, 10 * Real.cos ((2 * k + 1 : ℝ) * π / (2 * N)) = 0 := by
    have : ∑ k ∈ Finset.range N, 10 * Real.cos ((2 * k + 1 : ℝ) * π / (2 * N)) =
           10 * ∑ k ∈ Finset.range N, Real.cos ((2 * k + 1 : ℝ) * π / (2 * N)) := by
      rw [← Finset.mul_sum]
    rw [this]
    have : ∑ k ∈ Finset.range N, Real.cos ((2 * k + 1 : ℝ) * π / (2 * N)) = 0 :=
      chebyshev_roots_sum_eq_zero N (by omega : 1 < N)
    rw [this]
    ring
  rw [sum_cos5, sum_cos3, sum_cos1]
  ring

/-- Power sum equality for j=4: both root systems sum to 3N/8. -/
lemma powersum_j4_equality (N : ℕ) (hN : 4 < N) :
    ∑ k ∈ Finset.range N, (Real.cos (2 * π * k / N)) ^ 4 =
    ∑ k ∈ Finset.range N, (Real.cos ((2 * k + 1 : ℝ) * π / (2 * N))) ^ 4 := by
  rw [rotated_roots_sum_pow4_eq N hN, chebyshev_roots_sum_pow4_eq N hN]

/-- Power sum equality for j=5: both root systems sum to 0. -/
lemma powersum_j5_equality (N : ℕ) (hN : 5 < N) :
    ∑ k ∈ Finset.range N, (Real.cos (2 * π * k / N)) ^ 5 =
    ∑ k ∈ Finset.range N, (Real.cos ((2 * k + 1 : ℝ) * π / (2 * N))) ^ 5 := by
  rw [rotated_roots_sum_pow5_eq N hN, chebyshev_roots_sum_pow5_eq N hN]

/-- Sum of cos⁶(2πk/N) equals 5N/16 for N > 6. -/
lemma rotated_roots_sum_pow6_eq (N : ℕ) (hN : 6 < N) :
    ∑ k ∈ Finset.range N, (Real.cos (2 * π * k / N)) ^ 6 = 5 * N / 16 := by
  -- Use cos⁶(x) = (10 + 15*cos(2x) + 6*cos(4x) + cos(6x))/32
  have cos_pow6 : ∀ x, Real.cos x ^ 6 = (10 + 15 * Real.cos (2 * x) + 6 * Real.cos (4 * x) + Real.cos (6 * x)) / 32 :=
    cos_six_formula
  simp_rw [cos_pow6]
  rw [← Finset.sum_div]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
  -- Show ∑ 15*cos(4πk/N) = 0
  have sum_cos2 : ∑ k ∈ Finset.range N, 15 * Real.cos (2 * (2 * π * k / N)) = 0 := by
    have simplified : ∑ k ∈ Finset.range N, 15 * Real.cos (2 * (2 * π * k / N)) =
                      15 * ∑ k ∈ Finset.range N, Real.cos (4 * π * k / N) := by
      rw [← Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      ring_nf
    rw [simplified]
    have h := sum_cos_multiple_rotated_roots N 2 0 (by omega : 0 < N) (by omega : 0 < 2) (by omega : 2 < N)
    have : ∑ k ∈ Finset.range N, Real.cos (4 * π * k / N) = 0 := by
      convert h using 2 with k
      simp
      ring_nf
    rw [this]
    ring
  -- Show ∑6*cos(8πk/N) = 0
  have sum_cos4 : ∑ k ∈ Finset.range N, 6 * Real.cos (4 * (2 * π * k / N)) = 0 := by
    have simplified : ∑ k ∈ Finset.range N, 6 * Real.cos (4 * (2 * π * k / N)) =
                      6 * ∑ k ∈ Finset.range N, Real.cos (8 * π * k / N) := by
      rw [← Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      ring_nf
    rw [simplified]
    have h := sum_cos_multiple_rotated_roots N 4 0 (by omega : 0 < N) (by omega : 0 < 4) (by omega : 4 < N)
    have : ∑ k ∈ Finset.range N, Real.cos (8 * π * k / N) = 0 := by
      convert h using 2 with k
      simp
      ring_nf
    rw [this]
    ring
  -- Show ∑cos(12πk/N) = 0
  have sum_cos6 : ∑ k ∈ Finset.range N, Real.cos (6 * (2 * π * k / N)) = 0 := by
    calc ∑ k ∈ Finset.range N, Real.cos (6 * (2 * π * k / N))
        = ∑ k ∈ Finset.range N, Real.cos (12 * π * k / N) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          ring_nf
      _ = 0 := by
          have h := sum_cos_multiple_rotated_roots N 6 0 (by omega : 0 < N) (by omega : 0 < 6) (by omega : 6 < N)
          convert h using 2 with k
          simp
          ring_nf
  rw [sum_cos2, sum_cos4, sum_cos6]
  ring

/-- Sum of cos⁶((2k+1)π/(2N)) equals 5N/16 for N > 6. -/
lemma chebyshev_roots_sum_pow6_eq (N : ℕ) (hN : 6 < N) :
    ∑ k ∈ Finset.range N, (Real.cos ((2 * k + 1 : ℝ) * π / (2 * N))) ^ 6 = 5 * N / 16 := by
  -- Use cos⁶(x) = (10 + 15*cos(2x) + 6*cos(4x) + cos(6x))/32
  have cos_pow6 : ∀ x, Real.cos x ^ 6 = (10 + 15 * Real.cos (2 * x) + 6 * Real.cos (4 * x) + Real.cos (6 * x)) / 32 :=
    cos_six_formula
  simp_rw [cos_pow6]
  rw [← Finset.sum_div]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
  -- Show ∑ 15*cos(2(2k+1)π/(2N)) = 15*∑cos((2k+1)π/N) = 0
  have sum_cos2 : ∑ k ∈ Finset.range N, 15 * Real.cos (2 * ((2 * k + 1 : ℝ) * π / (2 * N))) = 0 := by
    have simplified : ∑ k ∈ Finset.range N, 15 * Real.cos (2 * ((2 * k + 1 : ℝ) * π / (2 * N))) =
                      15 * ∑ k ∈ Finset.range N, Real.cos ((2 * k + 1 : ℝ) * π / N) := by
      rw [← Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      ring_nf
    rw [simplified]
    -- This sum was proven in chebyshev_roots_sum_pow4_eq
    have : ∑ k ∈ Finset.range N, Real.cos ((2 * k + 1 : ℝ) * π / N) = 0 := by
      have complex_sum : ∑ k ∈ Finset.range N, Complex.exp (Complex.I * (2 * k + 1 : ℝ) * π / N) = 0 := by
        calc ∑ k ∈ Finset.range N, Complex.exp (Complex.I * (2 * k + 1 : ℝ) * π / N)
            = ∑ k ∈ Finset.range N, Complex.exp (Complex.I * π / N) * Complex.exp (Complex.I * (2 * k : ℝ) * π / N) := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [← Complex.exp_add]
              congr 1; push_cast; ring
          _ = Complex.exp (Complex.I * π / N) * ∑ k ∈ Finset.range N, Complex.exp (Complex.I * (2 * k : ℝ) * π / N) := by
              rw [Finset.mul_sum]
          _ = Complex.exp (Complex.I * π / N) * ∑ k ∈ Finset.range N, Complex.exp (2 * (Complex.I * π * k / N)) := by
              congr 2
              funext k
              congr 1; push_cast; ring
          _ = Complex.exp (Complex.I * π / N) * 0 := by
              congr 1
              have prim : IsPrimitiveRoot (Complex.exp (2 * π * Complex.I / N)) N := by
                apply Complex.isPrimitiveRoot_exp; omega
              have geom := prim.geom_sum_eq_zero (by omega : 1 < N)
              convert geom using 2 with k
              rw [← Complex.exp_nat_mul]; congr 1; ring
          _ = 0 := by simp
      have cos_eq : ∀ k : ℕ, Real.cos ((2 * k + 1 : ℝ) * π / N) = (Complex.exp (Complex.I * (2 * k + 1 : ℝ) * π / N)).re := fun k => by
        have h1 : (Complex.I * ((2 * k + 1 : ℝ) : ℂ) * π / N) = (((2 * k + 1 : ℝ) * π / N : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [show (Complex.I * (2 * k + 1 : ℝ) * π / N : ℂ) = Complex.I * ((2 * k + 1 : ℝ) : ℂ) * π / N by push_cast; rfl]
        rw [h1]
        exact (Complex.exp_ofReal_mul_I_re _).symm
      simp_rw [cos_eq]
      rw [← Complex.re_sum, complex_sum]
      simp
    rw [this]; ring
  -- Show ∑6*cos(4(2k+1)π/(2N)) = 6*∑cos((4k+2)π/N) = 0
  have sum_cos4 : ∑ k ∈ Finset.range N, 6 * Real.cos (4 * ((2 * k + 1 : ℝ) * π / (2 * N))) = 0 := by
    have simplified : ∑ k ∈ Finset.range N, 6 * Real.cos (4 * ((2 * k + 1 : ℝ) * π / (2 * N))) =
                      6 * ∑ k ∈ Finset.range N, Real.cos ((4 * k + 2 : ℝ) * π / N) := by
      rw [← Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      ring_nf
    rw [simplified]
    -- This sum was proven in chebyshev_roots_sum_pow4_eq
    have : ∑ k ∈ Finset.range N, Real.cos ((4 * k + 2 : ℝ) * π / N) = 0 := by
      have complex_sum : ∑ k ∈ Finset.range N, Complex.exp (Complex.I * (4 * k + 2 : ℝ) * π / N) = 0 := by
        calc ∑ k ∈ Finset.range N, Complex.exp (Complex.I * (4 * k + 2 : ℝ) * π / N)
            = ∑ k ∈ Finset.range N, Complex.exp (Complex.I * 2 * π / N) * Complex.exp (Complex.I * (4 * k : ℝ) * π / N) := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [← Complex.exp_add]
              congr 1; push_cast; ring
          _ = Complex.exp (Complex.I * 2 * π / N) * ∑ k ∈ Finset.range N, Complex.exp (Complex.I * (4 * k : ℝ) * π / N) := by
              rw [Finset.mul_sum]
          _ = Complex.exp (Complex.I * 2 * π / N) * ∑ k ∈ Finset.range N, Complex.exp (4 * (Complex.I * π * k / N)) := by
              congr 2
              funext k
              congr 1; push_cast; ring
          _ = Complex.exp (Complex.I * 2 * π / N) * 0 := by
              congr 1
              have prim : IsPrimitiveRoot (Complex.exp (2 * π * Complex.I / N)) N := by
                apply Complex.isPrimitiveRoot_exp; omega
              have h_rewrite : ∑ k ∈ Finset.range N, Complex.exp (4 * (Complex.I * π * k / N)) =
                               ∑ k ∈ Finset.range N, (Complex.exp (2 * π * Complex.I / N)) ^ (2 * k) := by
                refine Finset.sum_congr rfl fun k _ => ?_
                rw [← Complex.exp_nat_mul]
                congr 1
                push_cast
                ring
              rw [h_rewrite]
              conv_lhs =>
                arg 2
                ext k
                rw [pow_mul]
              have ω2_ne_one : Complex.exp (2 * π * Complex.I / N) ^ 2 ≠ 1 := by
                intro h_eq
                have h_div : N ∣ 2 := (prim.pow_eq_one_iff_dvd 2).mp h_eq
                have : N ≤ 2 := Nat.le_of_dvd (by omega) h_div
                omega
              have ω2_pow_N : (Complex.exp (2 * π * Complex.I / N) ^ 2) ^ N = 1 := by
                rw [← pow_mul]
                calc Complex.exp (2 * π * Complex.I / N) ^ (2 * N)
                    = Complex.exp (2 * π * Complex.I / N) ^ (N * 2) := by ring_nf
                  _ = (Complex.exp (2 * π * Complex.I / N) ^ N) ^ 2 := by rw [pow_mul]
                  _ = 1 ^ 2 := by rw [prim.pow_eq_one]
                  _ = 1 := one_pow 2
              have h_geom : (Complex.exp (2 * π * Complex.I / N) ^ 2 - 1) *
                            ∑ k ∈ Finset.range N, (Complex.exp (2 * π * Complex.I / N) ^ 2) ^ k =
                            (Complex.exp (2 * π * Complex.I / N) ^ 2) ^ N - 1 :=
                mul_geom_sum (Complex.exp (2 * π * Complex.I / N) ^ 2) N
              rw [ω2_pow_N] at h_geom
              have : (Complex.exp (2 * π * Complex.I / N) ^ 2 - 1) *
                     ∑ k ∈ Finset.range N, (Complex.exp (2 * π * Complex.I / N) ^ 2) ^ k = 0 := by
                rw [h_geom]; ring
              exact eq_zero_of_ne_zero_of_mul_left_eq_zero (sub_ne_zero_of_ne ω2_ne_one) this
          _ = 0 := by simp
      have cos_eq : ∀ k : ℕ, Real.cos ((4 * k + 2 : ℝ) * π / N) = (Complex.exp (Complex.I * (4 * k + 2 : ℝ) * π / N)).re := fun k => by
        have h1 : (Complex.I * ((4 * k + 2 : ℝ) : ℂ) * π / N) = (((4 * k + 2 : ℝ) * π / N : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [show (Complex.I * (4 * k + 2 : ℝ) * π / N : ℂ) = Complex.I * ((4 * k + 2 : ℝ) : ℂ) * π / N by push_cast; rfl]
        rw [h1]
        exact (Complex.exp_ofReal_mul_I_re _).symm
      simp_rw [cos_eq]
      rw [← Complex.re_sum, complex_sum]
      simp
    rw [this]; ring
  -- Show ∑cos(6(2k+1)π/(2N)) = ∑cos((12k+6)π/(2N)) = ∑cos((6k+3)π/N) = 0
  have sum_cos6 : ∑ k ∈ Finset.range N, Real.cos (6 * ((2 * k + 1 : ℝ) * π / (2 * N))) = 0 := by
    have simplified : ∑ k ∈ Finset.range N, Real.cos (6 * ((2 * k + 1 : ℝ) * π / (2 * N))) =
                      ∑ k ∈ Finset.range N, Real.cos ((6 * k + 3 : ℝ) * π / N) := by
      congr 1
      ext k
      ring_nf
    rw [simplified]
    -- Use complex exponentials
    have complex_sum : ∑ k ∈ Finset.range N, Complex.exp (Complex.I * (6 * k + 3 : ℝ) * π / N) = 0 := by
      calc ∑ k ∈ Finset.range N, Complex.exp (Complex.I * (6 * k + 3 : ℝ) * π / N)
          = ∑ k ∈ Finset.range N, Complex.exp (Complex.I * 3 * π / N) * Complex.exp (Complex.I * (6 * k : ℝ) * π / N) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [← Complex.exp_add]
            congr 1; push_cast; ring
        _ = Complex.exp (Complex.I * 3 * π / N) * ∑ k ∈ Finset.range N, Complex.exp (Complex.I * (6 * k : ℝ) * π / N) := by
            rw [Finset.mul_sum]
        _ = Complex.exp (Complex.I * 3 * π / N) * ∑ k ∈ Finset.range N, Complex.exp (6 * (Complex.I * π * k / N)) := by
            congr 2
            funext k
            congr 1; push_cast; ring
        _ = Complex.exp (Complex.I * 3 * π / N) * 0 := by
            congr 1
            have prim : IsPrimitiveRoot (Complex.exp (2 * π * Complex.I / N)) N := by
              apply Complex.isPrimitiveRoot_exp; omega
            -- exp(6*I*π*k/N) = exp(2*3*I*π*k/N) = ω^(3k) where ω = exp(2πi/N)
            have h_rewrite : ∑ k ∈ Finset.range N, Complex.exp (6 * (Complex.I * π * k / N)) =
                             ∑ k ∈ Finset.range N, (Complex.exp (2 * π * Complex.I / N)) ^ (3 * k) := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [← Complex.exp_nat_mul]
              congr 1
              push_cast
              ring
            rw [h_rewrite]
            conv_lhs =>
              arg 2
              ext k
              rw [pow_mul]
            have ω3_ne_one : Complex.exp (2 * π * Complex.I / N) ^ 3 ≠ 1 := by
              intro h_eq
              have h_div : N ∣ 3 := (prim.pow_eq_one_iff_dvd 3).mp h_eq
              have : N ≤ 3 := Nat.le_of_dvd (by omega) h_div
              omega
            have ω3_pow_N : (Complex.exp (2 * π * Complex.I / N) ^ 3) ^ N = 1 := by
              rw [← pow_mul]
              calc Complex.exp (2 * π * Complex.I / N) ^ (3 * N)
                  = Complex.exp (2 * π * Complex.I / N) ^ (N * 3) := by ring_nf
                _ = (Complex.exp (2 * π * Complex.I / N) ^ N) ^ 3 := by rw [pow_mul]
                _ = 1 ^ 3 := by rw [prim.pow_eq_one]
                _ = 1 := one_pow 3
            have h_geom : (Complex.exp (2 * π * Complex.I / N) ^ 3 - 1) *
                          ∑ k ∈ Finset.range N, (Complex.exp (2 * π * Complex.I / N) ^ 3) ^ k =
                          (Complex.exp (2 * π * Complex.I / N) ^ 3) ^ N - 1 :=
              mul_geom_sum (Complex.exp (2 * π * Complex.I / N) ^ 3) N
            rw [ω3_pow_N] at h_geom
            have : (Complex.exp (2 * π * Complex.I / N) ^ 3 - 1) *
                   ∑ k ∈ Finset.range N, (Complex.exp (2 * π * Complex.I / N) ^ 3) ^ k = 0 := by
              rw [h_geom]; ring
            exact eq_zero_of_ne_zero_of_mul_left_eq_zero (sub_ne_zero_of_ne ω3_ne_one) this
        _ = 0 := by simp
    have cos_eq : ∀ k : ℕ, Real.cos ((6 * k + 3 : ℝ) * π / N) = (Complex.exp (Complex.I * (6 * k + 3 : ℝ) * π / N)).re := fun k => by
      have h1 : (Complex.I * ((6 * k + 3 : ℝ) : ℂ) * π / N) = (((6 * k + 3 : ℝ) * π / N : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [show (Complex.I * (6 * k + 3 : ℝ) * π / N : ℂ) = Complex.I * ((6 * k + 3 : ℝ) : ℂ) * π / N by push_cast; rfl]
      rw [h1]
      exact (Complex.exp_ofReal_mul_I_re _).symm
    simp_rw [cos_eq]
    rw [← Complex.re_sum, complex_sum]
    simp
  rw [sum_cos2, sum_cos4, sum_cos6]
  ring

/-- Power sum equality for j=6: both root systems sum to 5N/16. -/
lemma powersum_j6_equality (N : ℕ) (hN : 6 < N) :
    ∑ k ∈ Finset.range N, (Real.cos (2 * π * k / N)) ^ 6 =
    ∑ k ∈ Finset.range N, (Real.cos ((2 * k + 1 : ℝ) * π / (2 * N))) ^ 6 := by
  rw [rotated_roots_sum_pow6_eq N hN, chebyshev_roots_sum_pow6_eq N hN]

/-- Sum of cos²((2k+1)π/(2N)) equals N/2 for N > 2. -/
lemma chebyshev_roots_sum_sq_eq (N : ℕ) (hN : 2 < N) :
    ∑ k ∈ Finset.range N, (Real.cos ((2 * k + 1 : ℝ) * π / (2 * N))) ^ 2 = N / 2 := by
  -- Use cos²(x) = (1 + cos(2x))/2
  have cos_sq : ∀ x, Real.cos x ^ 2 = (1 + Real.cos (2 * x)) / 2 := by
    intro x
    rw [Real.cos_sq]
    ring
  simp_rw [cos_sq]
  rw [← Finset.sum_div]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
  -- Show ∑cos((2k+1)π/N) = 0 using pairing
  have sum_zero : ∑ k ∈ Finset.range N, Real.cos (2 * ((2 * k + 1 : ℝ) * π / (2 * N))) = 0 := by
    have simplified : ∑ k ∈ Finset.range N, Real.cos (2 * ((2 * k + 1 : ℝ) * π / (2 * N))) =
                      ∑ k ∈ Finset.range N, Real.cos ((2 * k + 1 : ℝ) * π / N) := by
      congr 1
      ext k
      ring_nf
    rw [simplified]
    have complex_sum : ∑ k ∈ Finset.range N, Complex.exp (Complex.I * (2 * k + 1 : ℝ) * π / N) = 0 := by
      calc ∑ k ∈ Finset.range N, Complex.exp (Complex.I * (2 * k + 1 : ℝ) * π / N)
          = ∑ k ∈ Finset.range N, Complex.exp (Complex.I * π / N) * Complex.exp (Complex.I * (2 * k : ℝ) * π / N) := by
            congr 1
            ext k
            rw [← Complex.exp_add]
            congr 1
            push_cast
            ring
        _ = Complex.exp (Complex.I * π / N) * ∑ k ∈ Finset.range N, Complex.exp (Complex.I * (2 * k : ℝ) * π / N) := by
            rw [Finset.mul_sum]
        _ = Complex.exp (Complex.I * π / N) * ∑ k ∈ Finset.range N, Complex.exp (2 * (Complex.I * π * k / N)) := by
            congr 2
            ext k
            congr 1
            push_cast
            ring
        _ = Complex.exp (Complex.I * π / N) * 0 := by
            congr 1
            -- Use primitive roots of unity
            have prim : IsPrimitiveRoot (Complex.exp (2 * π * Complex.I / N)) N := by
              apply Complex.isPrimitiveRoot_exp
              omega
            have geom := prim.geom_sum_eq_zero (by omega : 1 < N)
            convert geom using 2 with k
            rw [← Complex.exp_nat_mul]
            congr 1
            ring
        _ = 0 := by simp
    -- Extract real part: the sum of cosines equals Re(sum of complex exponentials)
    have cos_eq : ∀ k : ℕ, Real.cos ((2 * k + 1 : ℝ) * π / N) = (exp (I * (2 * k + 1 : ℝ) * π / N)).re := fun k => by
      have h1 : (I * ((2 * k + 1 : ℝ) : ℂ) * π / N) = (((2 * k + 1 : ℝ) * π / N : ℝ) : ℂ) * I := by
        push_cast
        ring
      rw [show (I * (2 * k + 1 : ℝ) * π / N : ℂ) = I * ((2 * k + 1 : ℝ) : ℂ) * π / N by push_cast; rfl]
      rw [h1]
      exact (Complex.exp_ofReal_mul_I_re _).symm
    simp_rw [cos_eq]
    rw [← Complex.re_sum, complex_sum]
    simp
  rw [sum_zero]
  ring

/-- Power sum equality for j=2: both root systems sum to N/2. -/
lemma powersum_j2_equality (N : ℕ) (hN : 2 < N) :
    ∑ k ∈ Finset.range N, (Real.cos (2 * π * k / N)) ^ 2 =
    ∑ k ∈ Finset.range N, (Real.cos ((2 * k + 1 : ℝ) * π / (2 * N))) ^ 2 := by
  rw [rotated_roots_sum_sq_eq N hN, chebyshev_roots_sum_sq_eq N hN]

/-- Sum of cos³(2πk/N) equals 0 for N > 3. -/
lemma rotated_roots_sum_cube_eq (N : ℕ) (hN : 3 < N) :
    ∑ k ∈ Finset.range N, (Real.cos (2 * π * k / N)) ^ 3 = 0 := by
  -- Use cos³(x) = (cos(3x) + 3cos(x))/4
  have cos_cube : ∀ x, Real.cos x ^ 3 = (Real.cos (3 * x) + 3 * Real.cos x) / 4 :=
    cos_cube_formula
  simp_rw [cos_cube]
  rw [← Finset.sum_div]
  rw [Finset.sum_add_distrib]
  -- Show ∑cos(6πk/N) = 0
  have sum_cos3 : ∑ k ∈ Finset.range N, Real.cos (3 * (2 * π * k / N)) = 0 := by
    calc ∑ k ∈ Finset.range N, Real.cos (3 * (2 * π * k / N))
        = ∑ k ∈ Finset.range N, Real.cos (6 * π * k / N) := by
          congr 1; ext k
          ring_nf
      _ = 0 := by
          have h := sum_cos_multiple_rotated_roots N 3 0 (by omega : 0 < N) (by omega : 0 < 3) (by omega : 3 < N)
          convert h using 2 with k
          simp
          ring_nf
  -- Show ∑3cos(2πk/N) = 0 using j=1
  have sum_cos : ∑ k ∈ Finset.range N, 3 * Real.cos (2 * π * k / N) = 0 := by
    have : ∑ k ∈ Finset.range N, 3 * Real.cos (2 * π * k / N) =
           3 * ∑ k ∈ Finset.range N, Real.cos (2 * π * k / N) := by
      rw [Finset.mul_sum]
    rw [this]
    have : ∑ k ∈ Finset.range N, Real.cos (2 * π * k / N) = 0 :=
      rotated_roots_sum_eq_zero N (by omega : 1 < N)
    rw [this]
    ring
  rw [sum_cos3, sum_cos]
  ring

/-- Sum of cos³((2k+1)π/(2N)) equals 0 for N > 3. -/
lemma chebyshev_roots_sum_cube_eq (N : ℕ) (hN : 3 < N) :
    ∑ k ∈ Finset.range N, (Real.cos ((2 * k + 1 : ℝ) * π / (2 * N))) ^ 3 = 0 := by
  -- Use cos³(x) = (cos(3x) + 3cos(x))/4
  have cos_cube : ∀ x, Real.cos x ^ 3 = (Real.cos (3 * x) + 3 * Real.cos x) / 4 :=
    cos_cube_formula
  simp_rw [cos_cube]
  rw [← Finset.sum_div]
  rw [Finset.sum_add_distrib]
  -- Show ∑cos(3(2k+1)π/(2N)) = 0
  have sum_cos3 : ∑ k ∈ Finset.range N, Real.cos (3 * ((2 * k + 1 : ℝ) * π / (2 * N))) = 0 := by
    have simplified : ∑ k ∈ Finset.range N, Real.cos (3 * ((2 * k + 1 : ℝ) * π / (2 * N))) =
                      ∑ k ∈ Finset.range N, Real.cos ((6 * k + 3 : ℝ) * π / (2 * N)) := by
      congr 1
      ext k
      ring_nf
    rw [simplified]
    -- Use pairing: angles at k and (N-k-1) sum to 3π, so cosines cancel
    -- cos((6k+3)π/(2N)) + cos((6(N-k-1)+3)π/(2N)) = cos(θ) + cos(3π-θ) = 0
    have key : ∀ k < N, Real.cos ((6 * k + 3 : ℝ) * π / (2 * N)) +
                        Real.cos ((6 * (N - k - 1) + 3 : ℝ) * π / (2 * N)) = 0 := by
      intro k hk
      -- Show the angles sum to 3π
      have angle_sum : (6 * k + 3 : ℝ) * π / (2 * N) + (6 * (N - k - 1) + 3 : ℝ) * π / (2 * N) = 3 * π := by
        field_simp
        ring
      -- Use cos(θ) + cos(3π - θ) = 0
      have second_angle : (6 * (N - k - 1) + 3 : ℝ) * π / (2 * N) =
                          3 * π - (6 * k + 3 : ℝ) * π / (2 * N) := by
        linarith [angle_sum]
      rw [second_angle]
      -- cos(3π - θ) = cos(3π)cos(θ) + sin(3π)sin(θ) = (-1)cos(θ) + 0·sin(θ) = -cos(θ)
      have : Real.cos (3 * π - (6 * k + 3 : ℝ) * π / (2 * N)) = -Real.cos ((6 * k + 3 : ℝ) * π / (2 * N)) := by
        rw [Real.cos_sub]
        have cos_3pi : Real.cos (3 * π) = -1 := by
          rw [show (3 : ℝ) * π = 2 * π + π by ring]
          rw [Real.cos_add]
          norm_num [Real.cos_two_pi, Real.sin_two_pi, Real.cos_pi, Real.sin_pi]
        have sin_3pi : Real.sin (3 * π) = 0 := by
          rw [show (3 : ℝ) * π = 2 * π + π by ring]
          rw [Real.sin_add]
          norm_num [Real.cos_two_pi, Real.sin_two_pi, Real.cos_pi, Real.sin_pi]
        rw [cos_3pi, sin_3pi]
        ring
      rw [this]
      ring
    -- Use involution pairing
    let f : ℕ → ℝ := fun k => Real.cos ((6 * k + 3 : ℝ) * π / (2 * N))
    change ∑ k ∈ Finset.range N, f k = 0
    refine Finset.sum_involution (fun k _ => N - k - 1) ?_ ?_ ?_ ?_
    · -- Show f k + f (g k) = 0
      intro k hk
      have hk' : k < N := Finset.mem_range.mp hk
      change f k + f (N - k - 1) = 0
      simp only [f]
      -- Need to show ↑(N - k - 1) = ↑N - ↑k - 1
      have h_le : k + 1 ≤ N := Nat.succ_le_of_lt hk'
      have cast_eq : ((N - k - 1 : ℕ) : ℝ) = (N : ℝ) - (k : ℝ) - 1 := by
        rw [show N - k - 1 = N - (k + 1) by omega]
        rw [Nat.cast_sub h_le]
        push_cast
        ring
      rw [cast_eq]
      exact key k hk'
    · -- Show that non-zero elements map to different elements
      intro k hk hfk
      simp only [Finset.mem_range] at hk
      intro heq
      simp only [f] at hfk
      simp only at heq
      -- If N - k - 1 = k, then f k + f k = 0, so f k = 0
      -- This happens when 2k + 1 = N
      have h_eq : 2 * k + 1 = N := by omega
      -- Then (6k+3)π/(2N) = 3(2k+1)π/(2N) = 3π/2
      have : (6 * k + 3 : ℝ) * π / (2 * N) = 3 * π / 2 := by
        have : (6 * k + 3 : ℝ) = 3 * N := by norm_cast; omega
        rw [this]
        field_simp
      -- cos(3π/2) = 0 because 3π/2 = π + π/2, so cos(3π/2) = -cos(π/2) = 0
      have cos_val : Real.cos (3 * π / 2) = 0 := by
        rw [show (3 : ℝ) * π / 2 = π + π / 2 by ring]
        rw [Real.cos_add]
        norm_num [Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two, Real.sin_pi_div_two]
      rw [this, cos_val] at hfk
      exact hfk rfl
    · -- Show g k is in range
      intro k hk
      simp only [Finset.mem_range] at hk ⊢
      omega
    · -- Show g (g k) = k (involution)
      intro k hk
      simp only [Finset.mem_range] at hk
      -- Need: N - (N - k - 1) - 1 = k
      have hk_lt : k < N := hk
      have h_le : k + 1 ≤ N := Nat.succ_le_of_lt hk_lt
      simp only
      rw [show N - k - 1 = N - (k + 1) by omega]
      have h_le2 : N - (k + 1) + 1 ≤ N := by omega
      rw [Nat.sub_sub_self h_le]
      omega
  -- Show ∑3cos((2k+1)π/(2N)) = 0 using j=1
  have sum_cos : ∑ k ∈ Finset.range N, 3 * Real.cos ((2 * k + 1 : ℝ) * π / (2 * N)) = 0 := by
    have : ∑ k ∈ Finset.range N, 3 * Real.cos ((2 * k + 1 : ℝ) * π / (2 * N)) =
           3 * ∑ k ∈ Finset.range N, Real.cos ((2 * k + 1 : ℝ) * π / (2 * N)) := by
      rw [← Finset.mul_sum]
    rw [this]
    have : ∑ k ∈ Finset.range N, Real.cos ((2 * k + 1 : ℝ) * π / (2 * N)) = 0 :=
      chebyshev_roots_sum_eq_zero N (by omega : 1 < N)
    rw [this]
    ring
  rw [sum_cos3, sum_cos]
  ring

/-- Power sum equality for j=3: both root systems sum to 0. -/
lemma powersum_j3_equality (N : ℕ) (hN : 3 < N) :
    ∑ k ∈ Finset.range N, (Real.cos (2 * π * k / N)) ^ 3 =
    ∑ k ∈ Finset.range N, (Real.cos ((2 * k + 1 : ℝ) * π / (2 * N))) ^ 3 := by
  rw [rotated_roots_sum_cube_eq N hN, chebyshev_roots_sum_cube_eq N hN]

/-- Helper lemma: Compute the exact value of power sum for rotated roots.
    Uses binomial expansion and vanishing of non-constant terms. -/
lemma rotated_roots_powersum_value (N j : ℕ) (hN : 0 < N) (hj : 0 < j) (hj' : j < N) :
    ∑ k ∈ Finset.range N, (Real.cos (2 * π * k / N)) ^ j =
    if Even j then N * (2 : ℝ) ^ (-(j : ℤ)) * (j.choose (j / 2)) else 0 := by
  -- Apply binomial expansion from PowerSums.lean with θ=0
  have h_expand := sum_cos_pow_eq_sum_binomial N j 0 hN hj'
  simp only [zero_add] at h_expand
  rw [h_expand]

  -- All non-constant terms vanish, only r = j/2 survives when j is even
  by_cases h_even : Even j
  · -- j is even: only the middle term (r = j/2) contributes
    rw [if_pos h_even]
    -- When 2r - j = 0 (i.e., r = j/2), the sum is N (constant term)
    -- All other terms vanish by sum_cos_int_multiple_vanishes
    have sum_eq : ∑ r ∈ Finset.range (j + 1), (j.choose r : ℝ) *
        ∑ k ∈ Finset.range N, Real.cos (((2 * r - j) : ℤ) * (2 * π * k / N)) =
      (j.choose (j / 2) : ℝ) * N := by
      -- Only the term where 2*r - j = 0 contributes
      -- For even j, this happens when r = j/2
      obtain ⟨m, hm⟩ := h_even
      have hj_2_dvd : 2 ∣ j := by
        use m
        rw [hm]
        ring
      have hj_div : j / 2 = m := by omega

      -- Show the sum equals the single term at r = j/2
      have : ∑ r ∈ Finset.range (j + 1), (j.choose r : ℝ) *
          ∑ k ∈ Finset.range N, Real.cos (((2 * r - j) : ℤ) * (2 * π * k / N)) =
        ∑ r ∈ Finset.range (j + 1),
          if r = j / 2 then (j.choose r : ℝ) * N else 0 := by
        apply Finset.sum_congr rfl
        intro r hr
        by_cases h_mid : r = j / 2
        · -- r = j/2: the coefficient (2r - j) = 0, so cos(0) = 1 and sum = N
          rw [if_pos h_mid, h_mid]
          have h_zero : (2 * (j / 2) - j : ℤ) = 0 := by
            -- We have j = m + m, and j / 2 = m
            have h1 : (j / 2 : ℤ) = (m : ℤ) := by exact_mod_cast hj_div
            have h2 : (j : ℤ) = (m : ℤ) + (m : ℤ) := by omega
            rw [h1, h2]; ring
          simp [h_zero]
        · -- r ≠ j/2: the coefficient is non-zero, sum vanishes
          rw [if_neg h_mid]
          have h_neq : (2 * r - j : ℤ) ≠ 0 := by
            intro h_eq
            have h_eq_nat : 2 * r = j := by omega
            have : r = j / 2 := by
              have : j = 2 * r := by omega
              rw [this, Nat.mul_div_cancel_left r (by omega : 0 < 2)]
            contradiction
          -- Need to show |2*r - j| < N
          have h_bound : |(2 * r - j : ℤ)| < N := by
            have hr_le : r ≤ j := by
              simp only [Finset.mem_range] at hr
              omega
            by_cases hr_case : 2 * r ≥ j
            · -- 2r ≥ j: |2r - j| = 2r - j ≤ 2j - j = j < N
              rw [abs_of_nonneg (Int.sub_nonneg_of_le (by omega : (j : ℤ) ≤ (2 * r : ℤ)))]
              calc (2 * r - j : ℤ)
                _ ≤ (2 * j - j : ℤ) := by omega
                _ = (j : ℤ) := by ring
                _ < (N : ℤ) := by omega
            · -- 2r < j: |2r - j| = j - 2r < j < N
              push_neg at hr_case
              rw [abs_of_neg (Int.sub_neg_of_lt (by omega : (2 * r : ℤ) < (j : ℤ)))]
              calc -(2 * r - j : ℤ)
                _ = (j - 2 * r : ℤ) := by ring
                _ ≤ (j : ℤ) := by omega
                _ < (N : ℤ) := by omega
          -- Apply the vanishing lemma
          have h_vanish := sum_cos_int_multiple_vanishes N (2 * r - j) 0 hN h_neq h_bound
          simp only [zero_add] at h_vanish
          rw [h_vanish]
          ring
      rw [this]
      simp [Finset.sum_ite_eq', Finset.mem_range]
      omega
    rw [sum_eq]
    ring
  · -- j is odd: all terms vanish (2r - j is never 0 for integer r when j is odd)
    rw [if_neg h_even]
    have sum_zero : ∑ r ∈ Finset.range (j + 1), (j.choose r : ℝ) *
        ∑ k ∈ Finset.range N, Real.cos (((2 * r - j) : ℤ) * (2 * π * k / N)) = 0 := by
      -- All terms vanish: (2r - j) is never 0 when j is odd
      apply Finset.sum_eq_zero
      intro r hr
      -- Show (2*r - j) ≠ 0
      have h_neq : (2 * r - j : ℤ) ≠ 0 := by
        intro h_eq
        have h_eq_nat : 2 * r = j := by omega
        -- This contradicts j being odd (2*r is even)
        have : Even j := ⟨r, by omega⟩
        contradiction
      -- Show |2*r - j| < N
      have h_bound : |(2 * r - j : ℤ)| < N := by
        have hr_le : r ≤ j := by
          simp only [Finset.mem_range] at hr
          omega
        by_cases hr_case : 2 * r ≥ j
        · rw [abs_of_nonneg (Int.sub_nonneg_of_le (by omega : (j : ℤ) ≤ (2 * r : ℤ)))]
          calc (2 * r - j : ℤ)
            _ ≤ (2 * j - j : ℤ) := by omega
            _ = (j : ℤ) := by ring
            _ < (N : ℤ) := by omega
        · push_neg at hr_case
          rw [abs_of_neg (Int.sub_neg_of_lt (by omega : (2 * r : ℤ) < (j : ℤ)))]
          calc -(2 * r - j : ℤ)
            _ = (j - 2 * r : ℤ) := by ring
            _ ≤ (j : ℤ) := by omega
            _ < (N : ℤ) := by omega
      -- Apply vanishing lemma
      have h_vanish := sum_cos_int_multiple_vanishes N (2 * r - j) 0 hN h_neq h_bound
      simp only [zero_add] at h_vanish
      rw [h_vanish]
      ring
    rw [sum_zero]
    ring

/-- Helper lemma: Compute the exact value of power sum for Chebyshev roots.
    Uses binomial expansion and Chebyshev orthogonality. -/
lemma chebyshev_roots_powersum_value (N j : ℕ) (hN : 0 < N) (hj : 0 < j) (hj' : j < N) :
    ∑ k ∈ Finset.range N, (Real.cos ((2 * k + 1 : ℝ) * π / (2 * N))) ^ j =
    if Even j then N * (2 : ℝ) ^ (-(j : ℤ)) * (j.choose (j / 2)) else 0 := by
  -- Apply binomial expansion from ChebyshevOrthogonality.lean
  have h_bound : j < 2 * N := by omega
  rw [ChebyshevCircles.sum_cos_pow_chebyshev_binomial N j hN hj h_bound]

  -- All non-constant terms vanish by binomial_terms_vanish_chebyshev
  by_cases h_even : Even j
  · -- j is even: only the middle term (r = j/2) contributes
    rw [if_pos h_even]
    obtain ⟨m, hm⟩ := h_even

    -- Show that only the term where r = j/2 is non-zero
    have sum_eq : ∑ r ∈ Finset.range (j + 1), (j.choose r : ℝ) *
        ∑ k ∈ Finset.range N, Real.cos ((2 * r - j : ℤ) * (2 * k + 1 : ℝ) * π / (2 * N)) =
      (j.choose (j / 2) : ℝ) * N := by
      -- Apply binomial_terms_vanish_chebyshev to show all terms except r = j/2 vanish
      have hj_2_dvd : 2 ∣ j := by
        use m
        rw [hm]
        ring
      have hj_div : j / 2 = m := by omega

      have : ∑ r ∈ Finset.range (j + 1), (j.choose r : ℝ) *
          ∑ k ∈ Finset.range N, Real.cos ((2 * r - j : ℤ) * (2 * k + 1 : ℝ) * π / (2 * N)) =
        ∑ r ∈ Finset.range (j + 1),
          if r = j / 2 then (j.choose r : ℝ) * N else 0 := by
        apply Finset.sum_congr rfl
        intro r hr
        by_cases h_mid : r = j / 2
        · -- r = j/2: cos(0 * ...) = 1, sum = N
          rw [if_pos h_mid, h_mid]
          have h_zero : (2 * (j / 2) - j : ℤ) = 0 := by
            -- We have j = m + m, and j / 2 = m
            have h1 : (j / 2 : ℤ) = (m : ℤ) := by exact_mod_cast hj_div
            have h2 : (j : ℤ) = (m : ℤ) + (m : ℤ) := by omega
            rw [h1, h2]; ring
          simp [h_zero]
        · -- r ≠ j/2: apply binomial_terms_vanish_chebyshev
          rw [if_neg h_mid]
          have h_neq : (2 * r - j : ℤ) ≠ 0 := by
            intro h_eq
            have h_eq_nat : 2 * r = j := by omega
            have : r = j / 2 := by
              have : j = 2 * r := by omega
              rw [this, Nat.mul_div_cancel_left r (by omega : 0 < 2)]
            contradiction
          have h_vanish := ChebyshevCircles.binomial_terms_vanish_chebyshev N j r hN hj' hr h_neq
          rw [h_vanish]
          ring
      rw [this]
      simp [Finset.sum_ite_eq', Finset.mem_range]
      omega
    rw [sum_eq]
    ring
  · -- j is odd: all terms vanish
    rw [if_neg h_even]
    have sum_zero : ∑ r ∈ Finset.range (j + 1), (j.choose r : ℝ) *
        ∑ k ∈ Finset.range N, Real.cos ((2 * r - j : ℤ) * (2 * k + 1 : ℝ) * π / (2 * N)) = 0 := by
      -- All terms vanish: (2r - j) is odd when j is odd, apply binomial_terms_vanish_chebyshev
      apply Finset.sum_eq_zero
      intro r hr
      -- Show (2*r - j) ≠ 0
      have h_neq : (2 * r - j : ℤ) ≠ 0 := by
        intro h_eq
        have h_eq_nat : 2 * r = j := by omega
        -- This contradicts j being odd (2*r is even)
        have : Even j := ⟨r, by omega⟩
        contradiction
      -- Apply binomial_terms_vanish_chebyshev
      have h_vanish := ChebyshevCircles.binomial_terms_vanish_chebyshev N j r hN hj' hr h_neq
      rw [h_vanish]
      ring
    rw [sum_zero]
    ring

/-- General power sum equality: For all 0 < j < N, the j-th power sum is the same
    for both rotated roots of unity and Chebyshev roots.

    This is the key theorem that allows us to conclude the two polynomials have identical
    coefficients (except for the constant term).

    **Current Status**: This theorem is stated with the correct type signature and has
    base cases j=1-6 proven. The general case for j ≥ 7 requires continuing the explicit
    proof pattern established for j=1-6.

    **Proof Strategy**: Each case follows a consistent pattern:
    1. Apply power-reduction formula: cos^j(x) expressed as sum of cos(m*x) terms
    2. For rotated roots: use `sum_cos_multiple_rotated_roots` (geometric sums of roots of unity)
    3. For Chebyshev roots, distinguish cases:
       - Odd j: involution pairing (angles sum to odd multiple of π, cosines cancel)
       - Even j: complex exponentials with geometric sums (angles sum to even multiple of π)
    4. Conclude both sums equal the same constant term

    **Key Techniques**:
    - j=1,3,5 (odd): Involution pairing with `Finset.sum_involution`
    - j=2,4,6 (even): Complex exponential sums (e.g., ∑exp(i(2k+1)π/N) = 0)
    - Power reduction: `cos_cube_formula`, `cos_four_formula`, `cos_five_formula`, `cos_six_formula`

    **Practical Note**: For the Chebyshev circles application, j < N is typically small (N ≤ 20),
    so the proven cases j=1-6 already cover most practical scenarios. Extending to j=7,8,...
    follows the same mechanical pattern. -/
theorem general_powersum_equality (N j : ℕ) (hN : 0 < N) (hj : 0 < j) (hj' : j < N) :
    ∑ k ∈ Finset.range N, (Real.cos (2 * π * k / N)) ^ j =
    ∑ k ∈ Finset.range N, (Real.cos ((2 * k + 1 : ℝ) * π / (2 * N))) ^ j := by
  -- Handle cases j = 1, 2, 3, 4, 5, 6 with existing lemmas
  match j with
  | 1 =>
    have hN' : 1 < N := by omega
    simp only [pow_one]
    exact powersum_j1_equality N hN'
  | 2 =>
    have hN' : 2 < N := by omega
    exact powersum_j2_equality N hN'
  | 3 =>
    have hN' : 3 < N := by omega
    exact powersum_j3_equality N hN'
  | 4 =>
    have hN' : 4 < N := by omega
    exact powersum_j4_equality N hN'
  | 5 =>
    have hN' : 5 < N := by omega
    exact powersum_j5_equality N hN'
  | 6 =>
    have hN' : 6 < N := by omega
    exact powersum_j6_equality N hN'
  | j' + 7 =>
    -- For j ≥ 7, use binomial expansion + orthogonality
    -- Both sums expand via binomial theorem, and all non-constant frequency terms vanish
    -- The constant terms match, giving equality
    rw [rotated_roots_powersum_value N (j' + 7) hN (by omega) (by omega)]
    rw [chebyshev_roots_powersum_value N (j' + 7) hN (by omega) (by omega)]
    -- Both sides equal the same if-then-else expression


end PowerSumEquality

end

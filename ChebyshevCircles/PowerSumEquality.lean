/-
Copyright (c) 2025 Eric. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric
-/
import Mathlib.Algebra.BigOperators.Field
import ChebyshevCircles.RootsOfUnity
import ChebyshevCircles.TrigonometricIdentities
import ChebyshevCircles.ChebyshevRoots

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

end PowerSumEquality

end

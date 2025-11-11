/-
Copyright (c) 2025 Eric. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric, Claude Code

Discrete orthogonality for Chebyshev root angles.

Proves that sums of cosines at Chebyshev angles vanish for non-zero frequencies,
which is the key property needed to extend the binomial expansion proof technique
from rotated roots to Chebyshev roots.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.Analysis.Complex.Exponential
import ChebyshevCircles.TrigonometricIdentities
import ChebyshevCircles.PowerSums

noncomputable section
open Complex Real Finset

namespace ChebyshevCircles

/-- Factor sum of exponentials at Chebyshev angles θ_k = (2k+1)π/(2N) into geometric form.
    Extracts the common phase exp(mπi/(2N)), leaving a sum of exp(kmπi/N) terms. -/
lemma sum_exp_chebyshev_angles (N m : ℕ) :
    ∑ k ∈ range N, exp ((2 * k + 1 : ℂ) * m * π * I / (2 * N)) =
    exp (m * π * I / (2 * N)) * ∑ k ∈ range N, exp (k * m * π * I / N) := by
  -- Factor out exp(mπi/(2N)) from each term
  -- (2k+1) * m * π/(2N) = m*π/(2N) + k * m * π/N
  conv_lhs => arg 2; ext k; rw [show (2 * k + 1 : ℂ) * m * π * I / (2 * N) =
      m * π * I / (2 * N) + k * m * π * I / N by
    field_simp
    ring]
  simp_rw [Complex.exp_add, Finset.mul_sum]

/-- Sum of cosines at Chebyshev angles vanishes for non-zero odd frequencies.

    Proof strategy: Chebyshev angles satisfy φ_k + φ_{N-1-k} = π.
    For odd m, cos(m·φ_{N-1-k}) = cos(m·(π - φ_k)) = -cos(m·φ_k).
    Terms pair up and cancel via the involution k ↦ N-1-k. -/
lemma sum_cos_chebyshev_angles_vanishes (N : ℕ) (m : ℤ) (hN : 0 < N)
    (hm : m ≠ 0) (hm_odd : Odd m) (hm_bound : |m| < 2 * N) :
    ∑ k ∈ range N, Real.cos (m * (2 * k + 1 : ℝ) * π / (2 * N)) = 0 := by
  -- Define the term we're summing
  let f : ℕ → ℝ := fun k ↦ Real.cos (m * (2 * k + 1 : ℝ) * π / (2 * N))

  -- We'll show the sum vanishes by pairing terms using symmetry
  -- Key observation: φ_k + φ_{N-1-k} = (2k+1)π/(2N) + (2(N-1-k)+1)π/(2N) = π

  -- First, prove the pairing lemma: f(k) + f(N-1-k) = 0
  have pair_sum_zero : ∀ k ∈ range N, f k + f (N - 1 - k) = 0 := by
    intro k hk
    simp only [f]
    rw [mem_range] at hk
    have hk_le : k ≤ N - 1 := Nat.le_pred_of_lt hk

    -- First establish the cast identity for (N - 1 - k)
    have cast_eq : ((N - 1 - k) : ℝ) = N - 1 - k := by
      rfl

    -- The key insight: (2*(N-1-k)+1)*π/(2N) + (2*k+1)*π/(2N) = π
    -- So cos(m * first_angle) = cos(m*(π - second_angle)) = (-1)^m * cos(m*second_angle)

    -- Simplify the angle for N-1-k
    have angle_identity : (2 * (N - 1 - k : ℝ) + 1) * π /
      (2 * N) + (2 * k + 1) * π / (2 * N) = π := by
      have h2N_ne : (2 * N : ℝ) ≠ 0 := by
        have : (0 : ℝ) < N := Nat.cast_pos.mpr hN
        linarith
      rw [← add_div, ← add_mul]
      -- Show the sum of coefficients equals 2N
      have coeff_sum : 2 * (N - 1 - k : ℝ) + 1 + (2 * k + 1) = 2 * N := by
        have : (2 * (N - 1 - k) + 1 : ℕ) + (2 * k + 1) = 2 * N := by omega
        linarith
      rw [coeff_sum]
      field_simp

    -- Rewrite second angle as π minus first angle
    have second_angle : (2 * (N - 1 - k : ℝ) + 1) * π / (2 * N) =
      π - (2 * k + 1) * π / (2 * N) := by
      linarith [angle_identity]

    -- Substitute and use cosine identity
    -- Need to show the second cosine argument can be rewritten
    have key : m * (2 * ((N - 1 - k) : ℝ) + 1) * π / (2 * N) =
      m * (π - (2 * k + 1) * π / (2 * N)) := by
      calc m * (2 * (N - 1 - k : ℝ) + 1) * π / (2 * N)
          = m * ((2 * (N - 1 - k : ℝ) + 1) * π / (2 * N)) := by ring
        _ = m * (π - (2 * k + 1) * π / (2 * N)) := by rw [second_angle]

    -- Rewrite the goal to use the same casting as key
    have cast_adjust : (2 * ↑(N - 1 - k) + 1 : ℝ) = 2 * (↑N - 1 - ↑k) + 1 := by
      congr 1
      have : k ≤ N - 1 := hk_le
      rw [Nat.cast_sub this, Nat.cast_sub (Nat.one_le_of_lt hN)]
      simp
    rw [cast_adjust, key, mul_sub, Real.cos_int_mul_pi_sub]

    -- For odd m, (-1)^m = -1
    have neg_one_pow : (-1 : ℝ) ^ m = -1 := by
      obtain ⟨k, rfl⟩ := hm_odd
      rw [zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
      rw [zpow_mul, zpow_ofNat]
      norm_num

    rw [neg_one_pow]
    ring_nf

  -- Apply the sum involution: terms pair up and cancel
  -- We use the fact that g(k) = N-1-k is an involution and f(k) + f(g(k)) = 0

  -- The sum equals its own negation, hence it must be zero
  suffices h : ∑ k ∈ range N, f k = -∑ k ∈ range N, f k by
    linarith [h]

  -- Reindex the sum using the involution k ↦ N - 1 - k
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_bij (fun k _ => N - 1 - k) ?_ ?_ ?_ ?_
  · -- Prove ∀ k ∈ range N, N - 1 - k ∈ range N
    intro k hk
    simp [mem_range] at hk ⊢
    omega
  · -- Prove injectivity
    intro a₁ ha₁ a₂ ha₂ heq
    simp only at heq
    have h1 : a₁ < N := by simp [mem_range] at ha₁; exact ha₁
    have h2 : a₂ < N := by simp [mem_range] at ha₂; exact ha₂
    -- N - 1 - a₁ = N - 1 - a₂ implies a₁ = a₂
    omega
  · -- Prove surjectivity
    intro b hb
    use N - 1 - b
    refine ⟨?_, ?_⟩
    · simp [mem_range] at hb ⊢
      have : b < N := hb
      omega
    · simp only
      have : b < N := by simp [mem_range] at hb; exact hb
      omega
  · -- Prove ∀ k ∈ range N, -f k = f (N - 1 - k)
    intro k hk
    have := pair_sum_zero k hk
    linarith

/-- Euler's formula for cosine: cos(x) = Re((e^{ix} + e^{-ix})/2).
    Bridges real trigonometric sums and complex exponential manipulations. -/
lemma cos_as_exp_chebyshev (x : ℝ) :
    Real.cos x = ((Complex.exp (x * Complex.I) + Complex.exp (-(x * Complex.I))) / 2).re := by
  rw [show (Complex.exp (↑x * Complex.I) + Complex.exp (-(↑x * Complex.I))) / 2 =
    Complex.cos (x : ℂ) by
    rw [Complex.cos]
    congr 2
    congr 1
    rw [neg_mul]]
  exact Complex.cos_ofReal_re x

/-- Binomial expansion of (e^{ix} + e^{-ix})^j = ∑ C(j,r) e^{i(2r-j)x}.
    Powers of the sum expand into exponentials with frequency shifts (2r-j). -/
lemma exp_add_exp_pow_chebyshev (x : ℂ) (j : ℕ) :
    (Complex.exp (x * Complex.I) + Complex.exp (-(x * Complex.I))) ^ j =
    ∑ r ∈ range (j + 1), (j.choose r : ℂ) * Complex.exp ((2 * r - j : ℤ) * x * Complex.I) := by
  rw [Commute.add_pow (Commute.all _ _)]
  apply Finset.sum_congr rfl
  intro r hr
  have hr_le : r ≤ j := by simp only [mem_range] at hr; omega
  rw [← Complex.exp_nat_mul (n := r), ← Complex.exp_nat_mul (n := j - r)]
  rw [← Complex.exp_add, mul_comm]
  congr 1
  simp only [Nat.cast_sub hr_le]
  congr 1
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
  ring

/-- Lemma 5: Express power sum of cosines at Chebyshev angles as binomial expansion.

    This adapts the binomial expansion from PowerSums.lean to Chebyshev root angles.
    The key difference is that angles are (2k+1)π/(2N) instead of φ + 2πk/N. -/
lemma sum_cos_pow_chebyshev_binomial (N j : ℕ) (_hN : 0 < N) (_hj : 0 < j) (_hj' : j < 2 * N) :
    ∑ k ∈ range N, (Real.cos ((2 * k + 1 : ℝ) * π / (2 * N))) ^ j =
    (2 : ℝ) ^ (-(j : ℤ)) * ∑ r ∈ range (j + 1), (j.choose r : ℝ) *
    ∑ k ∈ range N, Real.cos ((2 * r - j : ℤ) * (2 * k + 1 : ℝ) * π / (2 * N)) := by
  -- Follows sum_cos_pow_eq_sum_binomial from PowerSums.lean
  simp only [cos_as_exp_chebyshev]

  -- Pull power inside re: (z.re)^j = (z^j).re when z is real
  have h_re_pow : ∀ k, ((Complex.exp (↑((2 * k + 1 : ℝ) * π / (2 * N)) * Complex.I) +
      Complex.exp (-(↑((2 * k + 1 : ℝ) * π / (2 * N)) * Complex.I))) / 2).re ^ j =
    (((Complex.exp (↑((2 * k + 1 : ℝ) * π / (2 * N)) * Complex.I) +
      Complex.exp (-(↑((2 * k + 1 : ℝ) * π / (2 * N)) * Complex.I))) / 2) ^ j).re := by
    intro k
    set z := (Complex.exp (↑((2 * k + 1 : ℝ) * π / (2 * N)) * Complex.I) +
        Complex.exp (-(↑((2 * k + 1 : ℝ) * π / (2 * N)) * Complex.I))) / 2 with z_def
    have h_real : z.im = 0 := by
      rw [z_def]
      have h1 : (Complex.exp (↑((2 * k + 1 : ℝ) * π / (2 * N)) * Complex.I) +
          Complex.exp (-(↑((2 * k + 1 : ℝ) * π / (2 * N)) * Complex.I))).im = 0 := by
        rw [Complex.add_im, Complex.exp_ofReal_mul_I_im]
        have : (Complex.exp (-(↑((2 * k + 1 : ℝ) * π / (2 * N)) * Complex.I))).im =
          Real.sin (-((2 * k + 1 : ℝ) * π / (2 * N))) := by
          rw [show -(↑((2 * k + 1 : ℝ) * π / (2 * N)) * Complex.I) =
            (↑(-((2 * k + 1 : ℝ) * π / (2 * N))) : ℂ) * Complex.I by
            apply Complex.ext <;> simp]
          exact Complex.exp_ofReal_mul_I_im _
        rw [this, Real.sin_neg]
        ring
      rw [Complex.div_im, h1]
      simp
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

  simp only [div_pow]

  rw [show ∑ x ∈ range N, (Complex.exp (↑((2 * ↑x + 1) * π / (2 * ↑N)) * Complex.I) +
      Complex.exp (-(↑((2 * ↑x + 1) * π / (2 * ↑N)) * Complex.I))) ^ j / (2 : ℂ) ^ j =
    ∑ x ∈ range N, (∑ r ∈ range (j + 1), (j.choose r : ℂ) *
      Complex.exp ((2 * r - j : ℤ) * ↑((2 * ↑x + 1) * π / (2 * ↑N)) * Complex.I)) / (2 : ℂ) ^ j by
    apply Finset.sum_congr rfl
    intro i _
    rw [exp_add_exp_pow_chebyshev (↑((2 * ↑i + 1) * π / (2 * ↑N))) j]]

  rw [← Finset.sum_div, div_eq_mul_inv, mul_comm]

  rw [show ((2 : ℂ) ^ j)⁻¹ = (2 : ℂ) ^ (-(j : ℤ)) by
    rw [← zpow_natCast, ← zpow_neg_one, ← zpow_mul]
    norm_num]

  rw [Complex.mul_re]

  have h_re : ((2 : ℂ) ^ (-(j : ℤ))).re = (2 : ℝ) ^ (-(j : ℤ)) := by
    have : (2 : ℂ) = (↑(2 : ℝ) : ℂ) := rfl
    rw [this, ← Complex.ofReal_zpow, Complex.ofReal_re]
  have h_im : ((2 : ℂ) ^ (-(j : ℤ))).im = 0 := by
    have : (2 : ℂ) = (↑(2 : ℝ) : ℂ) := rfl
    rw [this, ← Complex.ofReal_zpow, Complex.ofReal_im]
  rw [h_re, h_im]
  simp

  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [← Finset.mul_sum]
  congr 1

  rw [← Complex.re_sum, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro k _

  -- Show exp(...).re = (exp(...).re + exp(-...).re) / 2
  -- First normalize the LHS to match RHS form
  have lhs_norm : (Complex.exp ((2 * ↑r - ↑j) * ((2 * ↑k + 1) * ↑π / (2 * ↑N)) * Complex.I)).re =
      (Complex.exp ((2 * ↑r - ↑j) * (2 * ↑k + 1) * ↑π / (2 * ↑N) * Complex.I)).re := by
    congr 1
    ring_nf

  rw [lhs_norm]

  -- Now show: exp(m*φ*I).re = (exp(m*φ*I).re + exp(-m*φ*I).re) / 2
  have h1 : (Complex.exp ((2 * ↑r - ↑j) * (2 * ↑k + 1) * ↑π / (2 * ↑N) * Complex.I)).re =
    Real.cos ((2 * ↑r - ↑j) * (2 * ↑k + 1) * π / (2 * ↑N)) := by
    have : (2 * ↑r - ↑j) * (2 * ↑k + 1) * ↑π / (2 * ↑N) * Complex.I =
      ↑((2 * ↑r - ↑j) * (2 * ↑k + 1) * π / (2 * ↑N)) * Complex.I := by
      push_cast
      ring
    rw [this, Complex.exp_ofReal_mul_I_re]
  have h2 : (Complex.exp (-((2 * ↑r - ↑j) * (2 * ↑k + 1) * ↑π / (2 * ↑N) * Complex.I))).re =
    Real.cos ((2 * ↑r - ↑j) * (2 * ↑k + 1) * π / (2 * ↑N)) := by
    have : -((2 * ↑r - ↑j) * (2 * ↑k + 1) * ↑π / (2 * ↑N) * Complex.I) =
      ↑(-((2 * ↑r - ↑j) * (2 * ↑k + 1) * π / (2 * ↑N))) * Complex.I := by
      push_cast
      ring
    rw [this, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  rw [h1, h2]
  ring

/-- Lemma 5b: Sum of cosines at Chebyshev angles vanishes for non-zero even frequencies.

    For even m with 0 < m < N, the sum vanishes using complex exponentials and geometric sums.
    The key insight: m even means we can write m = 2s and use geometric sum of N-th roots. -/
lemma sum_cos_chebyshev_angles_even_vanishes (N m : ℕ)
    (hN : 0 < N) (hm : 0 < m) (hm_even : Even m) (hm_bound : m < N) :
    ∑ k ∈ range N, Real.cos (m * (2 * k + 1 : ℝ) * π / (2 * N)) = 0 := by
  -- Extract s from m = 2s
  obtain ⟨s, hs⟩ := hm_even
  rw [hs]

  -- Bound on s
  have hs_pos : 0 < s := by omega
  have hs_bound : s < N := by omega

  -- First convert s + s to 2 * s
  conv_lhs => arg 2; ext k; arg 1; rw [show (s + s : ℕ) = 2 * s by omega]

  -- Push down the cast and simplify
  conv_lhs => arg 2; ext k; arg 1; rw [show ((2 * s : ℕ) : ℝ) = 2 * (s : ℝ) by norm_cast]

  -- Simplify 2s * (2k+1) * π / (2N) = s * (2k+1) * π / N
  conv_lhs => arg 2; ext k; arg 1; rw [show (2 * (s : ℝ)) * (2 * k + 1 : ℝ) * π / (2 * N) =
      (s : ℝ) * (2 * k + 1 : ℝ) * π / N by field_simp]

  -- Now prove: ∑ k, cos(s*(2k+1)*π/N) = 0 using complex exponentials
  -- First prove the complex exponential sum is zero
  have geom_sum_zero : ∑ k ∈ range N, Complex.exp ((s * k : ℕ) * (2 * π * Complex.I / N)) = 0 := by
    -- Let ω = exp(2πi/N), primitive N-th root
    let ω := Complex.exp (2 * π * Complex.I / N)
    have ω_prim : IsPrimitiveRoot ω N := Complex.isPrimitiveRoot_exp N (by omega)

    -- Rewrite as sum of powers of ω^s
    have h_rewrite : ∑ k ∈ range N, Complex.exp ((s * k : ℕ) * (2 * π * Complex.I / N)) =
        ∑ k ∈ range N, ω ^ (s * k) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Complex.exp_nat_mul]
    rw [h_rewrite]

    conv_lhs =>
      arg 2
      ext k
      rw [pow_mul]

    -- Show ω^s ≠ 1
    have ωs_ne_one : ω ^ s ≠ 1 := by
      intro h_eq
      have h_div : N ∣ s := (ω_prim.pow_eq_one_iff_dvd s).mp h_eq
      have : N ≤ s := Nat.le_of_dvd hs_pos h_div
      omega

    -- Show (ω^s)^N = 1
    have ωs_pow_N : (ω ^ s) ^ N = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, ω_prim.pow_eq_one, one_pow]

    -- Geometric sum
    have h_geom : (ω ^ s - 1) * ∑ k ∈ range N, (ω ^ s) ^ k = (ω ^ s) ^ N - 1 :=
      mul_geom_sum (ω ^ s) N
    rw [ωs_pow_N] at h_geom
    have : (ω ^ s - 1) * ∑ k ∈ range N, (ω ^ s) ^ k = 0 := by
      rw [h_geom]; ring
    exact eq_zero_of_ne_zero_of_mul_left_eq_zero (sub_ne_zero_of_ne ωs_ne_one) this

  have complex_sum :
      ∑ k ∈ range N, Complex.exp (Complex.I * ((s : ℝ) * (2 * k + 1) * π / N)) = 0 := by
    -- Factor: s*(2k+1)*π/N = s*π/N + s*2k*π/N
    calc ∑ k ∈ range N, Complex.exp (Complex.I * ((s : ℝ) * (2 * k + 1) * π / N))
        = ∑ k ∈ range N, Complex.exp (Complex.I * (s : ℝ) * π / N) *
            Complex.exp (Complex.I * ((s : ℝ) * (2 * k) * π / N)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [← Complex.exp_add]
          congr 1
          push_cast
          ring
      _ = Complex.exp (Complex.I * (s : ℝ) * π / N) *
            ∑ k ∈ range N, Complex.exp (Complex.I * ((s : ℝ) * (2 * k) * π / N)) := by
          rw [Finset.mul_sum]
      _ = Complex.exp (Complex.I * (s : ℝ) * π / N) *
            ∑ k ∈ range N, Complex.exp ((s * k : ℕ) * (2 * π * Complex.I / N)) := by
          congr 2
          funext k
          congr 1
          push_cast
          ring
      _ = Complex.exp (Complex.I * (s : ℝ) * π / N) * 0 := by rw [geom_sum_zero]
      _ = 0 := by simp

  -- Convert cosine to exponential and use complex_sum
  have cos_eq : ∀ k : ℕ, Real.cos ((s : ℝ) * (2 * k + 1) * π / N) =
      (Complex.exp (Complex.I * ((s : ℝ) * (2 * k + 1) * π / N))).re := by
    intro k
    have h1 : (Complex.I * (((s : ℝ) * (2 * k + 1) * π / N) : ℂ)) =
        ((((s : ℝ) * (2 * k + 1) * π / N) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [show (Complex.I * ((s : ℝ) * (2 * k + 1) * π / N) : ℂ) =
        Complex.I * (((s : ℝ) * (2 * k + 1) * π / N) : ℂ) by push_cast; rfl]
    rw [h1]
    exact (Complex.exp_ofReal_mul_I_re _).symm

  simp_rw [cos_eq]
  rw [← Complex.re_sum, complex_sum]
  simp

/-- Lemma 6: All non-constant binomial terms vanish for Chebyshev angles.

    This shows that when (2r - j) ≠ 0, the sum of cosines vanishes because:
    1. (2r - j) is odd (when non-zero and j odd) OR even (when j even)
    2. |2r - j| < 2N (from the bounds on j and r)
    3. Apply the appropriate vanishing lemma -/
lemma binomial_terms_vanish_chebyshev (N j r : ℕ) (hN : 0 < N) (hj' : j < N)
    (hr : r ∈ range (j + 1)) (hr_neq : (2 * r - j : ℤ) ≠ 0) :
    ∑ k ∈ range N, Real.cos ((2 * r - j : ℤ) * (2 * k + 1 : ℝ) * π / (2 * N)) = 0 := by
  -- We need to show:
  -- 1. (2r - j) is odd
  -- 2. |2r - j| < 2N
  -- Then apply sum_cos_chebyshev_angles_vanishes

  -- First establish the bound: r ≤ j
  have hr_le : r ≤ j := by
    simp only [mem_range] at hr
    omega

  -- Split by parity of j
  by_cases h_parity : Odd j
  · -- Case 1: j is odd, so (2r - j) is odd
    have h_odd : Odd (2 * r - j : ℤ) := by
      obtain ⟨m, hm⟩ := h_parity
      use (r : ℤ) - m - 1
      have : (j : ℤ) = 2 * m + 1 := by exact_mod_cast hm
      calc (2 * r - j : ℤ)
        _ = 2 * (r : ℤ) - (2 * m + 1) := by rw [this]
        _ = 2 * ((r : ℤ) - m - 1) + 1 := by ring

    -- Prove |2r - j| < 2N
    have h_bound : |(2 * r - j : ℤ)| < 2 * N := by
      by_cases hr_case : 2 * r ≥ j
      · rw [abs_of_nonneg (Int.sub_nonneg_of_le (by omega : (j : ℤ) ≤ (2 * r : ℤ)))]
        calc (2 * r - j : ℤ)
          _ ≤ (2 * j - j : ℤ) := by omega
          _ = (j : ℤ) := by ring
          _ < (N : ℤ) := by omega
          _ < (2 * N : ℤ) := by omega
      · push_neg at hr_case
        rw [abs_of_neg (Int.sub_neg_of_lt (by omega : (2 * r : ℤ) < (j : ℤ)))]
        calc -(2 * r - j : ℤ)
          _ = (j - 2 * r : ℤ) := by ring
          _ ≤ (j : ℤ) := by omega
          _ < (N : ℤ) := by omega
          _ < (2 * N : ℤ) := by omega

    -- Apply odd vanishing lemma
    convert sum_cos_chebyshev_angles_vanishes N (2 * r - j) hN hr_neq h_odd h_bound using 2

  · -- Case 2: j is even, so (2r - j) is even
    have j_even : Even j := Nat.not_odd_iff_even.mp h_parity
    have h_even : Even (2 * r - j : ℤ) := by
      obtain ⟨m, hm⟩ := j_even
      use (r : ℤ) - m
      have : (j : ℤ) = (m + m : ℕ) := by simp [hm]
      calc (2 * r - j : ℤ)
        _ = 2 * (r : ℤ) - ((m : ℤ) + (m : ℤ)) := by rw [this]; simp
        _ = 2 * (r : ℤ) - 2 * (m : ℤ) := by ring
        _ = ((r : ℤ) - (m : ℤ)) + ((r : ℤ) - (m : ℤ)) := by ring

    -- Convert to natural number case
    -- Need to handle both positive and negative cases of (2r - j)
    by_cases h_sign : 2 * r ≥ j
    · -- Positive case: 2r - j ≥ 0
      have h_pos : 0 ≤ (2 * r - j : ℤ) := Int.sub_nonneg_of_le (by omega : (j : ℤ) ≤ (2 * r : ℤ))
      obtain ⟨m_nat, hm_nat⟩ := Int.eq_ofNat_of_zero_le h_pos

      -- Show m_nat is even and bounded
      have hm_even : Even m_nat := by
        have := h_even
        rwa [hm_nat, Int.even_coe_nat] at this

      have hm_pos : 0 < m_nat := by
        by_contra h
        push_neg at h
        have : m_nat = 0 := by omega
        rw [this] at hm_nat
        simp at hm_nat
        omega

      have hm_bound : m_nat < N := by
        have : (m_nat : ℤ) < N := by
          calc (m_nat : ℤ)
            _ = 2 * r - j := by rw [← hm_nat]
            _ ≤ 2 * j - j := by omega
            _ = j := by ring
            _ < N := by omega
        omega

      -- Apply even vanishing lemma
      calc ∑ k ∈ range N, Real.cos ((2 * r - j : ℤ) * (2 * k + 1 : ℝ) * π / (2 * N))
          _ = ∑ k ∈ range N, Real.cos ((m_nat : ℝ) * (2 * k + 1 : ℝ) * π / (2 * N)) := by
              congr 1; ext k; congr 1
              rw [hm_nat]
              norm_cast
          _ = 0 := sum_cos_chebyshev_angles_even_vanishes N m_nat hN hm_pos hm_even hm_bound

    · -- Negative case: 2r - j < 0, use cos(-x) = cos(x)
      have h_neg : (2 * r - j : ℤ) < 0 := Int.sub_neg_of_lt (by omega : (2 * r : ℤ) < (j : ℤ))
      have h_pos : 0 < -(2 * r - j : ℤ) := by omega

      obtain ⟨m_nat, hm_nat⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ -(2 * r - j : ℤ))

      -- Show m_nat is even and bounded
      have hm_even : Even m_nat := by
        have : Even (-(2 * r - j : ℤ)) := by
          obtain ⟨k, hk⟩ := h_even
          use -k
          calc -(2 * r - j : ℤ)
            _ = -(k + k) := by rw [hk]
            _ = -k + -k := by ring
        rwa [hm_nat, Int.even_coe_nat] at this

      have hm_pos : 0 < m_nat := by
        have : (m_nat : ℤ) ≠ 0 := by
          intro h
          rw [h] at hm_nat
          simp at hm_nat
          omega
        omega

      have hm_bound : m_nat < N := by
        have : (m_nat : ℤ) < N := by
          calc (m_nat : ℤ)
            _ = -(2 * r - j) := by rw [← hm_nat]
            _ = j - 2 * r := by ring
            _ ≤ j := by omega
            _ < N := by omega
        omega

      -- Apply even vanishing lemma with cos(-x) = cos(x)
      calc ∑ k ∈ range N, Real.cos ((2 * r - j : ℤ) * (2 * k + 1 : ℝ) * π / (2 * N))
          _ = ∑ k ∈ range N, Real.cos ((-(m_nat : ℤ)) * (2 * k + 1 : ℝ) * π / (2 * N)) := by
              congr 1; ext k; congr 1
              have : (2 * r - j : ℤ) = -(m_nat : ℤ) := by rw [← hm_nat]; ring
              rw [this]
              norm_cast
          _ = ∑ k ∈ range N, Real.cos ((m_nat : ℝ) * (2 * k + 1 : ℝ) * π / (2 * N)) := by
              congr 1; ext k
              have : ((-(m_nat : ℤ)) * (2 * k + 1 : ℝ) * π / (2 * N) : ℝ) =
                  -((m_nat : ℤ) * (2 * k + 1 : ℝ) * π / (2 * N)) := by
                push_cast; ring
              rw [this, Real.cos_neg]
              norm_cast
          _ = 0 := sum_cos_chebyshev_angles_even_vanishes N m_nat hN hm_pos hm_even hm_bound

end ChebyshevCircles

end

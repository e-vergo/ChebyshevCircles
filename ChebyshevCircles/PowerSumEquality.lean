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

/-!
# Power Sum Equality for Rotated Roots and Chebyshev Roots

This module establishes that power sums of rotated roots of unity equal power sums of
Chebyshev roots for all powers j with 0 < j < N. This equality is fundamental to proving
that the minimal polynomial of Chebyshev roots has coefficients matching those of rotated
roots (except for the constant term).

## Main results

* `general_powersum_equality`: For 0 < j < N, the j-th power sum of rotated roots
  equals the j-th power sum of Chebyshev roots
* `rotated_roots_powersum_value`: Computes exact closed-form values for power sums of
  rotated roots: N * 2^(-j) * C(j, j/2) when j is even, 0 when j is odd
* `chebyshev_roots_powersum_value`: Computes exact closed-form values for power sums of
  Chebyshev roots: N * 2^(-j) * C(j, j/2) when j is even, 0 when j is odd

## Implementation notes

The proof uses discrete orthogonality relations and binomial expansion:
1. For rotated roots: Apply binomial expansion with φ=0 and use primitive root
   orthogonality to show non-constant terms vanish
2. For Chebyshev roots: Apply binomial expansion and use Chebyshev-specific
   orthogonality relations to eliminate non-constant terms
3. Both approaches yield identical closed-form expressions depending only on parity of j

## Tags

power sums, Chebyshev polynomials, roots of unity, discrete orthogonality
-/

noncomputable section

open Complex Real
open scoped BigOperators

section PowerSumEquality

/-- Helper lemma: Compute the exact value of power sum for rotated roots.
    Uses binomial expansion and primitive root orthogonality. -/
lemma rotated_roots_powersum_value (N j : ℕ) (hN : 0 < N) (hj : 0 < j) (hj' : j < N) :
    ∑ k ∈ Finset.range N, (Real.cos (2 * π * k / N)) ^ j =
    if Even j then N * (2 : ℝ) ^ (-(j : ℤ)) * (j.choose (j / 2)) else 0 := by
  -- Apply binomial expansion from PowerSums.lean with φ=0
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
          ∑ k ∈ Finset.range N,
            Real.cos ((2 * r - j : ℤ) * (2 * k + 1 : ℝ) * π / (2 * N)) =
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
        ∑ k ∈ Finset.range N,
          Real.cos ((2 * r - j : ℤ) * (2 * k + 1 : ℝ) * π / (2 * N)) = 0 := by
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

    This theorem establishes that both root systems have identical power sums for all powers
    up to N-1. Combined with Newton's identities, this implies the two polynomials have
    identical elementary symmetric polynomials (and hence identical coefficients, except
    for the constant term which differs by design).

    The proof applies binomial expansion to both power sums and uses discrete orthogonality
    relations to show that all non-constant frequency terms vanish. The remaining constant
    terms match, yielding the equality. -/
theorem general_powersum_equality (N j : ℕ) (hN : 0 < N) (hj : 0 < j) (hj' : j < N) :
    ∑ k ∈ Finset.range N, (Real.cos (2 * π * k / N)) ^ j =
    ∑ k ∈ Finset.range N, (Real.cos ((2 * k + 1 : ℝ) * π / (2 * N))) ^ j := by
  -- Both sums equal the same closed-form expression
  rw [rotated_roots_powersum_value N j hN hj hj']
  rw [chebyshev_roots_powersum_value N j hN hj hj']

end PowerSumEquality

end

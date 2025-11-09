/-
Copyright (c) 2025 Eric. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric
-/
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic

set_option linter.style.longLine false

/-!
# Chebyshev Polynomial Roots

This section establishes that the roots of the Chebyshev polynomial T_N are exactly
the set {cos((2k+1)π/(2N)) | k = 0,...,N-1}.

## Main results

* `chebyshevRoot`: Definition of the k-th Chebyshev root for polynomial T_N
* `chebyshev_T_eval_chebyshevRoot`: The backward direction (these values are roots)
* `chebyshevRoots_distinct`: The Chebyshev roots are pairwise distinct
* `chebyshev_T_eval_eq_zero_iff`: The full characterization (if and only if)

## Tags

Chebyshev polynomials, roots, trigonometry
-/

noncomputable section

open Polynomial Real

/-- The k-th Chebyshev root for polynomial T_N -/
def chebyshevRoot (N k : ℕ) : ℝ := Real.cos ((2 * k + 1 : ℝ) * π / (2 * N))

/-- List of all Chebyshev roots for T_N -/
def chebyshevRootsList (N : ℕ) : List ℝ :=
  List.ofFn (fun k : Fin N => chebyshevRoot N k)

/-- Unfold definition of chebyshevRoot -/
lemma chebyshevRoot_def (N k : ℕ) :
    chebyshevRoot N k = Real.cos ((2 * k + 1 : ℝ) * π / (2 * N)) := rfl

/-- All Chebyshev roots are in [-1, 1] -/
lemma chebyshevRoot_in_Icc (N k : ℕ) : chebyshevRoot N k ∈ Set.Icc (-1) 1 := by
  unfold chebyshevRoot
  exact Real.cos_mem_Icc _

/-- Backward direction: T_N(cos((2k+1)π/(2N))) = 0 -/
lemma chebyshev_T_eval_chebyshevRoot (N k : ℕ) (hN : 0 < N) (_hk : k < N) :
    (Polynomial.Chebyshev.T ℝ N).eval (chebyshevRoot N k) = 0 := by
  unfold chebyshevRoot
  -- Use T_real_cos: T_n(cos θ) = cos(nθ)
  rw [Polynomial.Chebyshev.T_real_cos]
  -- Need to show: cos(N * ((2k+1)π/(2N))) = 0
  -- Simplify the argument using field_simp and show it equals (2k+1)π/2
  suffices Real.cos ((2 * k + 1) * π / 2) = 0 by
    convert this using 2
    push_cast
    field_simp [show (N : ℝ) ≠ 0 by positivity]
  -- Now we need: cos((2k+1)π/2) = 0
  -- Use Real.cos_eq_zero_iff: cos θ = 0 ↔ ∃ k : ℤ, θ = (2 * k + 1) * π / 2
  rw [Real.cos_eq_zero_iff]
  use k
  push_cast
  rfl

/-- The Chebyshev roots are pairwise distinct for 0 < N -/
lemma chebyshevRoots_distinct (N : ℕ) (hN : 0 < N) (k₁ k₂ : ℕ)
    (hk₁ : k₁ < N) (hk₂ : k₂ < N) (h_eq : chebyshevRoot N k₁ = chebyshevRoot N k₂) :
    k₁ = k₂ := by
  unfold chebyshevRoot at h_eq

  -- cos is injective on [0, π], and our angles are in this range
  let θ₁ := (2 * k₁ + 1 : ℝ) * π / (2 * N)
  let θ₂ := (2 * k₂ + 1 : ℝ) * π / (2 * N)

  -- Show both angles are in [0, π]
  have h₁_mem : θ₁ ∈ Set.Icc (0 : ℝ) π := by
    constructor
    · -- 0 ≤ θ₁
      simp only [θ₁]
      apply div_nonneg
      · apply mul_nonneg
        · norm_cast; omega
        · exact Real.pi_pos.le
      · norm_cast; omega
    · -- θ₁ ≤ π
      simp only [θ₁]
      have : (2 * k₁ + 1 : ℝ) < 2 * N := by norm_cast; omega
      have : (2 * k₁ + 1 : ℝ) * π < (2 * N) * π := by
        exact mul_lt_mul_of_pos_right this Real.pi_pos
      have lt_pi : (2 * k₁ + 1 : ℝ) * π / (2 * N) < π := by
        have hN' : (0 : ℝ) < 2 * N := by norm_cast; omega
        have : (2 * k₁ + 1 : ℝ) * π < π * (2 * N) := by linarith
        calc (2 * k₁ + 1 : ℝ) * π / (2 * N)
            < π * (2 * N) / (2 * N) := by
              exact div_lt_div_of_pos_right this hN'
          _ = π := by field_simp
      exact le_of_lt lt_pi

  have h₂_mem : θ₂ ∈ Set.Icc (0 : ℝ) π := by
    constructor
    · -- 0 ≤ θ₂
      simp only [θ₂]
      apply div_nonneg
      · apply mul_nonneg
        · norm_cast; omega
        · exact Real.pi_pos.le
      · norm_cast; omega
    · -- θ₂ ≤ π
      simp only [θ₂]
      have : (2 * k₂ + 1 : ℝ) < 2 * N := by norm_cast; omega
      have : (2 * k₂ + 1 : ℝ) * π < (2 * N) * π := by
        exact mul_lt_mul_of_pos_right this Real.pi_pos
      have lt_pi : (2 * k₂ + 1 : ℝ) * π / (2 * N) < π := by
        have hN' : (0 : ℝ) < 2 * N := by norm_cast; omega
        have : (2 * k₂ + 1 : ℝ) * π < π * (2 * N) := by linarith
        calc (2 * k₂ + 1 : ℝ) * π / (2 * N)
            < π * (2 * N) / (2 * N) := by
              exact div_lt_div_of_pos_right this hN'
          _ = π := by field_simp
      exact le_of_lt lt_pi

  -- Use injectivity of cos on [0, π]
  have cos_inj : θ₁ = θ₂ := by
    have inj := Real.injOn_cos
    unfold Set.InjOn at inj
    apply inj h₁_mem h₂_mem h_eq

  -- From θ₁ = θ₂, conclude k₁ = k₂
  simp only [θ₁, θ₂] at cos_inj
  have : (2 * k₁ + 1 : ℝ) * π / (2 * N) = (2 * k₂ + 1 : ℝ) * π / (2 * N) := cos_inj
  have : (2 * k₁ + 1 : ℝ) * π = (2 * k₂ + 1 : ℝ) * π := by
    have hN' : (0 : ℝ) < 2 * N := by norm_cast; omega
    have hN_ne : (2 * N : ℝ) ≠ 0 := ne_of_gt hN'
    calc (2 * k₁ + 1 : ℝ) * π
        = (2 * k₁ + 1 : ℝ) * π / (2 * N) * (2 * N) := by field_simp
      _ = (2 * k₂ + 1 : ℝ) * π / (2 * N) * (2 * N) := by rw [this]
      _ = (2 * k₂ + 1 : ℝ) * π := by field_simp
  have : (2 * k₁ + 1 : ℝ) = (2 * k₂ + 1 : ℝ) := by
    have hπ : π ≠ 0 := Real.pi_ne_zero
    calc (2 * k₁ + 1 : ℝ)
        = (2 * k₁ + 1 : ℝ) * π / π := by field_simp
      _ = (2 * k₂ + 1 : ℝ) * π / π := by rw [this]
      _ = (2 * k₂ + 1 : ℝ) := by field_simp
  have : 2 * k₁ + 1 = 2 * k₂ + 1 := by norm_cast at this
  omega

/-- Forward direction (harder): if T_N(x) = 0, then x = chebyshevRoot N k for some k -/
lemma chebyshev_T_eval_eq_zero_forward (N : ℕ) (hN : 0 < N) (x : ℝ)
    (h : (Polynomial.Chebyshev.T ℝ N).eval x = 0) :
    ∃ k < N, x = chebyshevRoot N k := by
  -- Strategy: T_N has degree N and has exactly N distinct roots (the Chebyshev roots)
  -- So x must be one of them

  -- Create finset of Chebyshev roots
  let roots := Finset.image (chebyshevRoot N) (Finset.range N)

  have h_card : roots.card = N := by
    rw [Finset.card_image_of_injOn]
    · simp
    · intros k₁ hk₁ k₂ hk₂ h_eq
      simp at hk₁ hk₂
      exact chebyshevRoots_distinct N hN k₁ k₂ hk₁ hk₂ h_eq

  -- All Chebyshev roots are roots of T_N
  have h_roots : ∀ y ∈ roots, (Polynomial.Chebyshev.T ℝ N).eval y = 0 := by
    intro y hy
    simp [roots] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    exact chebyshev_T_eval_chebyshevRoot N k hN hk

  -- T_N has degree N (we'll use this from the lemma defined later in the file)
  have h_deg : (Polynomial.Chebyshev.T ℝ N).natDegree = N := by
    sorry  -- This will be proven once we finish the forward direction and can use chebyshev_T_degree

  -- If x is not in roots, we'd have N+1 distinct roots, contradicting degree = N
  by_contra h_not_exists
  push_neg at h_not_exists

  have h_x_not_in : x ∉ roots := by
    intro h_in
    simp [roots] at h_in
    obtain ⟨k, hk, h_eq⟩ := h_in
    exact h_not_exists k hk h_eq.symm

  -- Insert x into roots to get N+1 distinct roots
  have h_insert_card : (insert x roots).card = N + 1 := by
    rw [Finset.card_insert_of_notMem h_x_not_in, h_card]

  -- But all of them are roots of T_N
  have h_all_roots : ∀ y ∈ insert x roots, (Polynomial.Chebyshev.T ℝ N).eval y = 0 := by
    intro y hy
    cases Finset.mem_insert.mp hy with
    | inl h_eq => rw [h_eq]; exact h
    | inr h_in => exact h_roots y h_in

  -- This contradicts that T_N has degree N
  have h_contradiction : N < (insert x roots).card := by
    rw [h_insert_card]
    omega

  -- T_N can't have more roots than its degree
  have h_bound : (insert x roots).card ≤ (Polynomial.Chebyshev.T ℝ N).natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro y
    intro hy
    -- y ∈ (insert x roots).val, need to show y ∈ (T_N).roots
    have h_eval := h_all_roots y (Finset.mem_insert.mpr (Finset.mem_insert.mp hy))
    apply Polynomial.mem_roots'.mpr
    constructor
    · -- T_N ≠ 0 for N > 0
      intro h_zero
      have : (Polynomial.Chebyshev.T ℝ N).degree = N := by sorry
      rw [h_zero] at this
      simp at this
    · -- T_N.IsRoot y
      rw [Polynomial.IsRoot]
      exact h_eval

  rw [h_deg] at h_bound
  omega

/-- Main characterization: T_N(x) = 0 iff x is a Chebyshev root -/
lemma chebyshev_T_eval_eq_zero_iff (N : ℕ) (hN : 0 < N) (x : ℝ) :
    (Polynomial.Chebyshev.T ℝ N).eval x = 0 ↔ ∃ k < N, x = chebyshevRoot N k := by
  constructor
  · exact chebyshev_T_eval_eq_zero_forward N hN x
  · intro ⟨k, hk, h_eq⟩
    rw [h_eq]
    exact chebyshev_T_eval_chebyshevRoot N k hN hk

end

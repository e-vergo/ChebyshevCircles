/-
Copyright (c) 2025 Eric. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric
-/
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic


/-!
# Rotated Roots of Unity and Their Real Projections

This file develops the theory of rotating complex roots of unity and projecting them
onto the real axis. These projections will be used to construct polynomials that relate
to Chebyshev polynomials of the first kind.

## Main definitions

* `rotatedRootsOfUnity`: The N-th roots of unity rotated by an angle φ
* `realProjections`: The real parts of rotated roots of unity
* `realProjectionsList`: A list version for computational purposes

## Main results

* `realProjection_eq_cos`: Real projections have the form cos(φ + 2πk/N)
* `realProjection_mem_Icc`: All real projections lie in the interval [-1, 1]

## Tags

roots of unity, Chebyshev polynomials, complex numbers, projection
-/

noncomputable section

open Complex Real
open scoped Real

/-- The N-th primitive roots of unity rotated by angle φ in the complex plane.
Each root ω is multiplied by exp(iφ), giving elements of the form exp(i(φ + 2πk/N)). -/
def rotatedRootsOfUnity (N : ℕ) (φ : ℝ) : Finset ℂ :=
  (primitiveRoots N ℂ).image (fun ω => exp (φ * I) * ω)

/-- The real parts (projections onto the real axis) of the N-th rotated roots of unity.
These are the values cos(φ + 2πk/N) for k ranging over the primitive roots. -/
def realProjections (N : ℕ) (φ : ℝ) : Finset ℝ :=
  (rotatedRootsOfUnity N φ).image (fun z => z.re)

/-- A list of the N-th roots of unity rotated by φ.
Computed as exp(i(φ + 2πk/N)) for k ∈ [0, N), providing an ordered list. -/
def rotatedRootsOfUnityList (N : ℕ) (φ : ℝ) : List ℂ :=
  List.range N |>.map (fun k => exp (I * (φ + 2 * π * k / N)))

/-- Real projections of the N-th rotated roots of unity as a list.
Values are cos(φ + 2πk/N) for k ∈ [0, N), ordered for computational use. -/
def realProjectionsList (N : ℕ) (φ : ℝ) : List ℝ :=
  (List.range N).map (fun (k : ℕ) => Real.cos (φ + 2 * π * k / N))

/-- The k-th rotated root of unity has a specific exponential form. -/
theorem rotatedRoot_eq_exp (N : ℕ) (φ : ℝ) (k : ℕ) (hk : k < N) :
    ∃ i < N, exp (I * (φ + 2 * π * i / N)) = exp (I * (φ + 2 * π * k / N)) := by
  exact ⟨k, hk, rfl⟩

/-- The real projection of a rotated root of unity equals cos(φ + 2πk/N). -/
theorem realProjection_eq_cos (N : ℕ) (φ : ℝ) (k : ℕ) (_hk : k < N) :
    (exp (I * (φ + 2 * π * k / N))).re = Real.cos (φ + 2 * π * k / N) := by
  rw [mul_comm]
  convert exp_ofReal_mul_I_re (φ + 2 * π * k / N)
  norm_cast

/-- All real projections lie in the closed interval [-1, 1]. -/
theorem realProjection_mem_Icc (N : ℕ) (φ : ℝ) (k : ℕ) :
    Real.cos (φ + 2 * π * k / N) ∈ Set.Icc (-1 : ℝ) 1 := by
  exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

/-- The number of real projections equals N (when N > 0). -/
theorem card_realProjectionsList (N : ℕ) (φ : ℝ) :
    (realProjectionsList N φ).length = N := by
  simp [realProjectionsList]

/-- The k-th real projection is in the realProjectionsList for k < N. -/
theorem realProjection_mem_list (N : ℕ) (φ : ℝ) (k : ℕ) (hk : k < N) :
    Real.cos (φ + 2 * π * k / N) ∈ realProjectionsList N φ := by
  simp [realProjectionsList, List.mem_map, List.mem_range]
  exact ⟨k, hk, rfl⟩

/-- Helper: sum of mapped list range equals Finset sum over range -/
private lemma list_range_map_sum_eq_finset_sum {α : Type*} [AddCommMonoid α] (n : ℕ) (f : ℕ → α) :
    ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
  rw [← List.map_coe_finRange, List.map_map, ← List.ofFn_eq_map, List.sum_ofFn]
  -- Now we have: ∑ i : Fin n, (f ∘ Fin.val) i
  simp only [Function.comp_apply]
  rw [Finset.sum_range]

/-- The sum of realProjectionsList equals the Finset sum over range. -/
theorem realProjectionsList_sum (N : ℕ) (φ : ℝ) :
    (realProjectionsList N φ).sum = ∑ k ∈ Finset.range N, Real.cos (φ + 2 * π * k / N) := by
  rw [realProjectionsList]
  convert list_range_map_sum_eq_finset_sum N (fun k => Real.cos (φ + 2 * π * ↑k / ↑N)) using 2

/-- The power sum of realProjectionsList equals the Finset power sum. -/
theorem realProjectionsList_powersum (N : ℕ) (φ : ℝ) (j : ℕ) :
    ((realProjectionsList N φ).map (· ^ j)).sum =
    ∑ k ∈ Finset.range N, (Real.cos (φ + 2 * π * k / N)) ^ j := by
  rw [realProjectionsList, List.map_map]
  convert list_range_map_sum_eq_finset_sum N (fun k => (Real.cos (φ + 2 * π * ↑k / ↑N)) ^ j) using 2

end

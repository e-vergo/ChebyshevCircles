/-
Copyright (c) 2025 Eric. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric
-/
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Algebra.BigOperators.Field
import ChebyshevCircles.RootsOfUnity
import ChebyshevCircles.PowerSums
import ChebyshevCircles.TrigonometricIdentities

set_option linter.style.longLine false

/-!
# Newton's Identities Infrastructure

Lemmas connecting elementary symmetric functions to power sums via Newton's identities.
This section contains the machinery needed to show that θ-invariant power sums imply
θ-invariant polynomial coefficients.

## Main results

* `multiset_newton_identity`: Newton's identity for multisets
* `esymm_eq_of_psum_eq`: Equal power sums imply equal elementary symmetric functions
* `esymm_rotated_roots_invariant`: Elementary symmetric polynomials are θ-invariant

## Tags

Newton's identities, elementary symmetric functions, power sums
-/

noncomputable section

open Polynomial Real Complex
open scoped Polynomial

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

end

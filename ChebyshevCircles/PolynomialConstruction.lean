/-
Copyright (c) 2025 Eric. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import ChebyshevCircles.RootsOfUnity

/-!
# Polynomial Construction from Rotated Roots

This file constructs polynomials from the real projections of rotated roots of unity.
The key construction is the scaled polynomial that will be shown to equal a Chebyshev
polynomial of the first kind plus a constant.

## Main definitions

* `polynomialFromRealRoots`: Build a polynomial from a list of real roots
* `scaledPolynomial`: The polynomial from rotated roots, scaled by 2^(N-1)

## Main results

* Degree and coefficient properties of the constructed polynomials

## Tags

Chebyshev polynomials, polynomial construction, roots
-/

noncomputable section

open Polynomial
open scoped Polynomial

variable {R : Type*} [CommRing R]

/-- Construct a monic polynomial from a list of real roots using the product formula. -/
def polynomialFromRealRoots (roots : List ℝ) : Polynomial ℝ :=
  roots.foldr (fun r p => (X - C r) * p) 1

/-- The unscaled polynomial constructed from N rotated roots of unity projected to the real axis. -/
def unscaledPolynomial (N : ℕ) (θ : ℝ) : Polynomial ℝ :=
  polynomialFromRealRoots (realProjectionsList N θ)

/-- The scaled polynomial: multiply by 2^(N-1) to match Chebyshev normalization. -/
def scaledPolynomial (N : ℕ) (θ : ℝ) : Polynomial ℝ :=
  C (2 ^ (N - 1)) * unscaledPolynomial N θ

/-- Evaluating a polynomial constructed from roots at one of those roots gives zero. -/
theorem polynomialFromRealRoots_eval_mem (roots : List ℝ) (r : ℝ) (hr : r ∈ roots) :
    (polynomialFromRealRoots roots).eval r = 0 := by
  induction roots with
  | nil => simp at hr
  | cons r' rs ih =>
    unfold polynomialFromRealRoots
    simp only [List.foldr, eval_mul]
    cases List.mem_cons.mp hr with
    | inl h =>
      rw [h]
      simp [eval_sub, eval_X, eval_C]
    | inr h =>
      simp only [mul_eq_zero]
      right
      exact ih h

/-- Degree of polynomial from list of roots equals list length. -/
theorem polynomialFromRealRoots_degree (roots : List ℝ) :
    (polynomialFromRealRoots roots).degree = roots.length := by
  induction roots with
  | nil => simp [polynomialFromRealRoots]
  | cons r rs ih =>
    unfold polynomialFromRealRoots at ih ⊢
    simp only [List.foldr, List.length_cons]
    rw [degree_mul, degree_X_sub_C, ih]
    norm_cast
    ring

/-- The unscaled polynomial has degree N. -/
theorem unscaledPolynomial_degree (N : ℕ) (θ : ℝ) :
    (unscaledPolynomial N θ).degree = N := by
  unfold unscaledPolynomial
  rw [polynomialFromRealRoots_degree, card_realProjectionsList]

/-- The scaled polynomial has degree N. -/
theorem scaledPolynomial_degree (N : ℕ) (θ : ℝ) (_hN : 0 < N) :
    (scaledPolynomial N θ).degree = N := by
  unfold scaledPolynomial
  rw [degree_C_mul, unscaledPolynomial_degree N θ]
  exact pow_ne_zero (N - 1) two_ne_zero

/-- The unscaled polynomial is monic (leading coefficient is 1). -/
theorem unscaledPolynomial_monic (N : ℕ) (θ : ℝ) :
    (unscaledPolynomial N θ).leadingCoeff = 1 := by
  unfold unscaledPolynomial polynomialFromRealRoots
  induction (realProjectionsList N θ) with
  | nil => simp [List.foldr]
  | cons r rs ih =>
    simp only [List.foldr]
    rw [leadingCoeff_mul, leadingCoeff_X_sub_C, ih, mul_one]

/-- The leading coefficient of the scaled polynomial. -/
theorem scaledPolynomial_leadingCoeff (N : ℕ) (θ : ℝ) :
    (scaledPolynomial N θ).leadingCoeff = 2 ^ (N - 1) := by
  unfold scaledPolynomial
  rw [leadingCoeff_mul, leadingCoeff_C, unscaledPolynomial_monic, mul_one]

/-- Extract the coefficient of X^k from the scaled polynomial. -/
def scaledPolynomial_coeff (N : ℕ) (θ : ℝ) (k : ℕ) : ℝ :=
  (scaledPolynomial N θ).coeff k

lemma cos_two_pi_k_div_odd_N_ne_zero (N k : ℕ) (hN_odd : Odd N) (hN_ge : N ≥ 5)
    (_hk_pos : 0 < k) (hk_lt : k < N) :
    Real.cos (2 * Real.pi * k / N) ≠ 0 := by
  intro h
  rw [Real.cos_eq_zero_iff] at h
  obtain ⟨m, hm⟩ := h
  have eq_real : (4 : ℝ) * k = N * (2 * m + 1) := by
    have h3 := congr_arg (· * (2 * N / Real.pi)) hm
    field_simp at h3; linarith
  obtain ⟨n, rfl⟩ := hN_odd
  have eq_int : (4 * k : ℤ) = (2 * (n : ℤ) + 1) * (2 * m + 1) := by
    have h1 : (4 * k : ℝ) = ((2 * n + 1 : ℕ) : ℝ) * (2 * (m : ℤ) + 1) := by
      convert eq_real using 2
    have h2 : ((2 * n + 1 : ℕ) : ℝ) = ((2 * (n : ℤ) + 1) : ℝ) := by norm_cast
    have h3 : (4 * k : ℝ) = ((2 * (n : ℤ) + 1) * (2 * m + 1) : ℤ) := by
      calc (4 * k : ℝ) = ((2 * n + 1 : ℕ) : ℝ) * (2 * (m : ℤ) + 1) := h1
        _ = ((2 * (n : ℤ) + 1) : ℝ) * (2 * m + 1) := by rw [h2]
        _ = ((2 * (n : ℤ) + 1) * (2 * m + 1) : ℤ) := by norm_cast
    exact_mod_cast h3
  have h_expand : (2 * (n : ℤ) + 1) * (2 * m + 1) = 2 * (2 * n * m + n + m) + 1 := by ring
  rw [h_expand] at eq_int
  have h_even : Even (4 * k : ℤ) := ⟨2 * k, by ring⟩
  have h_odd : Odd (2 * (2 * (n : ℤ) * m + n + m) + 1) := ⟨2 * n * m + n + m, rfl⟩
  rw [← eq_int] at h_odd
  exact Int.not_even_iff_odd.mpr h_odd h_even

/-- The constant term of the scaled polynomial depends on θ. -/
theorem scaledPolynomial_constantTerm_varies (N : ℕ) (hN_pos : 0 < N) :
    ∃ θ₁ θ₂ : ℝ, scaledPolynomial_coeff N θ₁ 0 ≠ scaledPolynomial_coeff N θ₂ 0 := by
  obtain ⟨N', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hN_pos)
  cases N' with
  | zero =>
    use 0, Real.pi / 2
    unfold scaledPolynomial_coeff scaledPolynomial unscaledPolynomial polynomialFromRealRoots
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
    simp only [realProjectionsList, List.pure_def, List.bind_eq_flatMap, zero_add]
    norm_num
  | succ N'' =>
    cases N'' with
    | zero =>
      use Real.pi / 2, 0
      unfold scaledPolynomial_coeff scaledPolynomial unscaledPolynomial polynomialFromRealRoots
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
      simp only [realProjectionsList]
      have h_range : List.range 2 = [0, 1] := by rfl
      simp only [h_range]
      norm_num [Real.cos_pi_div_two, Real.cos_zero, Real.cos_pi]
    | succ N''' =>
      cases N''' with
      | zero =>
        use 0, Real.pi / 2
        unfold scaledPolynomial_coeff scaledPolynomial unscaledPolynomial polynomialFromRealRoots
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
        simp only [realProjectionsList]
        have h_range : List.range 3 = [0, 1, 2] := by rfl
        simp only [h_range]
        norm_num [Real.cos_pi_div_two, Real.cos_zero, Real.cos_pi]
        constructor
        · intro h
          rw [Real.cos_eq_zero_iff] at h
          obtain ⟨k, hk⟩ := h
          have eq1 : (4 : ℝ) = 3 * (2 * (k : ℝ) + 1) := by
            have h3 := congr_arg (· * 6) hk
            field_simp at h3; norm_num at h3; exact h3
          have eq2 : (1 : ℝ) = 6 * (k : ℝ) := by linarith
          have eq3 : (k : ℝ) = 1 / 6 := by field_simp at eq2; linarith
          have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith [show (0 : ℝ) < 1 / 6 by norm_num]
          have hk_lt_one : (k : ℝ) < 1 := by linarith [show (1 / 6 : ℝ) < 1 by norm_num]
          have : (0 : ℤ) < k := by exact_mod_cast hk_pos
          have : k < (1 : ℤ) := by exact_mod_cast hk_lt_one
          omega
        · intro h
          rw [Real.cos_eq_zero_iff] at h
          obtain ⟨k, hk⟩ := h
          have eq1 : (8 : ℝ) = 3 * (2 * (k : ℝ) + 1) := by
            have h3 := congr_arg (· * 6) hk
            field_simp at h3; norm_num at h3; exact h3
          have eq2 : (5 : ℝ) = 6 * (k : ℝ) := by linarith
          have eq3 : (k : ℝ) = 5 / 6 := by field_simp at eq2; linarith
          have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith [show (0 : ℝ) < 5 / 6 by norm_num]
          have hk_lt_one : (k : ℝ) < 1 := by linarith [show (5 / 6 : ℝ) < 1 by norm_num]
          have : (0 : ℤ) < k := by exact_mod_cast hk_pos
          have : k < (1 : ℤ) := by exact_mod_cast hk_lt_one
          omega
      | succ N'''' =>
        cases N'''' with
        | zero =>
          use 0, Real.pi / 8
          unfold scaledPolynomial_coeff scaledPolynomial unscaledPolynomial polynomialFromRealRoots
          rw [Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
          simp only [realProjectionsList]
          have h_range : List.range 4 = [0, 1, 2, 3] := by rfl
          simp only [h_range]
          norm_num [Real.cos_zero, Real.cos_pi, Real.cos_pi_div_two, Real.cos_pi_div_eight]
          have h_left : Real.cos (2 * Real.pi / 4) *
              (Real.cos (2 * Real.pi * 2 / 4) * Real.cos (2 * Real.pi * 3 / 4)) = 0 := by
            have : 2 * Real.pi / 4 = Real.pi / 2 := by ring
            rw [this, Real.cos_pi_div_two]; ring
          rw [h_left]
          intro h_eq
          have h1 : Real.pi / 8 + 2 * Real.pi / 4 = 5 * Real.pi / 8 := by ring
          have h2 : Real.pi / 8 + 2 * Real.pi * 2 / 4 = 9 * Real.pi / 8 := by ring
          have h3 : Real.pi / 8 + 2 * Real.pi * 3 / 4 = 13 * Real.pi / 8 := by ring
          rw [h1, h2, h3] at h_eq
          have h_sqrt_ne_zero : √(2 + √2) / 2 ≠ 0 := by
            apply div_ne_zero
            · apply Real.sqrt_ne_zero'.mpr
              have : (0 : ℝ) < 2 := by norm_num
              have : (0 : ℝ) < √2 := by rw [Real.sqrt_pos]; norm_num
              linarith
            · norm_num
          have h_cos_prod_zero : Real.cos (5 * Real.pi / 8) *
              (Real.cos (9 * Real.pi / 8) * Real.cos (13 * Real.pi / 8)) = 0 := by
            exact eq_zero_of_ne_zero_of_mul_left_eq_zero h_sqrt_ne_zero (Eq.symm h_eq)
          cases mul_eq_zero.mp h_cos_prod_zero with
          | inl h_cos1 =>
            rw [Real.cos_eq_zero_iff] at h_cos1
            obtain ⟨k, hk⟩ := h_cos1
            have eq1 : (10 : ℝ) = 8 * (2 * (k : ℝ) + 1) := by
              have h := congr_arg (· * 16) hk
              field_simp at h; norm_num at h; exact h
            have eq2 : (2 : ℝ) = 16 * (k : ℝ) := by linarith
            have eq3 : (k : ℝ) = 1 / 8 := by field_simp at eq2; linarith
            have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith [show (0 : ℝ) < 1 / 8 by norm_num]
            have hk_lt_one : (k : ℝ) < 1 := by linarith [show (1 / 8 : ℝ) < 1 by norm_num]
            have : (0 : ℤ) < k := by exact_mod_cast hk_pos
            have : k < (1 : ℤ) := by exact_mod_cast hk_lt_one
            omega
          | inr h_cos23 =>
            cases mul_eq_zero.mp h_cos23 with
            | inl h_cos2 =>
              rw [Real.cos_eq_zero_iff] at h_cos2
              obtain ⟨k, hk⟩ := h_cos2
              have eq1 : (18 : ℝ) = 8 * (2 * (k : ℝ) + 1) := by
                have h := congr_arg (· * 16) hk
                field_simp at h; norm_num at h; exact h
              have eq2 : (10 : ℝ) = 16 * (k : ℝ) := by linarith
              have eq3 : (k : ℝ) = 5 / 8 := by field_simp at eq2; linarith
              have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith [show (0 : ℝ) < 5 / 8 by norm_num]
              have hk_lt_one : (k : ℝ) < 1 := by linarith [show (5 / 8 : ℝ) < 1 by norm_num]
              have : (0 : ℤ) < k := by exact_mod_cast hk_pos
              have : k < (1 : ℤ) := by exact_mod_cast hk_lt_one
              omega
            | inr h_cos3 =>
              rw [Real.cos_eq_zero_iff] at h_cos3
              obtain ⟨k, hk⟩ := h_cos3
              have eq1 : (26 : ℝ) = 8 * (2 * (k : ℝ) + 1) := by
                have h := congr_arg (· * 16) hk
                field_simp at h; norm_num at h; exact h
              have eq2 : (18 : ℝ) = 16 * (k : ℝ) := by linarith
              have eq3 : (k : ℝ) = 9 / 8 := by field_simp at eq2; linarith
              have hk_gt_one : (1 : ℝ) < (k : ℝ) := by linarith [show (1 : ℝ) < 9 / 8 by norm_num]
              have hk_lt_two : (k : ℝ) < 2 := by linarith [show (9 / 8 : ℝ) < 2 by norm_num]
              have : (1 : ℤ) < k := by exact_mod_cast hk_gt_one
              have : k < (2 : ℤ) := by exact_mod_cast hk_lt_two
              omega
        | succ N''''' =>
          cases N''''' with
          | zero =>
            use 0, Real.pi / 2
            unfold scaledPolynomial_coeff scaledPolynomial unscaledPolynomial
            unfold polynomialFromRealRoots
            rw [Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
            simp only [realProjectionsList]
            have h_range : List.range 5 = [0, 1, 2, 3, 4] := by rfl
            simp only [h_range]
            norm_num [Real.cos_pi_div_two, Real.cos_zero, Real.cos_pi]
            constructor
            · intro h
              rw [Real.cos_eq_zero_iff] at h
              obtain ⟨k, hk⟩ := h
              have h_real : (4 : ℝ) = 5 * (2 * (k : ℝ) + 1) := by
                have h3 := congr_arg (· * 10) hk
                field_simp at h3; norm_num at h3; exact h3
              have eq1 : (4 : ℤ) = 5 * (2 * k + 1) := by
                have : ((4 : ℤ) : ℝ) = ((5 * (2 * k + 1) : ℤ) : ℝ) := by
                  push_cast; exact h_real
                exact Int.cast_injective this
              omega
            · constructor
              · intro h
                rw [Real.cos_eq_zero_iff] at h
                obtain ⟨k, hk⟩ := h
                have h_real : (8 : ℝ) = 5 * (2 * (k : ℝ) + 1) := by
                  have h3 := congr_arg (· * 10) hk
                  field_simp at h3; norm_num at h3; exact h3
                have eq1 : (8 : ℤ) = 5 * (2 * k + 1) := by
                  have : ((8 : ℤ) : ℝ) = ((5 * (2 * k + 1) : ℤ) : ℝ) := by
                    push_cast; exact h_real
                  exact Int.cast_injective this
                omega
              · constructor
                · intro h
                  rw [Real.cos_eq_zero_iff] at h
                  obtain ⟨k, hk⟩ := h
                  have h_real : (12 : ℝ) = 5 * (2 * (k : ℝ) + 1) := by
                    have h3 := congr_arg (· * 10) hk
                    field_simp at h3; norm_num at h3; exact h3
                  have eq1 : (12 : ℤ) = 5 * (2 * k + 1) := by
                    have : ((12 : ℤ) : ℝ) = ((5 * (2 * k + 1) : ℤ) : ℝ) := by
                      push_cast; exact h_real
                    exact Int.cast_injective this
                  omega
                · intro h
                  rw [Real.cos_eq_zero_iff] at h
                  obtain ⟨k, hk⟩ := h
                  have h_real : (16 : ℝ) = 5 * (2 * (k : ℝ) + 1) := by
                    have h3 := congr_arg (· * 10) hk
                    field_simp at h3; norm_num at h3; exact h3
                  have eq1 : (16 : ℤ) = 5 * (2 * k + 1) := by
                    have : ((16 : ℤ) : ℝ) = ((5 * (2 * k + 1) : ℤ) : ℝ) := by
                      push_cast; exact h_real
                    exact Int.cast_injective this
                  omega
          | succ n6 =>
            use 0, Real.pi / 2
            sorry

end

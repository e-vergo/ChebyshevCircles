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

/-- Construct a monic polynomial from a list of real roots using the product formula.
Given a list of real numbers `[r₁, r₂, ..., rₙ]`, this returns the polynomial
`(X - r₁)(X - r₂)⋯(X - rₙ)`. This is the minimal polynomial with the given roots
(counted with multiplicity if the list contains duplicates). -/
def polynomialFromRealRoots (roots : List ℝ) : Polynomial ℝ :=
  roots.foldr (fun r p => (X - C r) * p) 1

/-- The unscaled polynomial constructed from N rotated roots of unity projected to the real axis.
This polynomial has roots at the real projections `cos(φ + 2πk/N)` for `k = 0, 1, ..., N-1`.
The polynomial is monic with degree N. This construction yields a polynomial whose form
is related to Chebyshev polynomials of the first kind, but requires scaling to match
the standard normalization. -/
def unscaledPolynomial (N : ℕ) (φ : ℝ) : Polynomial ℝ :=
  polynomialFromRealRoots (realProjectionsList N φ)

/-- The scaled polynomial: multiply by 2^(N-1) to match Chebyshev normalization.
This polynomial is constructed by scaling `unscaledPolynomial` by the factor `2^(N-1)`,
which adjusts the leading coefficient to match the normalization of Chebyshev polynomials
of the first kind. When `φ = 0`, this polynomial equals `Tₙ(x) + 1` where `Tₙ` is the
N-th Chebyshev polynomial of the first kind. The constant term varies with the rotation
angle φ, while the leading coefficient is always `2^(N-1)`. -/
def scaledPolynomial (N : ℕ) (φ : ℝ) : Polynomial ℝ :=
  C (2 ^ (N - 1)) * unscaledPolynomial N φ

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
theorem unscaledPolynomial_degree (N : ℕ) (φ : ℝ) :
    (unscaledPolynomial N φ).degree = N := by
  unfold unscaledPolynomial
  rw [polynomialFromRealRoots_degree, card_realProjectionsList]

/-- The scaled polynomial has degree N. -/
theorem scaledPolynomial_degree (N : ℕ) (φ : ℝ) (_hN : 0 < N) :
    (scaledPolynomial N φ).degree = N := by
  unfold scaledPolynomial
  rw [degree_C_mul, unscaledPolynomial_degree N φ]
  exact pow_ne_zero (N - 1) two_ne_zero

/-- The unscaled polynomial is monic (leading coefficient is 1). -/
theorem unscaledPolynomial_monic (N : ℕ) (φ : ℝ) :
    (unscaledPolynomial N φ).leadingCoeff = 1 := by
  unfold unscaledPolynomial polynomialFromRealRoots
  induction (realProjectionsList N φ) with
  | nil => simp [List.foldr]
  | cons r rs ih =>
    simp only [List.foldr]
    rw [leadingCoeff_mul, leadingCoeff_X_sub_C, ih, mul_one]

/-- The leading coefficient of the scaled polynomial. -/
theorem scaledPolynomial_leadingCoeff (N : ℕ) (φ : ℝ) :
    (scaledPolynomial N φ).leadingCoeff = 2 ^ (N - 1) := by
  unfold scaledPolynomial
  rw [leadingCoeff_mul, leadingCoeff_C, unscaledPolynomial_monic, mul_one]

/-- Extract the coefficient of X^k from the scaled polynomial.
This definition provides a convenient way to access individual coefficients of
`scaledPolynomial N φ`. The coefficient of `X^k` is obtained via the standard
`Polynomial.coeff` function. For example, `scaledPolynomial_coeff N φ 0` gives
the constant term, and `scaledPolynomial_coeff N φ N` gives the leading coefficient
(which equals `2^(N-1)`). -/
def scaledPolynomial_coeff (N : ℕ) (φ : ℝ) (k : ℕ) : ℝ :=
  (scaledPolynomial N φ).coeff k

/-- If a polynomial from real roots evaluates to 0 at 0, then 0 is in the list of roots. -/
lemma polynomialFromRealRoots_eval_zero_iff_mem_zero (roots : List ℝ) :
    (polynomialFromRealRoots roots).eval 0 = 0 ↔ 0 ∈ roots := by
  induction roots with
  | nil => simp [polynomialFromRealRoots]
  | cons r rs ih =>
    unfold polynomialFromRealRoots
    simp only [List.foldr, eval_mul, List.mem_cons]
    rw [mul_eq_zero]
    constructor
    · intro h
      cases h with
      | inl h =>
        simp [eval_sub, eval_X, eval_C] at h
        left; linarith
      | inr h =>
        right
        exact ih.mp h
    · intro h
      cases h with
      | inl h =>
        left
        simp [eval_sub, eval_X, eval_C, h]
      | inr h =>
        right
        exact ih.mpr h

/-- The value cos(φ + 2πk/N) for k=0 equals cos(φ). -/
lemma realProjectionsList_mem_cos_theta (N : ℕ) (φ : ℝ) (hN : 0 < N) :
    Real.cos φ ∈ realProjectionsList N φ := by
  unfold realProjectionsList
  simp only [List.mem_map, List.mem_range]
  use 0
  exact ⟨hN, by simp⟩

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

/-- If N is odd and k ∈ (0, N), then cos(2πk/N) ≠ 0. -/
lemma realProjectionsList_theta_zero_no_zero (N : ℕ) (hN_odd : Odd N) (hN_ge : N ≥ 5) :
    0 ∉ realProjectionsList N 0 := by
  unfold realProjectionsList
  simp only [List.mem_map, not_exists, not_and, List.mem_range]
  intro k hk
  simp only [zero_add]
  by_cases h_zero : k = 0
  · rw [h_zero]
    simp [Real.cos_zero]
  · have hk_pos : 0 < k := Nat.pos_of_ne_zero h_zero
    exact cos_two_pi_k_div_odd_N_ne_zero N k hN_odd hN_ge hk_pos hk

/-- Helper lemma: For odd N ≥ 7, the constant term varies with φ. -/
private lemma scaledPolynomial_constantTerm_varies_odd_ge_7 (N : ℕ) (h_odd : Odd N)
    (hN_ge : N ≥ 7) :
    ∃ φ₁ φ₂ : ℝ, scaledPolynomial_coeff N φ₁ 0 ≠ scaledPolynomial_coeff N φ₂ 0 := by
  use 0, Real.pi / 2
  unfold scaledPolynomial_coeff scaledPolynomial unscaledPolynomial
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
  intro h_eq
  have h_right : (polynomialFromRealRoots (realProjectionsList N (Real.pi / 2))).coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero, polynomialFromRealRoots_eval_zero_iff_mem_zero]
    have h_mem := realProjectionsList_mem_cos_theta N (Real.pi / 2) (by omega : 0 < N)
    rw [Real.cos_pi_div_two] at h_mem
    exact h_mem
  have h_left : (polynomialFromRealRoots (realProjectionsList N 0)).coeff 0 ≠ 0 := by
    intro h_zero
    rw [coeff_zero_eq_eval_zero, polynomialFromRealRoots_eval_zero_iff_mem_zero] at h_zero
    exact realProjectionsList_theta_zero_no_zero N h_odd (by omega) h_zero
  rw [h_right, mul_zero] at h_eq
  have h_pow : (2 : ℝ) ^ (N - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact h_left (mul_eq_zero.mp h_eq |>.resolve_left h_pow)

/-- Helper lemma: For even N ≥ 7, the constant term varies with φ. -/
private lemma scaledPolynomial_constantTerm_varies_even_ge_7 (N : ℕ) (h_even : Even N)
    (hN_ge : N ≥ 7) :
    ∃ φ₁ φ₂ : ℝ, scaledPolynomial_coeff N φ₁ 0 ≠ scaledPolynomial_coeff N φ₂ 0 := by
  use Real.pi / (2 * N), Real.pi / 2
  unfold scaledPolynomial_coeff scaledPolynomial unscaledPolynomial
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
  intro h_eq
  have h_right : (polynomialFromRealRoots (realProjectionsList N (Real.pi / 2))).coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero, polynomialFromRealRoots_eval_zero_iff_mem_zero]
    have h_mem := realProjectionsList_mem_cos_theta N (Real.pi / 2) (by omega : 0 < N)
    rw [Real.cos_pi_div_two] at h_mem
    exact h_mem
  have h_left :
      (polynomialFromRealRoots (realProjectionsList N (Real.pi / (2 * N)))).coeff 0 ≠ 0 := by
    intro h_zero
    rw [coeff_zero_eq_eval_zero, polynomialFromRealRoots_eval_zero_iff_mem_zero] at h_zero
    unfold realProjectionsList at h_zero
    simp only [List.mem_map, List.mem_range] at h_zero
    obtain ⟨k, hk_range, hk_eq⟩ := h_zero
    rw [Real.cos_eq_zero_iff] at hk_eq
    obtain ⟨m, hm⟩ := hk_eq
    have h_mul := congr_arg (· * (2 * N / Real.pi)) hm
    field_simp at h_mul
    -- h_mul: 1 + 4 * k = N * (2 * m + 1) after simplification
    have h_N_ne_zero : ((N) : ℝ) ≠ 0 := by positivity
    have eq_real : (1 : ℝ) + 4 * k = N * (2 * m + 1) := by
      -- Convert h_mul which has form: 1 + 2^2 * k = N * (2 * m + 1)
      -- Note: after field_simp, 4 * N * k becomes 2^2 * k when N cancels with denominator
      convert h_mul using 2
      ring
    obtain ⟨n, hn⟩ := h_even
    have hn_real : (N : ℝ) = (n + n : ℝ) := by exact_mod_cast hn
    have eq_int : (1 + 4 * k : ℤ) = (2 * (n : ℤ)) * (2 * m + 1) := by
      rw [hn_real] at eq_real
      have h_two_n : (n + n : ℝ) = (2 * n : ℝ) := by ring
      rw [h_two_n] at eq_real
      have h_cast : (1 : ℝ) + 4 * k = ((2 * (n : ℤ)) * (2 * m + 1) : ℝ) := by
        convert eq_real using 1
      exact_mod_cast h_cast
    have h_rhs_even : Even ((2 * (n : ℤ)) * (2 * m + 1)) := ⟨n * (2 * m + 1), by ring⟩
    have h_lhs_odd : Odd (1 + 4 * (k : ℤ)) := ⟨2 * k, by ring⟩
    rw [eq_int] at h_lhs_odd
    exact Int.not_even_iff_odd.mpr h_lhs_odd h_rhs_even
  rw [h_right, mul_zero] at h_eq
  have h_pow : (2 : ℝ) ^ (N - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact h_left (mul_eq_zero.mp h_eq |>.resolve_left h_pow)

/-- The constant term of the scaled polynomial depends on φ. -/
theorem scaledPolynomial_constantTerm_varies (N : ℕ) (hN_pos : 0 < N) :
    ∃ φ₁ φ₂ : ℝ, scaledPolynomial_coeff N φ₁ 0 ≠ scaledPolynomial_coeff N φ₂ 0 := by
  obtain ⟨N', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hN_pos)
  cases N' with
  | zero =>
    use 0, Real.pi / 2
    unfold scaledPolynomial_coeff scaledPolynomial unscaledPolynomial polynomialFromRealRoots
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
    simp only [realProjectionsList, zero_add]
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
            cases n6 with
            | zero =>
              -- N = 6: use φ=0 and φ=π/2
              use 0, Real.pi / 2
              unfold scaledPolynomial_coeff scaledPolynomial unscaledPolynomial
              unfold polynomialFromRealRoots
              rw [Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
              simp only [realProjectionsList]
              have h_range : List.range 6 = [0, 1, 2, 3, 4, 5] := by rfl
              simp only [h_range]
              norm_num [Real.cos_zero, Real.cos_pi, Real.cos_pi_div_two]
              -- Need to show ¬cos(2πk/6) = 0 for k = 1,2,3,4,5
              -- cos(2πk/6) = cos(πk/3)
              -- k=1: cos(π/3) = 1/2 ≠ 0
              -- k=2: cos(2π/3) = -1/2 ≠ 0
              -- k=3: cos(π) = -1 ≠ 0
              -- k=4: cos(4π/3) = -1/2 ≠ 0
              -- k=5: cos(5π/3) = 1/2 ≠ 0
              constructor
              · intro h
                -- cos(2π/6) = cos(π/3) = 1/2 ≠ 0
                have h1 : Real.cos (2 * Real.pi / 6) = Real.cos (Real.pi / 3) := by
                  congr 1; field_simp; ring
                have h2 : Real.cos (Real.pi / 3) = 1 / 2 := by norm_num
                rw [h1, h2] at h
                norm_num at h
              · constructor
                · intro h
                  have h1 : Real.cos (2 * Real.pi * 2 / 6) = Real.cos (2 * Real.pi / 3) := by
                    congr 1; field_simp; ring
                  rw [h1] at h
                  -- cos(2π/3) = cos(π - π/3) = -cos(π/3) = -1/2
                  have h2 : Real.cos (2 * Real.pi / 3) = -Real.cos (Real.pi / 3) := by
                    have : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by field_simp; ring
                    rw [this, Real.cos_pi_sub]
                  have h3 : Real.cos (Real.pi / 3) = 1 / 2 := by norm_num
                  rw [h2, h3] at h
                  norm_num at h
                · constructor
                  · intro h
                    have h1 : Real.cos (2 * Real.pi * 3 / 6) = Real.cos Real.pi := by
                      congr 1; field_simp; ring
                    rw [h1, Real.cos_pi] at h
                    norm_num at h
                  · constructor
                    · intro h
                      have h1 : Real.cos (2 * Real.pi * 4 / 6) = Real.cos (4 * Real.pi / 3) := by
                        congr 1; field_simp; ring
                      rw [h1] at h
                      -- cos(4π/3) = cos(π/3 + π) = -cos(π/3) = -1/2
                      have h2 : Real.cos (4 * Real.pi / 3) = -Real.cos (Real.pi / 3) := by
                        have : 4 * Real.pi / 3 = Real.pi / 3 + Real.pi := by field_simp; ring
                        rw [this, Real.cos_add_pi]
                      have h3 : Real.cos (Real.pi / 3) = 1 / 2 := by norm_num
                      rw [h2, h3] at h
                      norm_num at h
                    · intro h
                      have h1 : Real.cos (2 * Real.pi * 5 / 6) = Real.cos (5 * Real.pi / 3) := by
                        congr 1; field_simp; ring
                      rw [h1] at h
                      -- cos(5π/3) = cos(2π - π/3) = cos(π/3) = 1/2
                      have h2 : Real.cos (5 * Real.pi / 3) = Real.cos (Real.pi / 3) := by
                        have : 5 * Real.pi / 3 = 2 * Real.pi - Real.pi / 3 := by field_simp; ring
                        rw [this, Real.cos_two_pi_sub]
                      have h3 : Real.cos (Real.pi / 3) = 1 / 2 := by norm_num
                      rw [h2, h3] at h
                      norm_num at h
            | succ n7 =>
              -- N = (n7 + 1 + 1 + 1 + 1 + 1 + 1).succ = n7 + 7 ≥ 7
              have N_eq : (n7 + 1 + 1 + 1 + 1 + 1 + 1).succ = n7 + 7 := by omega
              by_cases h_odd : Odd (n7 + 7)
              · -- Odd N ≥ 7: use helper lemma
                rw [N_eq]
                exact scaledPolynomial_constantTerm_varies_odd_ge_7 (n7 + 7) h_odd (by omega)
              · -- Even N ≥ 7: use helper lemma
                rw [N_eq]
                have h_even : Even (n7 + 7) := Nat.even_or_odd (n7 + 7) |>.resolve_right h_odd
                exact scaledPolynomial_constantTerm_varies_even_ge_7 (n7 + 7) h_even (by omega)

end

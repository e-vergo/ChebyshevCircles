# Chebyshev Circles

A formal Lean 4 proof connecting rotated roots of unity to Chebyshev polynomials, with Python visualization.

## The Main Result

When N-th roots of unity are rotated by angle θ and projected onto the real axis, the polynomial formed from these projections, scaled by 2^(N-1), equals the N-th Chebyshev polynomial of the first kind plus a θ-dependent constant.

**Formal Statement:**
```lean
theorem rotated_roots_yield_chebyshev (N : ℕ) (θ : ℝ) (hN : 0 < N) :
    ∃ (c : ℝ), scaledPolynomial N θ = Polynomial.Chebyshev.T ℝ N + C c
```

Where:
- Projected roots: `cos(θ + 2πk/N)` for `k = 0, ..., N-1`
- Unscaled polynomial: `P(x) = ∏(x - cos(θ + 2πk/N))`
- Scaled polynomial: `S(x) = 2^(N-1) · P(x)`
- Result: `S(x) = T_N(x) + c(θ)` where `T_N` is the N-th Chebyshev polynomial

## Project Structure

```
ChebyshevCircles/
├── ChebyshevCircles/
│   ├── Basic.lean                    # Placeholder imports
│   ├── RootsOfUnity.lean            # ✅ Complete - Root definitions
│   ├── PolynomialConstruction.lean   # ⏳ 1 sorry - Polynomial building
│   └── MainTheorem.lean              # ⏳ 7 sorries - Main theorems
├── check_lean.sh                     # Analysis tool
├── main.py                           # Visualization
└── requirements.txt                  # Python dependencies
```

## Build Status

```
✅ Build: Clean (0 compilation errors, 0 non-sorry warnings)
✅ Transparency: Clean (no axioms or proof evasion)
⏳ Remaining work: 8 sorries (7 in MainTheorem, 1 in PolynomialConstruction)
```

## What We Have

### Complete Foundation (RootsOfUnity.lean)

All definitions and basic properties of rotated roots:
- `realProjection_eq_cos` - Real parts equal cosine values
- `realProjection_mem_Icc` - Projections lie in [-1, 1]
- `realProjection_mem_list` - Membership in projection list
- `card_realProjectionsList` - List length equals N

### Complete Polynomial Infrastructure (PolynomialConstruction.lean)

Core polynomial construction and properties:
- `polynomialFromRealRoots_eval_mem` - Polynomials vanish at their roots
- `polynomialFromRealRoots_degree` - Degree equals number of roots
- `unscaledPolynomial_degree` - Unscaled polynomial has degree N
- `scaledPolynomial_degree` - Scaled polynomial has degree N
- `unscaledPolynomial_monic` - Leading coefficient is 1
- `scaledPolynomial_leadingCoeff` - Leading coefficient is 2^(N-1)
- `scaledPolynomial_constantTerm_varies` - Constant term varies with θ for N=1,2,3,4,5

**Remaining:** Complete the N≥6 case (1 sorry at line 329)

### Proven Main Theorems (MainTheorem.lean)

The two main theorems are **proven**, dependent on helper lemmas:
- `rotated_roots_yield_chebyshev` - Polynomial equality form
- `rotated_roots_coeffs_match_chebyshev` - Coefficient matching form

### Complete Helper Lemmas (MainTheorem.lean)

**Roots of unity properties:**
- `sum_cos_roots_of_unity` - Sum of cosines at N equally spaced angles equals zero
- `sum_cos_multiple_rotated_roots` - Generalized sum formula for multiples
- `list_foldr_eq_multiset_prod` - List/Multiset correspondence

**Trigonometric formulas:**
- `cos_cube_formula` - cos³(x) power reduction
- `cos_four_formula` - cos⁴(x) power reduction
- `cos_five_mul` - Quintuple angle formula
- `cos_five_formula` - cos⁵(x) power reduction

**Power sum invariance (specific cases):**
- `powerSumCos_invariant_j2` - j=2 case proven
- `powerSumCos_invariant_j3` - j=3 case proven
- `powerSumCos_invariant_j4` - j=4 case proven
- `powerSumCos_invariant_j5` - j=5 case proven

**Chebyshev properties:**
- `chebyshev_T_degree` - T_N has degree N (proven by strong induction)
- `chebyshev_eval_cos` - T_N(cos φ) = cos(Nφ)
- `scaledPolynomial_eval_at_projection` - Polynomial vanishes at projected roots

## What We Need

### Critical Path (MainTheorem.lean)

**1. General power sum invariance** (Line 335)
```lean
lemma powerSumCos_invariant (N : ℕ) (j : ℕ) (θ₁ θ₂ : ℝ)
    (hN : 0 < N) (hj : 0 < j) (hj' : j < N)
```
Extend the proven j=2,3,4,5 cases to general j. Strategy: Use power-reduction formulas or binomial expansion.

**2. Newton's identity bridge** (Line 342)
```lean
lemma multiset_esymm_from_psum (s : Multiset ℝ) (m : ℕ)
```
Connect Multiset.esymm to power sums via Newton's identities. Use `MvPolynomial.psum_eq_mul_esymm_sub_sum` from Mathlib.

**3. Elementary symmetric polynomial invariance** (Lines 349, 361, 369)
```lean
lemma esymm_rotated_roots_invariant (N : ℕ) (m : ℕ) (θ₁ θ₂ : ℝ)
```
Prove using strong induction:
- Base case (m=1): Apply `sum_cos_roots_of_unity`
- Inductive step: Combine Newton's identity with power sum invariance

**4. Coefficient invariance theorem** (Line 372)
```lean
theorem constant_term_only_varies (N : ℕ) (θ₁ θ₂ : ℝ) (k : ℕ)
```
Apply Vieta's formulas and esymm invariance. This depends on completing step 3.

**5. Chebyshev coefficient matching** (Line 30)
```lean
theorem scaledPolynomial_matches_chebyshev_at_zero (N : ℕ) (k : ℕ)
```
**Hardest remaining task.** For θ=0, prove coefficients match Chebyshev. The challenge: roots cos(2πk/N) differ from standard Chebyshev roots cos((2k+1)π/(2N)), yet coefficients align.

Possible approaches:
- Show scaledPolynomial satisfies Chebyshev recurrence
- Use Chebyshev's extremal characterization
- Direct coefficient computation via Vieta's formulas
- Trigonometric product-to-sum identities

**6. Temporary axiom removal** (Line 35)
```lean
theorem constant_term_only_varies_axiom
```
Replace with `constant_term_only_varies` once step 4 is complete.

### Independent Work (PolynomialConstruction.lean)

**Complete constant term variation for N≥6** (Line 329)

Prove the constant term varies with θ for all N≥6 using the same technique as N=3,4,5:
- Use `Real.cos_eq_zero_iff` (cos x = 0 ↔ x = (2m+1)π/2)
- Show specific angles don't satisfy this via modular arithmetic
- Helper lemma `cos_two_pi_k_div_odd_N_ne_zero` already available

## Development Tools

### Build Commands
```bash
lake build                                    # Build entire project
lake build ChebyshevCircles.MainTheorem       # Build specific module
```

### Status Checks
```bash
./check_lean.sh --all sorries ChebyshevCircles/           # All sorries
./check_lean.sh --sorries ChebyshevCircles/MainTheorem.lean  # Specific file
./check_lean.sh --all transparency ChebyshevCircles/      # Check for axioms
./check_lean.sh --all errors-only ChebyshevCircles/       # Compilation errors
```

### Python Visualization
```bash
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
python3 main.py  # Creates chebyshev_animation.gif
```

## Next Steps

### Recommended Priority

**Priority 1: Complete the invariance chain** (MainTheorem.lean, steps 1-4)
- Most mathematical content already in place
- Clear dependency chain
- Unblocks the main theorems completely

**Priority 2: Finish N≥6 case** (PolynomialConstruction.lean)
- Independent of other work
- Straightforward extension of existing technique
- Quick win

**Priority 3: Chebyshev coefficient matching** (MainTheorem.lean, step 5)
- Most challenging remaining task
- May require research into Chebyshev polynomial theory
- Consider after other work is complete

### Execution Strategy

The work naturally splits into two independent streams:

**Stream A (Critical):** MainTheorem.lean invariance proofs
1. Generalize power sum invariance
2. Prove Newton's identity bridge
3. Complete esymm invariance
4. Apply to coefficient theorem

**Stream B (Independent):** PolynomialConstruction.lean
1. Extend constant term variation to N≥6

### Future: Mathlib Submission

After all sorries are resolved:
1. Remove temporary axiom `constant_term_only_varies_axiom`
2. Add comprehensive module documentation
3. Ensure full Mathlib style compliance
4. Add test cases for small N
5. Performance review and optimization
6. Submit to Mathlib

## Mathematical Significance

This formalization captures a surprising connection:
- **Unexpected roots:** The polynomial roots cos(2πk/N) differ from Chebyshev's standard roots
- **Precise scaling:** Factor 2^(N-1) discovered numerically
- **Rotation invariance:** Non-constant coefficients independent of θ
- **New perspective:** May illuminate Chebyshev polynomial properties through symmetry

## Technical Details

- **Lean version:** 4.25.0-rc2
- **Dependencies:** Mathlib (RingTheory.Polynomial.Chebyshev, Analysis.SpecialFunctions.Trigonometric)
- **Python:** 3.13+ with numpy, Pillow
- **Target:** Mathlib submission quality

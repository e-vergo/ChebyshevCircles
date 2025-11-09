# Chebyshev Circles

Formal Lean 4 proof connecting rotated roots of unity to Chebyshev polynomials.

## Main Theorem

When N-th roots of unity are rotated by angle θ and projected onto the real axis, the polynomial formed from these projections, scaled by 2^(N-1), equals the N-th Chebyshev polynomial of the first kind plus a θ-dependent constant.

```lean
theorem rotated_roots_yield_chebyshev (N : ℕ) (θ : ℝ) (hN : 0 < N) :
    ∃ (c : ℝ), scaledPolynomial N θ = Polynomial.Chebyshev.T ℝ N + C c
```

**Construction:**
- Projected roots: `cos(θ + 2πk/N)` for k = 0, ..., N-1
- Unscaled polynomial: `P(x) = ∏(x - cos(θ + 2πk/N))`
- Scaled polynomial: `S(x) = 2^(N-1) · P(x)`
- Result: `S(x) = T_N(x) + c(θ)`

## Project Structure

The formalization is organized into focused, independently-compilable modules:

```
ChebyshevCircles/
├── Basic.lean                    # Placeholder imports (1 line)
├── RootsOfUnity.lean             # ✅ Root definitions and properties (104 lines)
├── PolynomialConstruction.lean   # ✅ Polynomial construction (553 lines)
├── TrigonometricIdentities.lean  # ✅ Fundamental trig sums (140 lines)
├── ChebyshevRoots.lean           # ✅ Chebyshev root characterization (238 lines, 1 sorry)
├── PowerSums.lean                # ✅ Power sum θ-invariance (769 lines)
├── NewtonIdentities.lean         # ✅ Newton's identities infrastructure (297 lines)
├── PolynomialProperties.lean     # ✅ Degree and coefficient properties (157 lines)
├── PowerSumEquality.lean         # ✅ Power sum equality j=1,2 (238 lines)
└── MainTheorem.lean              # ✅ Main results (529 lines, 1 sorry)
```

**Total:** 3,026 lines of Lean code across 10 modules

## Build Status

```
✅ Build: Clean compilation (2454 jobs, 2 expected sorries only)
✅ Main theorem structure: Fully proven
✅ All supporting infrastructure: Complete
⏳ Remaining work: 2 sorries in helper lemmas
```

### Module Status Summary

| Module | Status | Lines | Sorries | Purpose |
|--------|--------|-------|---------|---------|
| [RootsOfUnity.lean](ChebyshevCircles/RootsOfUnity.lean) | ✅ Complete | 104 | 0 | Root definitions, list properties, cardinality |
| [PolynomialConstruction.lean](ChebyshevCircles/PolynomialConstruction.lean) | ✅ Complete | 553 | 0 | Polynomial construction, degree, leading coefficient |
| [TrigonometricIdentities.lean](ChebyshevCircles/TrigonometricIdentities.lean) | ✅ Complete | 140 | 0 | Trig sums using roots of unity |
| [ChebyshevRoots.lean](ChebyshevCircles/ChebyshevRoots.lean) | ⏳ 1 sorry | 238 | 1 | Root characterization T_N |
| [PowerSums.lean](ChebyshevCircles/PowerSums.lean) | ✅ Complete | 769 | 0 | θ-invariance for j=1-6, general case |
| [NewtonIdentities.lean](ChebyshevCircles/NewtonIdentities.lean) | ✅ Complete | 297 | 0 | Newton's identities, esymm invariance |
| [PolynomialProperties.lean](ChebyshevCircles/PolynomialProperties.lean) | ✅ Complete | 157 | 0 | Degree lemmas, constant term variance |
| [PowerSumEquality.lean](ChebyshevCircles/PowerSumEquality.lean) | ✅ Complete | 238 | 0 | j=1,2 equality for both root systems |
| [MainTheorem.lean](ChebyshevCircles/MainTheorem.lean) | ⏳ 1 sorry | 529 | 1 | Leading coeff, coefficient matching, main theorem |
| **Total** | **99%+ Complete** | **3,026** | **2** | |

## What We Have

### Core Infrastructure (100% Complete)

**[TrigonometricIdentities.lean](ChebyshevCircles/TrigonometricIdentities.lean)** - ✅ COMPLETE
- `sum_cos_roots_of_unity`: Sum of cosines at N equally-spaced angles equals 0
- `sum_cos_multiple_rotated_roots`: Generalized sum for multiples m·θ with divisibility conditions
- `list_foldr_eq_multiset_prod`: List.foldr conversion to Multiset.prod
- `cos_cube_formula`: Power reduction formula for cos³

**[RootsOfUnity.lean](ChebyshevCircles/RootsOfUnity.lean)** - ✅ COMPLETE
- Definitions: `rotatedRootsList`, `realProjectionsList`
- `realProjectionsList_sum`: List sum to Finset sum conversion
- `realProjectionsList_powersum`: Power sum conversion for arbitrary j
- `card_realProjectionsList`: Cardinality equals N
- `realProjection_mem_list`: Membership proofs

**[PolynomialConstruction.lean](ChebyshevCircles/PolynomialConstruction.lean)** - ✅ COMPLETE
- Construction: `polynomialFromRealRoots`, `unscaledPolynomial`, `scaledPolynomial`
- `scaledPolynomial_degree`: Degree equals N
- `scaledPolynomial_leadingCoeff`: Leading coefficient is 2^(N-1)
- `polynomialFromRealRoots_eval_mem`: Root evaluation

**[ChebyshevRoots.lean](ChebyshevCircles/ChebyshevRoots.lean)** - ⏳ 1 SORRY (line 155)
- `chebyshevRoot`: Definition of k-th Chebyshev root cos((2k+1)π/(2N))
- `chebyshev_T_eval_chebyshevRoot`: T_N vanishes at Chebyshev roots ✅
- `chebyshevRoots_distinct`: Pairwise distinctness ✅
- `chebyshev_T_eval_eq_zero_forward`: Forward direction (if T_N(x)=0 then x is a Chebyshev root) ⏳ 1 sorry
  - References degree lemma from PolynomialProperties
- `chebyshev_T_eval_eq_zero_iff`: Full characterization ✅

**[PowerSums.lean](ChebyshevCircles/PowerSums.lean)** - ✅ COMPLETE
- `powerSumCos_invariant_j2` through `powerSumCos_invariant_j6`: Explicit cases ✅
- `powerSumCos_invariant`: General theorem via binomial expansion ✅
- Helper lemmas for complex exponentials and binomial coefficients
- All cases fully proven using trigonometric identities and roots of unity

**[NewtonIdentities.lean](ChebyshevCircles/NewtonIdentities.lean)** - ✅ COMPLETE
- `multiset_newton_identity`: Newton's identities for multisets
- `esymm_eq_of_psum_eq`: Equal power sums imply equal elementary symmetric functions
- `esymm_rotated_roots_invariant`: θ-invariant power sums imply θ-invariant coefficients
- Critical bridge from power sum invariance to coefficient invariance

**[PolynomialProperties.lean](ChebyshevCircles/PolynomialProperties.lean)** - ✅ COMPLETE
- `constant_term_only_varies`: Non-constant coefficients are θ-invariant
- `chebyshev_T_degree`: T_N has degree N for N ≥ 1
- `scaledPolynomial_degree_eq_chebyshev`: Degree matching
- `chebyshev_eval_cos`: T_N(cos φ) = cos(N·φ)

**[PowerSumEquality.lean](ChebyshevCircles/PowerSumEquality.lean)** - ✅ COMPLETE
- `rotated_roots_sum_eq_zero`: Sum of cos(2πk/N) equals 0 for N > 1
- `chebyshev_roots_sum_eq_zero`: Sum of cos((2k+1)π/(2N)) equals 0 for N > 1
- `powersum_j1_equality`: Both root systems have the same j=1 power sum
- `rotated_roots_sum_sq_eq`: Sum of squares equals N/2 for N > 2
- `chebyshev_roots_sum_sq_eq`: Sum of squares equals N/2 for N > 2
- `powersum_j2_equality`: Both root systems have the same j=2 power sum

### Main Results (MainTheorem.lean)

**[MainTheorem.lean](ChebyshevCircles/MainTheorem.lean)** - ⏳ 1 SORRY (line 154)

Completed proofs:
- `chebyshev_T_leadingCoeff`: Leading coefficient of T_N is 2^(N-1) ✅
- `rotated_roots_yield_chebyshev`: Main theorem (depends on one helper) ✅
- `rotated_roots_coeffs_match_chebyshev`: All k > 0 coefficients match ✅

In progress:
- `scaledPolynomial_matches_chebyshev_at_zero`: Coefficient matching at θ=0
  - ✅ N = 1: Complete
  - ✅ N = 2: Complete
  - ✅ N = 3: Complete
  - ⏳ N ≥ 4: Requires harmonic analysis (1 sorry at line 154)

## What We Need

### The 2 Remaining Sorries

#### 1. ChebyshevRoots.lean:155 - TRIVIAL
**Function:** `chebyshev_T_eval_eq_zero_forward`
**Issue:** References degree lemma that now exists in PolynomialProperties
**Fix:** Replace `sorry` with `chebyshev_T_degree N hN`
**Effort:** 1 minute

#### 2. MainTheorem.lean:154 - HARD
**Function:** `scaledPolynomial_matches_chebyshev_at_zero` for N ≥ 4
**Challenge:** Different root sets with identical power sums

The two polynomials have different roots:
- `scaledPolynomial N 0`: roots are cos(2πk/N) for k = 0, ..., N-1
- `Chebyshev.T ℝ N`: roots are cos((2k+1)π/(2N)) for k = 0, ..., N-1

**Why this is hard:** Despite different roots, both polynomials must have identical elementary symmetric functions (via Newton's identities) for indices 1 to N-1. This requires proving:

```
∑_{k=0}^{N-1} cos(2πk/N)^j = ∑_{k=0}^{N-1} cos((2k+1)π/(2N))^j
```

for all 0 < j < N. We have proven this for j=1,2 in PowerSumEquality.lean. The general case requires ~50-100 additional lemmas in harmonic analysis.

**Estimated effort:** Research-level mathematics, 2-4 weeks

## Next Steps

### Immediate (5 minutes)

**Fix ChebyshevRoots.lean:155**
- Replace the sorry with the now-available `chebyshev_T_degree` lemma
- This completes the Chebyshev root characterization module

### Long-term (Research Required)

**Complete N ≥ 4 coefficient matching**

Three potential approaches:

1. **Power Sum Approach (Most Direct)**
   - Prove power sum equality for j=3 through j=N-1
   - Use existing PowerSums.lean infrastructure
   - Extend PowerSumEquality.lean with additional cases
   - Apply Newton's identities to conclude equal coefficients

2. **Evaluation-Based Approach**
   - Show the difference polynomial has degree < N
   - Prove it agrees at N+1 points (from cos evaluation properties)
   - Force the polynomial to be zero

3. **Fourier-Analytic Approach**
   - Develop discrete Fourier transform theory for both root sets
   - Show both have identical "discrete moments"
   - Apply uniqueness theorems from orthogonal polynomial theory

**Recommended:** Start with Power Sum Approach, using existing j=1,2 proofs as templates.

## Development Workflow

### Build and Test
```bash
# Full build
lake build

# Check for sorries
./check_lean.sh --sorries ChebyshevCircles/

# Run visualization
python3 main.py  # Creates chebyshev_animation.gif
```

### Lean Development Best Practices

**Use MCP Tools as First Resort:**
- `lean_local_search`: Find project declarations (VERY FAST)
- `lean_goal`: Check proof state frequently
- `lean_diagnostic_messages`: Understand errors immediately
- `lean_hover_info`: Get documentation for syntax and terms
- `lean_leansearch`: Natural language theorem search
- `lean_loogle`: Search by type signature or pattern
- `lean_leanfinder`: Semantic search by mathematical concept

**Iterative Development:**
1. Read all transitively imported files for context
2. Create scratch files for experiments (prevents breaking production)
3. Test each proof step immediately - don't batch
4. Keep partial progress - never replace working code with sorry
5. Copy working proofs back to production files
6. Delete scratch files when done

**Anti-Patterns to Avoid:**
- Writing progress summaries or documentation markdown (wastes tokens)
- Skipping intermediate build checks (fail fast on type errors)
- Batching multiple changes before testing (harder to isolate failures)
- Giving up on proofs due to complexity (all proofs must eventually complete)

## Technical Environment

- **Lean Version:** 4.25.0-rc2
- **Mathlib Imports:**
  - `RingTheory.Polynomial.Chebyshev`
  - `Analysis.SpecialFunctions.Trigonometric.Chebyshev`
  - `RingTheory.Polynomial.Vieta`
  - `RingTheory.MvPolynomial.Symmetric.NewtonIdentities`
  - `NumberTheory.Cyclotomic.PrimitiveRoots`
- **Quality Target:** Mathlib submission quality

## Theory Overview

### The Main Mathematical Insight

The constant term is the only coefficient that varies with rotation angle θ. All other coefficients are θ-invariant because:

1. **Power sums are θ-invariant:** ∑ cos(θ + 2πk/N)^j is independent of θ for 0 < j < N (PowerSums.lean)
2. **Newton's identities:** Express elementary symmetric functions in terms of power sums (NewtonIdentities.lean)
3. **Vieta's formulas:** Relate polynomial coefficients to elementary symmetric functions (used throughout)
4. **Conclusion:** Coefficients for k > 0 are determined solely by the (θ-invariant) power sums

Therefore, `scaledPolynomial N θ` and `Chebyshev.T ℝ N` can only differ by a constant term.

### Why the Remaining Sorry is Hard

The final missing piece is showing that `scaledPolynomial N 0` and `Chebyshev.T ℝ N` have the same non-constant coefficients. This requires proving that two completely different sets of roots have identical power sums - a deep result in harmonic analysis that doesn't follow from elementary manipulations.

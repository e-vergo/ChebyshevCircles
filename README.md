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

```
ChebyshevCircles/
├── ChebyshevCircles/
│   ├── Basic.lean                   # Placeholder imports
│   ├── RootsOfUnity.lean            # ✅ COMPLETE - Root definitions and properties
│   ├── PolynomialConstruction.lean  # ✅ COMPLETE - Polynomial construction
│   └── MainTheorem.lean             # ⏳ Main theorem (3 helper lemmas remain)
├── check_lean.sh                    # Analysis tool
├── main.py                          # Visualization
└── requirements.txt                 # Python dependencies
```

## Build Status

```
✅ Build: Clean compilation (3 sorry warnings only)
✅ Main theorem structure: Proven (depends on 3 helper lemmas)
✅ Infrastructure: RootsOfUnity and PolynomialConstruction fully complete
⏳ Remaining work: 3 mathematical lemmas in MainTheorem.lean
```

### Quick Status Summary

| Component | Status | Lines | Sorries |
|-----------|--------|-------|---------|
| RootsOfUnity.lean | ✅ Complete | 105 | 0 |
| PolynomialConstruction.lean | ✅ Complete | 550+ | 0 |
| MainTheorem.lean | ⏳ In Progress | 679 | 3 |
| **Total** | **95% Complete** | **1334+** | **3** |

**Critical path:** The 3 remaining lemmas form a dependency chain. Once `powerSumCos_invariant` is proven, the other two can be tackled in sequence.

## What We Have

### Complete Modules (100%)

**[RootsOfUnity.lean](ChebyshevCircles/RootsOfUnity.lean)** - ✅ COMPLETE
- Definitions: `rotatedRootsList`, `realProjectionsList`
- Basic properties: bounds, membership, cardinality
- **Key results:**
  - `realProjectionsList_sum`: List sum equals Finset sum conversion
  - `realProjectionsList_powersum`: Power sum conversion for arbitrary j
  - Helper lemma `list_range_map_sum_eq_finset_sum` for general conversions
- Status: All proofs complete, no sorries

**[PolynomialConstruction.lean](ChebyshevCircles/PolynomialConstruction.lean)** - ✅ COMPLETE
- Construction: `polynomialFromRealRoots`, `unscaledPolynomial`, `scaledPolynomial`
- Properties: degree, monic property, leading coefficient
- Constant term variation: Proven for all N ≥ 1
- Special cases: N = 1, 2, 3 with explicit verification
- Status: All proofs complete, no sorries

### Proven Main Results (MainTheorem.lean)

The main theorems are **structurally complete** (depend on 3 remaining helper lemmas):

```lean
theorem rotated_roots_yield_chebyshev (N : ℕ) (θ : ℝ) (hN : 0 < N) :
    ∃ (c : ℝ), scaledPolynomial N θ = Polynomial.Chebyshev.T ℝ N + C c

theorem rotated_roots_coeffs_match_chebyshev (N : ℕ) (k : ℕ) (θ : ℝ) (hN : 0 < N) (hk : 0 < k) :
    (scaledPolynomial N θ).coeff k = (Polynomial.Chebyshev.T ℝ N).coeff k
```

### Complete Infrastructure (MainTheorem.lean)

**Trigonometric identities:** ✅
- Sum of cosines at N equally-spaced angles: `sum_cos_roots_of_unity`
- Generalized sum for multiples: `sum_cos_multiple_rotated_roots`
- Power-reduction formulas: cos² through cos⁵
- Multiple angle formulas

**Power sum invariance (specific cases):** ✅
- j = 2, 3, 4, 5: Power sums ∑cos(θ + 2πk/N)^j are θ-independent

**List/Multiset conversions:** ✅ COMPLETE
- `multiset_coe_realProjectionsList_sum`: Multiset sum to Finset sum
- `multiset_powersum_realProjectionsList`: Multiset power sum to Finset sum
- `fin_univ_map_get`, `fin_sum_eq_multiset_sum`: Helper lemmas

**Elementary symmetric functions:** ✅
- `esymm_one_eq_sum`: First symmetric polynomial equals sum
- `esymm_rotated_roots_invariant`: θ-invariance for 0 < m < N (uses Newton's identities)

**Polynomial properties:** ✅
- Degree calculations
- Chebyshev recursion and evaluation: `chebyshev_eval_cos`
- Root evaluation

## What We Need

Three mathematical lemmas in [MainTheorem.lean](ChebyshevCircles/MainTheorem.lean) remain:

### Dependency Structure

```
[MEDIUM] General power sum invariance (line 357)
   ↓
[MEDIUM] Chebyshev leading coefficient (line 663)
   ↓
[HARD] Coefficient matching at θ=0 (line 668)
```

### The 3 Remaining Lemmas

#### 1. powerSumCos_invariant (line 357) - MEDIUM
**What:** Generalize proven j=2,3,4,5 cases to arbitrary 0 < j < N
```lean
∑ k ∈ Finset.range N, cos(θ₁ + 2πk/N)^j = ∑ k ∈ Finset.range N, cos(θ₂ + 2πk/N)^j
```

**Why it matters:** This is the key invariance property that allows us to relate polynomials at different rotation angles. Combined with Newton's identities, it proves that elementary symmetric functions (and thus polynomial coefficients) are θ-invariant for k > 0.

**Strategy A - Power Reduction (Recommended):**
- Use power-reduction formulas: cos^j(x) = linear combination of cos(kx) for k ≤ j
- Apply `sum_cos_multiple_rotated_roots` (already proven)
- Key insight: All cos(m·(2πi/N)) terms sum to zero when 0 < m < N
- This is a direct generalization of the j=2,3,4,5 cases already proven

**Strategy B - Complex Exponential:**
- Express cos(θ + 2πk/N) = Re(exp(i(θ + 2πk/N)))
- Use binomial expansion and geometric sum formulas
- Show all non-constant terms vanish

**Resources:**
- `sum_cos_multiple_rotated_roots` (line ~250): Already handles the geometric sum
- Proven cases j=2,3,4,5 (lines ~260-320): Templates for the pattern

#### 2. chebyshev_T_leadingCoeff (line 663) - MEDIUM
**What:** Prove the standard result that T_N has leading coefficient 2^(N-1) for N ≥ 1
```lean
(Polynomial.Chebyshev.T ℝ N).leadingCoeff = 2 ^ (N - 1)
```

**Why it matters:** Needed to show that `scaledPolynomial N θ` and `Chebyshev.T ℝ N` have the same leading coefficient, which is crucial for proving they differ only by a constant.

**Strategy - Induction on Recurrence:**
- Base cases: T₁ = X (leading coeff = 1 = 2⁰), T₂ = 2X² - 1 (leading coeff = 2 = 2¹)
- Recurrence: T_(n+2) = 2X·T_(n+1) - T_n
- Use `Polynomial.leadingCoeff_mul`, `Polynomial.leadingCoeff_sub_of_degree_lt`
- Inductive step: lc(2X·T_(n+1)) = 2·lc(T_(n+1)) = 2·2^n = 2^(n+1)
- The subtraction of T_n doesn't affect leading term since deg(T_n) < deg(2X·T_(n+1))

**Resources:**
- `Polynomial.Chebyshev.T_add_two` (Mathlib): Recurrence relation
- `Polynomial.leadingCoeff_mul` (Mathlib): lc(f·g) = lc(f)·lc(g)
- `Polynomial.leadingCoeff_sub_of_degree_lt` (Mathlib): Leading coeff preserved when subtracting lower-degree poly

**Alternative:** Search Mathlib - this is a standard result that may already exist

#### 3. scaledPolynomial_matches_chebyshev_at_zero (line 668) - HARD
**What:** At θ=0, prove coefficients match for k > 0
```lean
(scaledPolynomial N 0).coeff k = (Polynomial.Chebyshev.T ℝ N).coeff k  for k > 0
```

**Why it matters:** This is the deepest result connecting our construction to Chebyshev polynomials. Once proven, the main theorem follows immediately.

**Challenge:** The roots differ:
- `scaledPolynomial N 0`: roots are cos(2πk/N) for k = 0, ..., N-1
- `Chebyshev.T ℝ N`: roots are cos((2k-1)π/(2N)) for k = 1, ..., N

**Current proof structure:** Already uses `esymm_rotated_roots_invariant` to show coefficients k > 0 are θ-independent. Need to show they match Chebyshev.

**Strategy A - Evaluation-based:**
- Both polynomials have degree N, leading coefficient 2^(N-1)
- They differ by degree < N polynomial
- Prove they evaluate identically at N distinct points
- Use `Polynomial.eq_of_infinite_eval_eq` or similar uniqueness result

**Strategy B - Recurrence relation:**
- Show `scaledPolynomial N θ` satisfies same recurrence as Chebyshev
- Prove matching initial conditions
- Uniqueness of recurrence solution

**Strategy C - Direct computation:**
- Use the trigonometric evaluation: T_N(cos φ) = cos(Nφ)
- Show scaledPolynomial also satisfies this at appropriate points
- Leverage Fourier/trigonometric orthogonality

**This is a research problem:** May require new insights or different approach to current strategy.

## Next Steps

### Recommended Approach

**Phase 1: Power Sum Invariance** (Medium - 2-4 hours)
- Complete `powerSumCos_invariant` (line 357)
- Use power-reduction formulas (Strategy A recommended)
- Pattern already established in j=2,3,4,5 cases
- This unblocks the rest of the proof chain

**Phase 2: Chebyshev Leading Coefficient** (Medium - 1-2 hours)
- Complete `chebyshev_T_leadingCoeff` (line 663)
- Standard induction on Chebyshev recurrence
- Check Mathlib first - this may already exist
- Needed for the final coefficient matching

**Phase 3: Coefficient Matching** (Hard - Research TBD)
- Complete `scaledPolynomial_matches_chebyshev_at_zero` (line 668)
- This is the deepest mathematical result
- May require evaluation-based proof or new insights
- Consider multiple strategies before committing

### Execution Principles

**For formal verification:**
- Use MCP lean-lsp tools as first resort: `lean_local_search`, `lean_hover_info`, `lean_goal`
- Read transitively imported files for context
- Check proof state frequently with `lean_diagnostic_messages`

**Iterative workflow:**
- Create scratch files for experiments (prevents breaking main file)
- Test each proof step immediately
- Keep partial progress - never replace working tactics with sorry
- Delete scratch files when done

**Search strategies:**
- `lean_leansearch`: Natural language or Lean terms
- `lean_loogle`: Search by type shape or pattern
- `lean_local_search`: Project-specific lemmas
- `lean_state_search`: Theorems relevant to current proof state

**Avoid:**
- Writing documentation markdown (wastes context tokens)
- Batching multiple changes before testing
- Giving up on proofs due to complexity (all proofs must eventually complete)

## Development Commands

```bash
# Build
lake build

# Check sorries
./check_lean.sh --sorries ChebyshevCircles/MainTheorem.lean

# Visualization
python3 main.py  # Creates chebyshev_animation.gif
```

## Technical Details

- Lean 4.25.0-rc2
- Mathlib: RingTheory.Polynomial.Chebyshev, Analysis.SpecialFunctions.Trigonometric
- Target: Mathlib submission quality

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
│   ├── RootsOfUnity.lean            # ✅ Root definitions and properties
│   ├── PolynomialConstruction.lean  # ✅ Polynomial construction and properties
│   └── MainTheorem.lean             # ⏳ Main theorem (6 helper lemmas remain)
├── check_lean.sh                    # Analysis tool
├── main.py                          # Visualization
└── requirements.txt                 # Python dependencies
```

## Build Status

```
✅ Build: Clean compilation (6 sorry warnings only)
✅ Main theorem structure: Proven (depends on helper lemmas)
⏳ Remaining work: 6 helper lemmas in MainTheorem.lean
```

## What We Have

### Complete Modules

**RootsOfUnity.lean** - Rotated root definitions and basic properties
- Definitions: `rotatedRootsList`, `realProjectionsList`
- Properties: bounds, membership, cardinality
- All proofs complete

**PolynomialConstruction.lean** - Polynomial construction from roots
- Construction: `polynomialFromRealRoots`, `unscaledPolynomial`, `scaledPolynomial`
- Properties: degree, monic property, leading coefficient
- Constant term variation: Proven for all N ≥ 1
- All proofs complete

### Proven Main Results (MainTheorem.lean)

The main theorems are **structurally complete** (depend on 6 helper lemmas):

```lean
theorem rotated_roots_yield_chebyshev (N : ℕ) (θ : ℝ) (hN : 0 < N) :
    ∃ (c : ℝ), scaledPolynomial N θ = Polynomial.Chebyshev.T ℝ N + C c

theorem rotated_roots_coeffs_match_chebyshev (N : ℕ) (k : ℕ) (θ : ℝ) (hN : 0 < N) (hk : 0 < k) :
    (scaledPolynomial N θ).coeff k = (Polynomial.Chebyshev.T ℝ N).coeff k
```

### Supporting Infrastructure (MainTheorem.lean)

**Trigonometric identities:**
- Sum of cosines at N equally-spaced angles: `sum_cos_roots_of_unity`
- Generalized sum for multiples: `sum_cos_multiple_rotated_roots`
- Power-reduction formulas: cos² through cos⁵
- Multiple angle formulas

**Power sum invariance (specific cases proven):**
- j = 2, 3, 4, 5: Power sums ∑cos(θ + 2πk/N)^j are θ-independent

**Polynomial properties:**
- Degree calculations
- Chebyshev recursion and evaluation
- Root evaluation

## What We Need

Six helper lemmas in [MainTheorem.lean](ChebyshevCircles/MainTheorem.lean) remain. They form a dependency chain:

### Dependency Structure

```
[EASY] List/Finset conversions (lines 382, 388)
   ↓
[MEDIUM] Newton's identity (line 350)
   ↓
[MEDIUM] General power sum invariance (line 339)
   ↓
[TRIVIAL] Remove temporary axiom (line 37)
   ↓
[HARD] Chebyshev coefficient matching (line 32)
```

### The 6 Remaining Lemmas

#### 1. multiset_coe_realProjectionsList_sum (line 382)
**Difficulty:** Easy
**What:** Convert `(↑(realProjectionsList N θ) : Multiset ℝ).sum` to `∑ k ∈ Finset.range N, Real.cos(...)`
**Strategy:** Unfold definitions, use List.sum equals Finset.sum conversion

#### 2. multiset_powersum_realProjectionsList (line 388)
**Difficulty:** Easy
**What:** Same as #1 but with `.map (fun x => x ^ j)` applied
**Strategy:** Identical to #1 with additional map composition

#### 3. multiset_newton_identity (line 350)
**Difficulty:** Medium
**What:** Newton's identities relating `Multiset.esymm` to power sums
```lean
m * s.esymm m = (-1)^(m+1) * ∑_{i<m} (-1)^i * s.esymm i * psum_{m-i}
```
**Strategy:** (Detailed in code comments)
- Quotient multiset to list representation
- Apply `MvPolynomial.mul_esymm_eq_sum`
- Evaluate using `aeval`
- Use `MvPolynomial.aeval_esymm_eq_multiset_esymm` bridge

#### 4. powerSumCos_invariant (line 339)
**Difficulty:** Medium
**What:** Generalize proven j=2,3,4,5 cases to arbitrary j < N
```lean
∑ k, cos(θ₁ + 2πk/N)^j = ∑ k, cos(θ₂ + 2πk/N)^j
```
**Strategy:**
- Use power-reduction: cos^j(x) = linear combination of cos(kx) for k ≤ j
- Apply `sum_cos_multiple_rotated_roots` (already proven)
- All cos(k·(2πi/N)) terms sum to zero when k < N

**Alternative:** Complex exponential method via Re(exp(ijθ)) and geometric sums

#### 5. constant_term_only_varies_axiom (line 37)
**Difficulty:** Trivial (already proven!)
**What:** Remove axiom, replace with call to `constant_term_only_varies` (proven in PolynomialConstruction.lean)
**Strategy:** One-line fix once dependencies (#3, #4) complete

#### 6. scaledPolynomial_matches_chebyshev_at_zero (line 32)
**Difficulty:** Hard (research problem)
**What:** At θ=0, prove `(scaledPolynomial N 0).coeff k = (T_N).coeff k` for k > 0

**Challenge:** Roots cos(2πk/N) differ from Chebyshev roots cos((2k+1)π/(2N))

**Possible approaches:**
- Prove scaledPolynomial satisfies Chebyshev recurrence relation
- Use Chebyshev extremal property
- Trigonometric product identities
- Evaluation-based proof (both polynomials agree at sufficiently many points)

## Next Steps

### Recommended Approach

**Phase 1: List/Finset conversions** (Quick win - 30 min)
1. Complete `multiset_coe_realProjectionsList_sum` (line 382)
2. Complete `multiset_powersum_realProjectionsList` (line 388)
- These are routine conversions, unblock everything else

**Phase 2: Algebraic infrastructure** (Parallel - 4-6 hours)
Launch 2 agents in parallel:
- Agent A: `multiset_newton_identity` (line 350) - MvPolynomial machinery
- Agent B: `powerSumCos_invariant` (line 339) - Complex exponential method

**Phase 3: Integration** (Trivial - 5 min)
- Replace `constant_term_only_varies_axiom` with proven theorem

**Phase 4: Research** (Hard - TBD)
- `scaledPolynomial_matches_chebyshev_at_zero` (line 32)
- May require new insights into Chebyshev theory
- Consider multiple approaches before committing

### Execution Principles

**Context engineering:**
- Read ALL transitively imported files before writing proofs
- Use lean-lsp MCP tools extensively: `lean_local_search`, `lean_hover_info`, `lean_goal`
- Check proof state frequently with `lean_diagnostic_messages`

**Iterative development:**
- Create scratch files for experimentation (copy file, work there, copy back)
- Test each proof step immediately
- Keep partial progress - never replace working tactics with sorry

**Parallel execution:**
- Launch sonnet 4.5 agents for independent proofs
- Scratch files prevent interference between agents

**Avoid:**
- Writing markdown summaries (wastes tokens)
- Batching changes before testing
- Deleting partial proofs when stuck

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

# Chebyshev Circles

A mathematical discovery connecting rotated roots of unity to Chebyshev polynomials, with formal Lean 4 proof and Python visualization.

## The Mathematical Discovery

When the N-th roots of unity are rotated by angle θ and projected onto the real axis, the polynomial formed from these projections (scaled by 2^(N-1)) has coefficients that exactly match the N-th Chebyshev polynomial of the first kind, except for the constant term.

**The Main Result:**
```
For N-th roots of unity rotated by angle θ:
- Projected roots: cos(θ + 2πk/N) for k = 0, ..., N-1
- Polynomial P(x) = ∏(x - cos(θ + 2πk/N))
- Scaled polynomial S(x) = 2^(N-1) · P(x)

Then: S(x) = T_N(x) + c(θ)
where T_N is the N-th Chebyshev polynomial and c(θ) depends only on θ
```

## Project Components

### 1. Lean 4 Formalization (`ChebyshevCircles/`)

Formal proof targeting Mathlib submission quality.

**Files:**
- `RootsOfUnity.lean` - Definitions and lemmas for rotated roots and projections
- `PolynomialConstruction.lean` - Building and scaling polynomials from roots
- `MainTheorem.lean` - Main theorems and supporting lemmas

**Build:** `lake build`

### 2. Python Visualization (`main.py`)

Animated visualization showing roots rotating and the resulting polynomial.

**Setup and run:**
```bash
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
python3 main.py
```

Creates `chebyshev_animation.gif` showing the relationship dynamically.

### 3. Repository Analysis Tool (`check_lean.sh`)

Token-efficient tool for analyzing Lean proof status without full build output.

**Usage:**
```bash
./check_lean.sh --all sorries ChebyshevCircles/      # Summary of all sorries
./check_lean.sh --sorries ChebyshevCircles/MainTheorem.lean  # Sorries in specific file
./check_lean.sh --transparency ChebyshevCircles/MainTheorem.lean  # Check for proof evasion
./check_lean.sh --errors-only ChebyshevCircles/PolynomialConstruction.lean  # Only errors
```

## Current Status

### Build Health
```
✅ Build: Successful (0 compilation errors)
✅ Transparency: Clean (no proof evasion)
⏳ Sorries: 16 remaining (12 in MainTheorem.lean, 4 in PolynomialConstruction.lean)
⏳ Axioms: 0 (converted to theorems with sorry)
```

### ✅ Fully Proven Infrastructure

**Foundation (RootsOfUnity.lean) - 100% Complete:**
- `realProjection_eq_cos` - Real parts are cosine values
- `realProjection_mem_Icc` - Projections lie in [-1, 1]
- All helper lemmas for root definitions

**Polynomial Properties (PolynomialConstruction.lean) - Core lemmas complete:**
- `polynomialFromRealRoots_degree` - Degree equals root count
- `unscaledPolynomial_degree` - Unscaled has degree N
- `scaledPolynomial_degree` - Scaled preserves degree N
- `unscaledPolynomial_monic` - Leading coefficient is 1
- `scaledPolynomial_leadingCoeff` - Leading coefficient is 2^(N-1)

**Key Supporting Lemmas (MainTheorem.lean) - All proven:**
- `sum_cos_roots_of_unity` - ∑cos(θ + 2πk/N) = 0 for N≥2
- `list_foldr_eq_multiset_prod` - List.foldr equals Multiset.prod
- `chebyshev_T_degree` - T_N has degree N (proven by strong induction)
- `chebyshev_eval_cos` - T_N(cos φ) = cos(Nφ) (from Mathlib)
- `scaledPolynomial_eval_at_projection` - Polynomial vanishes at projected roots

**Main Theorems - Proven modulo 2 unproven helper theorems:**
1. `rotated_roots_yield_chebyshev`: ∃ c, scaledPolynomial N θ = T_N + C c
2. `rotated_roots_coeffs_match_chebyshev`: Coefficient matching for k > 0

### ⏳ Partially Complete Work

**`esymm_rotated_roots_invariant` proof architecture (~60% complete):**
- 4-phase proof structure built (~110 LOC)
- Phase A: `sum_cos_multiple_rotated_roots` - Geometric sum argument (3 sorries, ~15 LOC remaining)
- Phase B: `powerSumCos_invariant` - Binomial expansion (1 sorry, ~70 LOC remaining)
- Phase C: `multiset_esymm_from_psum` - Newton's identity bridge (1 sorry, ~50 LOC remaining)
- Phase D: `esymm_rotated_roots_invariant` - Strong induction (2 sorries, ~40 LOC remaining)

**`scaledPolynomial_constantTerm_varies` - Partially proven:**
- ✅ N=0: Fixed by adding hypothesis 0 < N
- ✅ N=1,2: Fully proven with norm_num
- ✅ N=3,5: Fully proven using Real.cos_eq_zero_iff and omega
- ✅ Architectural restructure: Odd/even split with correct angle pairs
- ⏳ N=4: Needs cosine inequality lemma (1 sorry)
- ⏳ N≥6 even: Needs cosine inequality lemma (1 sorry)
- ⏳ N≥5 odd: Needs cosine inequality lemma (2 sorries)

## Remaining Work

### Priority 1: Complete esymm Proof Architecture (~190 LOC)

This is the **critical path** that blocks `constant_term_only_varies`.

**Phase A: `sum_cos_multiple_rotated_roots` (~15 LOC)**
- 3 sorries remaining (lines 261, 270, 286)
- Goal: Prove ∑ cos(m(θ + 2πk/N)) = 0 for 0 < m < N
- Strategy: Complex exponentials + geometric sum of primitive roots
- Key lemma: `IsPrimitiveRoot.geom_sum_eq_zero`

**Phase B: `powerSumCos_invariant` (~70 LOC)**
- 1 sorry remaining (line 299)
- Goal: Power sums ∑ cos(θ + 2πk/N)^j are θ-invariant for 0 < j < N
- Strategy: Binomial expansion of cos^j = ((e^ix + e^-ix)/2)^j, then apply Phase A

**Phase C: `multiset_esymm_from_psum` (~50 LOC)**
- 1 sorry remaining (line 313)
- Goal: Bridge Multiset.esymm to Newton's identities
- Strategy: Use `MvPolynomial.psum_eq_mul_esymm_sub_sum` from Mathlib

**Phase D: `esymm_rotated_roots_invariant` (~40 LOC)**
- 2 sorries remaining (lines 352, 362)
- Goal: Elementary symmetric polynomials are θ-invariant
- Strategy: Strong induction using Phases A-C
  - Base case (m=1): Use `sum_cos_roots_of_unity`
  - Inductive step: Newton's identity + IH + power sum invariance

**Difficulty:** Very Hard (12-15 hours) - Deepest mathematical result in the project

### Priority 2: Complete `constant_term_only_varies` (~minimal work)

**Status:** 3 sorries remaining (lines 389, 398, 408)

**Dependency:** Requires `esymm_rotated_roots_invariant` from Priority 1

**Work Remaining:**
- Apply Vieta's formula: coeff k = (-1)^(N-k) · esymm(N-k)
- Use `esymm_rotated_roots_invariant` to show coefficients are θ-invariant
- Proof structure already exists, just needs esymm lemma

**Difficulty:** Medium (2-3 hours after esymm is complete)

**Follow-up:** Replace `constant_term_only_varies_axiom` with `constant_term_only_varies` throughout the file (5 minutes)

### Priority 3: Complete `scaledPolynomial_constantTerm_varies` (~80 LOC)

**Status:** 4 sorries remaining (lines 137, 244, 344, 345)

**Independent of other work - can be done in parallel**

**Remaining Cases:**
- N=4 (line 137): Prove cos(5π/8) ≠ 0 ∧ cos(9π/8) ≠ 0 ∧ cos(13π/8) ≠ 0
- N≥6 even (line 244): General lemma about cos(π(1+4k)/(2N)) ≠ 0
- N≥5 odd (lines 344-345): General lemma about cos(2πk/N) ≠ 0 for odd N

**Strategy:**
- Use `Real.cos_eq_zero_iff` (cos x = 0 ↔ x = (2m+1)π/2)
- Show the specific angles don't match this pattern via modular arithmetic
- Similar technique to already-proven N=3,5 cases

**Difficulty:** Medium (4-6 hours) - Mathematical reasoning is clear, needs formalization

### Priority 4: Prove `scaledPolynomial_matches_chebyshev_at_zero` (Hardest Task)

**Status:** 1 sorry (line 57) - This is a theorem statement, not an axiom

**Goal:** For θ=0, prove (scaledPolynomial N 0).coeff k = (T_N).coeff k for all k > 0

**Challenge:** The roots cos(2πk/N) are NOT the standard Chebyshev roots cos((2k+1)π/(2N)), yet the coefficients match. This is the deep mystery being formalized.

**Possible Approaches:**
1. **Recurrence relation:** Show scaledPolynomial satisfies the Chebyshev recurrence T_{n+1} = 2X·T_n - T_{n-1}
2. **Extremal characterization:** Use Chebyshev's minimax property
3. **Direct coefficient computation:** Calculate coefficients via Vieta's formulas and match to known T_N formulas
4. **Trigonometric identities:** Exploit cos(N·θ) product-to-sum formulas

**Difficulty:** Very Hard (12-15 hours) - Requires deep understanding of Chebyshev polynomial theory

**Recommendation:** Tackle this last, after all other work is complete

## Tools and Commands

### Lean Build
```bash
lake build                           # Build entire project
lake build ChebyshevCircles.MainTheorem  # Build specific file
```

### Status Checks
```bash
# Check all sorries across project
./check_lean.sh --all sorries ChebyshevCircles/

# Check specific file
./check_lean.sh --sorries ChebyshevCircles/MainTheorem.lean

# Check for proof evasion (axioms, sorry in definitions, etc.)
./check_lean.sh --all transparency ChebyshevCircles/

# Check for compilation errors only
./check_lean.sh --all errors-only ChebyshevCircles/
```

### Python Visualization
```bash
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
python3 main.py  # Creates chebyshev_animation.gif
```

## Mathematical Significance

1. **Unexpected connection:** Rotated roots don't match Chebyshev roots, yet coefficients align perfectly
2. **Scaling precision:** Exactly 2^(N-1), discovered through numerical experimentation
3. **Rotation invariance:** Non-constant structure is independent of rotation angle θ
4. **Potential applications:** May provide new perspective on Chebyshev polynomial properties

## Next Actions

### Immediate Work (Choose one)

**Option A: Complete esymm proof (Critical Path)**
- Start with Phase A (`sum_cos_multiple_rotated_roots`) - smallest piece (~15 LOC)
- This blocks `constant_term_only_varies` and ultimately the main theorems
- Highest mathematical depth

**Option B: Complete PolynomialConstruction cases (Independent)**
- Finish N=4,6+ cases with cosine inequality lemmas (~80 LOC)
- Independent of other work, can proceed in parallel
- Clearer path to completion

**Option C: Tackle Chebyshev connection (Hardest)**
- Prove `scaledPolynomial_matches_chebyshev_at_zero`
- Should probably wait until other work is complete
- Requires extensive Chebyshev polynomial theory

### Parallel Execution Strategy

The work naturally splits into 2 independent streams:

**Stream 1:** MainTheorem.lean
- Complete esymm proof (~190 LOC)
- Complete constant_term_only_varies (depends on esymm)
- Replace axiom with theorem (5 min)
- Tackle Chebyshev connection proof

**Stream 2:** PolynomialConstruction.lean
- Complete N=4,6+ cases (~80 LOC)
- Independent of Stream 1

### After All Sorries Are Resolved

1. **Remove `constant_term_only_varies_axiom`** - Replace with `constant_term_only_varies`
2. **Mathlib submission preparation:**
   - Add comprehensive documentation
   - Follow Mathlib style guide
   - Add test cases for small N
   - Performance optimization
3. **Submit to Mathlib**

## Project Structure

```
ChebyshevCircles/
├── ChebyshevCircles/
│   ├── Basic.lean                    # ✅ Complete
│   ├── RootsOfUnity.lean            # ✅ Complete
│   ├── PolynomialConstruction.lean   # ⏳ 4 sorries (N=4,6+ cases)
│   └── MainTheorem.lean              # ⏳ 12 sorries (esymm + helpers)
├── check_lean.sh                     # Repository analysis tool
├── main.py                           # Python visualization
├── requirements.txt                  # Python dependencies
└── README.md                         # This file
```

## Resources

- **Lean:** 4.25.0-rc2 with Mathlib
- **Python:** 3.13+ with numpy, Pillow
- **Documentation:** See file headers and inline comments for detailed proof strategies

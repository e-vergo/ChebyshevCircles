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

## What We Have Accomplished

### ✅ Fully Proven Core Lemmas

**Foundation (RootsOfUnity.lean):**
- `realProjection_eq_cos` - Real parts are cosine values
- `realProjection_mem_Icc` - Projections lie in [-1, 1]

**Polynomial Properties (PolynomialConstruction.lean):**
- `polynomialFromRealRoots_degree` - Degree equals root count
- `unscaledPolynomial_degree` - Unscaled has degree N
- `scaledPolynomial_degree` - Scaled preserves degree N
- `unscaledPolynomial_monic` - Leading coefficient is 1
- `scaledPolynomial_leadingCoeff` - Leading coefficient is 2^(N-1)

**Key Results (MainTheorem.lean):**
- `sum_cos_roots_of_unity` - ∑cos(θ + 2πk/N) = 0 for N≥2 ✅ COMPLETE
- `list_foldr_eq_multiset_prod` - List.foldr equals Multiset.prod ✅ COMPLETE
- `chebyshev_T_degree` - T_N has degree N ✅ COMPLETE (proven by strong induction)
- `chebyshev_eval_cos` - T_N(cos φ) = cos(Nφ) (from Mathlib)
- `scaledPolynomial_eval_at_projection` - Polynomial vanishes at projected roots

### ✅ Main Theorems Proven (Using Axioms)

1. **Main Theorem** (`rotated_roots_yield_chebyshev`):
   ```lean
   ∃ (c : ℝ), scaledPolynomial N θ = Chebyshev.T ℝ N + C c
   ```
   Status: ✅ Proven using two axioms

2. **Coefficient Matching** (`rotated_roots_coeffs_match_chebyshev`):
   ```lean
   ∀ k > 0, (scaledPolynomial N θ).coeff k = (Chebyshev.T ℝ N).coeff k
   ```
   Status: ✅ Proven (follows from main theorem)

## What We Need To Do Next

### Current Build Status
```
Build: Successful
Errors: 0
Sorries: 10 (across 4 theorems/lemmas)
Axioms: 2 (supporting main theorem)
```

### Priority 1: Prove Supporting Lemmas (Replace Sorries)

**1. `esymm_rotated_roots_invariant` (MainTheorem.lean:239)** - 1 sorry
- **What:** Elementary symmetric polynomials are θ-invariant for 0 < m < N
- **Current Status:** Comprehensive proof strategy documented using Newton's Identities
- **Strategy:**
  - STEP 1: Establish power sum invariance (∑ cos^j is θ-independent for j < N)
  - STEP 2: Apply Newton's identities relating e_k to power sums p_k
  - STEP 3: Use strong induction on m with base case m=1
- **Key Insight:** Power sums of rotated roots are invariant; Newton's identities then give esymm invariance
- **Difficulty:** Very Hard (8-12 hours) - Requires extensive complex number machinery
- **Mathematical Core:** This is the deepest mathematical result - rotation invariance of symmetric functions

**2. `constant_term_only_varies` (MainTheorem.lean:253)** - 3 sorries
- **What:** Non-constant coefficients are θ-invariant
- **Current Status:** Main proof structure complete using Vieta's formulas
- **Dependencies:** Requires `esymm_rotated_roots_invariant` above
- **Remaining Work:**
  - 2 sorries proving degree bounds (standard polynomial degree results)
  - The core logic connecting Vieta → esymm → invariance is complete
- **Strategy:** Apply Vieta's formula (coeff k = esymm(N-k)), use rotation invariance
- **Difficulty:** Medium (2-3 hours) - Mostly technical degree lemmas

**3. `scaledPolynomial_constantTerm_varies` (PolynomialConstruction.lean:117)** - 6 sorries
- **What:** Constant term varies with θ (show ∃θ₁,θ₂ with different constant terms)
- **Current:** N=1,2 fully proven with norm_num
- **Challenge Discovered:** Current proof strategy (θ=0 vs θ=π/2) fails for even N≥4
  - For even N: Both angles give 0 as a root, so both constant terms are 0
  - Need different angle pairs for even N (e.g., θ=0 vs θ=π/N)
- **Remaining Cases:**
  - N=0: Theorem false (needs hypothesis 0 < N)
  - N=3,5 (odd): Need `Real.cos_eq_zero_iff` or interval arithmetic
  - N=4,6+ (even): Need restructured proof with different angle choices
- **Difficulty:** Medium (4-6 hours) - Mathematical reasoning clear, needs formalization

### Priority 2: Replace Axioms

**1. `scaledPolynomial_matches_chebyshev_at_zero` (MainTheorem.lean:52)**
- **What:** For θ=0, all non-constant coefficients of scaledPolynomial match T_N
- **Why Hard:** Requires establishing the fundamental connection between our construction and Chebyshev polynomials
- **Possible Approaches:**
  1. **Extremal property:** Show both polynomials satisfy the same characterization
  2. **Direct computation:** Compute coefficients from roots using Vieta and match to T_N
  3. **Recurrence relation:** Show scaled polynomial satisfies T_n recurrence
- **Key Challenge:** The roots cos(2πk/N) are NOT the Chebyshev roots, yet coefficients match
- **Difficulty:** Very Hard (12-15 hours) - Requires deep Chebyshev polynomial theory
- **This is the hardest remaining task**

**2. `constant_term_only_varies_axiom` (MainTheorem.lean:64)**
- **What:** Temporary axiom wrapping `constant_term_only_varies` theorem
- **Strategy:** Simple removal once `constant_term_only_varies` is fully proven (replaces axiom with theorem)
- **Difficulty:** Trivial (5 minutes) - Just find-and-replace after dependency proven

### Priority 3: Mathlib Submission Preparation

1. **Complete all proofs** - Eliminate all sorries and axioms
2. **Add documentation** - Comprehensive docstrings for all public definitions
3. **Style compliance** - Follow Mathlib naming conventions and style guide
4. **Add tests** - Example computations for small N values
5. **Performance optimization** - Ensure proofs compile efficiently

## Repository Status Check

Run these commands to verify current state:

```bash
# Check all sorries
./check_lean.sh --all sorries ChebyshevCircles/

# Check for proof evasion patterns
./check_lean.sh --all transparency ChebyshevCircles/

# Verify no errors
./check_lean.sh --all errors-only ChebyshevCircles/
```

Current output shows:
- 2/4 files are sorry-free (Basic.lean, RootsOfUnity.lean)
- 2/4 files have sorries (MainTheorem.lean: 4, PolynomialConstruction.lean: 6)
- 2 axioms in MainTheorem.lean

**Breakdown by file:**
- `MainTheorem.lean`: 1 sorry in `esymm_rotated_roots_invariant`, 3 sorries in `constant_term_only_varies`
- `PolynomialConstruction.lean`: 6 sorries in `scaledPolynomial_constantTerm_varies` (N=0,3,4,5,6+ cases)

## Mathematical Significance

1. **Unexpected connection:** Rotated roots don't match Chebyshev roots, yet coefficients align perfectly
2. **Scaling precision:** Exactly 2^(N-1), discovered through numerical experimentation
3. **Rotation invariance:** Non-constant structure is independent of rotation angle θ
4. **Potential applications:** May provide new perspective on Chebyshev polynomial properties

## Implementation Strategy for Remaining Work

### For `esymm_rotated_roots_invariant` (Core Mathematical Challenge):

**Newton's Identities Approach:**
```lean
-- STEP 1: Prove power_sum_cos_invariant
-- Show ∑_{k=0}^{N-1} cos(θ + 2πk/N)^j is independent of θ for 0 < j < N
-- Use: cos^j(x) = linear combination of cos(kx) via binomial theorem
-- Apply: vanishing sums ∑ cos(i(θ + 2πk/N)) = 0 for 0 < i < N

-- STEP 2: Apply Newton's Identities
-- Newton's identities relate e_k (elementary symmetric) to p_k (power sums):
--   k·e_k = ∑_{i=1}^k (-1)^(i-1) e_{k-i} p_i
-- Use strong induction with power sum invariance

-- STEP 3: Base case and induction
-- Base: e_1 = ∑ roots = 0 (from sum_cos_roots_of_unity)
-- Inductive: Use Newton's identity with invariant power sums
```

**Required Infrastructure:**
- Complex exponential representation of cos^j
- Binomial theorem for (e^(ix) + e^(-ix))^j
- Geometric series for roots of unity
- Newton's identities formalization

### For `constant_term_only_varies` (Technical Completion):

**Using Vieta's Formulas:**
```lean
-- Structure already in place at MainTheorem.lean:253
-- Converts List.foldr → Multiset.prod (done via list_foldr_eq_multiset_prod)
-- Applies Vieta: coeff k = (-1)^(N-k) · esymm(N-k)
-- Uses esymm_rotated_roots_invariant for invariance

-- Remaining: 2 degree bound lemmas (standard results)
-- Prove: (Multiset.map (X - C r) M).prod.natDegree ≤ card M
```

### For `scaledPolynomial_constantTerm_varies` (Case-by-Case):

**Odd N Strategy (N=3,5,7,...):**
- Use θ=0 vs θ=π/2
- Need: `Real.cos_eq_zero_iff` (cos x = 0 ↔ x = (2m+1)π/2)
- Show: For odd N, 2πk/N ≠ (2m+1)π/2 for any integers k,m with 0<k<N

**Even N Strategy (N=4,6,8,...):**
- Current approach (θ=0 vs θ=π/2) fails
- Use different angles: θ=0 vs θ=π/N or θ=π/(2N)
- Show: One angle gives 0 as root, the other doesn't

### For axiom replacement (Hardest Task):

**Connecting Construction to Chebyshev:**
- The fundamental challenge: roots are cos(2πk/N), NOT Chebyshev roots cos((2k+1)π/(2N))
- Yet coefficients match - this is the deep mystery being formalized
- Possible approaches:
  1. Show both polynomials satisfy same recurrence + initial conditions
  2. Use Chebyshev's extremal characterization
  3. Direct calculation via coefficient formulas and trigonometric identities

## Tools and Resources

- **Lean:** 4.25.0-rc2 with Mathlib
- **Python:** 3.13+ with numpy, Pillow
- **Analysis:** check_lean.sh for efficient repository inspection

## Next Action Items

**Immediate Priorities (Can work in parallel):**

1. **Tackle `esymm_rotated_roots_invariant`** (Critical path, blocks other work)
   - Start with helper lemmas: `sum_cos_roots_of_unity_mul`, `power_sum_cos_invariant`
   - Build Newton's identity infrastructure
   - This is the mathematical core - most important proof

2. **Complete N≥3 cases in `scaledPolynomial_constantTerm_varies`**
   - Find or prove `Real.cos_eq_zero_iff`
   - Split odd/even N cases with appropriate angle pairs
   - Independent of other proofs, can proceed in parallel

**After `esymm_rotated_roots_invariant` completes:**

3. **Finish `constant_term_only_varies`**
   - Proof structure already complete
   - Just needs 2 degree bound lemmas
   - Quick win once dependency proven

4. **Remove `constant_term_only_varies_axiom`**
   - Simple find-and-replace
   - 5-minute task

**Final Boss:**

5. **Prove `scaledPolynomial_matches_chebyshev_at_zero`**
   - This is the hardest and most important axiom
   - Requires establishing fundamental Chebyshev connection
   - Should be tackled last with full attention

**Summary:** The project has strong foundations. Core infrastructure is proven (`list_foldr_eq_multiset_prod`, degree lemmas, evaluation lemmas). The remaining work centers on two deep mathematical results: (1) rotation invariance of symmetric polynomials, and (2) the connection between our construction and Chebyshev polynomials. Once these are proven, Mathlib submission readiness is within reach.
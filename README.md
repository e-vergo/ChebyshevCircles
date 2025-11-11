# Chebyshev Circles

When the N-th roots of unity are rotated by angle φ and projected onto the real axis and then taken to be the roots of a polynomial, after scaling by 2^(N-1) the polynomial formed from these projections equals the N-th Chebyshev polynomial of the first kind plus a φ-dependent constant.

```lean
theorem rotated_roots_yield_chebyshev (N : ℕ) (φ : ℝ) (hN : 0 < N) :
    ∃ (c : ℝ), scaledPolynomial N φ = Polynomial.Chebyshev.T ℝ N + C c
```

**Construction:**
- Projected roots: `cos(φ + 2πk/N)` for k = 0, ..., N-1
- Unscaled polynomial: `P(x) = ∏(x - cos(φ + 2πk/N))`
- Scaled polynomial: `S(x) = 2^(N-1) · P(x)`
- Result: `S(x) = T_N(x) + c(φ)`


## Project Organization

The proof is structured into 10 modules totaling 3,457 lines of Lean 4 code:

| Module | Lines | Purpose |
|--------|-------|---------|
| [RootsOfUnity.lean](ChebyshevCircles/RootsOfUnity.lean) | 108 | Root definitions and list properties |
| [PolynomialConstruction.lean](ChebyshevCircles/PolynomialConstruction.lean) | 541 | Polynomial construction from roots |
| [TrigonometricIdentities.lean](ChebyshevCircles/TrigonometricIdentities.lean) | 137 | Trigonometric sum identities |
| [ChebyshevRoots.lean](ChebyshevCircles/ChebyshevRoots.lean) | 235 | Chebyshev root characterization |
| [PowerSums.lean](ChebyshevCircles/PowerSums.lean) | 705 | Power sum φ-invariance |
| [NewtonIdentities.lean](ChebyshevCircles/NewtonIdentities.lean) | 317 | Newton's identities framework |
| [PolynomialProperties.lean](ChebyshevCircles/PolynomialProperties.lean) | 130 | Polynomial degree and coefficient properties |
| [PowerSumEquality.lean](ChebyshevCircles/PowerSumEquality.lean) | 273 | General power sum equality |
| [ChebyshevOrthogonality.lean](ChebyshevCircles/ChebyshevOrthogonality.lean) | 538 | Discrete orthogonality relations |
| [MainTheorem.lean](ChebyshevCircles/MainTheorem.lean) | 473 | Main theorem and supporting results |

## Mathematical Content

### Core Definitions

**Rotated Roots** ([RootsOfUnity.lean](ChebyshevCircles/RootsOfUnity.lean))
- `rotatedRootsOfUnity N φ`: N-th roots of unity rotated by angle φ
- `realProjections N φ`: Real parts of rotated roots as a multiset
- `realProjectionsList N φ`: List representation for computation

**Polynomial Construction** ([PolynomialConstruction.lean](ChebyshevCircles/PolynomialConstruction.lean))
- `polynomialFromRealRoots`: Construct polynomial from list of real roots
- `unscaledPolynomial N φ`: Monic polynomial with rotated roots as zeros
- `scaledPolynomial N φ`: Unscaled polynomial multiplied by 2^(N-1)

**Chebyshev Roots** ([ChebyshevRoots.lean](ChebyshevCircles/ChebyshevRoots.lean))
- `chebyshevRoot N k`: The k-th Chebyshev root `cos((2k+1)π/(2N))`
- Full characterization of zeros of T_N on [-1, 1]

### Key Results

**Trigonometric Identities** ([TrigonometricIdentities.lean](ChebyshevCircles/TrigonometricIdentities.lean))
- `sum_cos_roots_of_unity`: Sum of cosines over N equally-spaced angles vanishes
- `sum_cos_multiple_rotated_roots`: Generalization to integer multiples

**Power Sum Invariance** ([PowerSums.lean](ChebyshevCircles/PowerSums.lean))
- `powerSumCos_invariant`: For 0 < j < N, the sum ∑ cos(φ + 2πk/N)^j is independent of φ
- Proof uses binomial expansion and geometric sum cancellation

**Newton's Identities** ([NewtonIdentities.lean](ChebyshevCircles/NewtonIdentities.lean))
- `esymm_eq_of_psum_eq`: Equal power sums imply equal elementary symmetric functions
- `esymm_rotated_roots_invariant`: Polynomial coefficients (except constant term) are φ-invariant

**Discrete Orthogonality** ([ChebyshevOrthogonality.lean](ChebyshevOrthogonality.lean))
- `sum_cos_chebyshev_angles_vanishes`: Odd frequency terms vanish via involution pairing
- `sum_cos_chebyshev_angles_even_vanishes`: Even frequency terms vanish via geometric sums
- `binomial_terms_vanish_chebyshev`: All non-constant binomial expansion terms cancel

**Power Sum Equality** ([PowerSumEquality.lean](ChebyshevCircles/PowerSumEquality.lean))
- `general_powersum_equality`: For all 0 < j < N, power sums over rotated roots equal power sums over Chebyshev roots
- Closed-form value lemmas for both root systems

**Polynomial Properties** ([PolynomialProperties.lean](ChebyshevCircles/PolynomialProperties.lean))
- `constant_term_only_varies`: All coefficients except the constant term are φ-independent
- Degree and leading coefficient lemmas

**Main Results** ([MainTheorem.lean](ChebyshevCircles/MainTheorem.lean))
- `chebyshev_T_leadingCoeff`: Leading coefficient of T_N is 2^(N-1) for N ≥ 1
- `scaledPolynomial_matches_chebyshev_at_zero`: All non-constant coefficients match at φ=0
- `rotated_roots_coeffs_match_chebyshev`: Coefficients match for all φ
- `rotated_roots_yield_chebyshev`: Main theorem

## Proof Architecture

The proof establishes that the constant term is the only coefficient varying with rotation angle φ:

1. **Power sum φ-invariance**: For rotated roots at `cos(φ + 2πk/N)`, power sums ∑ cos^j are independent of φ for 0 < j < N

2. **Discrete orthogonality**: For Chebyshev roots at `cos((2k+1)π/(2N))`, binomial expansion terms vanish via:
   - Odd frequencies: Involution pairing using cos(π - x) = -cos(x)
   - Even frequencies: Geometric sum cancellation

3. **Power sum equality**: Both root systems yield identical power sum values for all 0 < j < N

4. **Newton's identities**: Power sums determine elementary symmetric functions, which determine polynomial coefficients via Vieta's formulas

5. **Coefficient matching**: Since power sums match and determine all non-constant coefficients, the polynomials differ only by a constant

## Proof Techniques

The formalization employs:

- **Binomial expansion** via De Moivre's formula for cos^j
- **Discrete Fourier analysis** using roots of unity and geometric sums
- **Involution arguments** exploiting symmetry of Chebyshev angles
- **Newton's identities** connecting power sums to elementary symmetric functions
- **Primitive root theory** from Mathlib's cyclotomic infrastructure
- **Complex exponential methods** for trigonometric sum evaluation

## Technical Environment

**Lean Version:** 4.25.0-rc2

**Key Mathlib Dependencies:**
- `RingTheory.Polynomial.Chebyshev`
- `Analysis.SpecialFunctions.Trigonometric.Chebyshev`
- `RingTheory.Polynomial.Vieta`
- `RingTheory.MvPolynomial.Symmetric.NewtonIdentities`
- `NumberTheory.Cyclotomic.PrimitiveRoots`
- `Analysis.SpecialFunctions.Trigonometric.Complex`

**Build Information:**
```bash
# Full project build
lake build
# Expected: Build completed successfully (2454 jobs)

# Verify no sorries
grep -r "sorry" ChebyshevCircles/*.lean | grep -v "^--"
# Expected: No output
```

## Documentation

All modules include:
- Module-level docstrings describing purpose and main results
- Declaration-level docstrings for all public definitions, lemmas, and theorems
- Implementation notes explaining proof strategies
- Full adherence to Mathlib style guidelines

## Code Quality

- Zero axioms beyond Lean's core foundations
- Zero sorry placeholders
- Complete type-checked verification
- Modular architecture with clear dependencies
- Helper lemmas extracted for complex case analysis
- All line lengths within 100-character limit
- Consistent naming conventions following Mathlib standards

## Significance

This formalization provides a computer-verified proof connecting:

- Algebraic structures (roots of unity, polynomial rings)
- Trigonometric functions (cosine at special angles)
- Orthogonal polynomials (Chebyshev polynomials)
- Harmonic analysis (discrete orthogonality relations)

The proof demonstrates that research-level results involving multiple mathematical domains can be completely formalized in dependent type theory with full mechanical verification.

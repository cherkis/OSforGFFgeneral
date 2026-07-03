# Architecture

How the 48 files fit together. For proof details see the paper (§4); for the
dimension-generic design (the `GFFPropagator` typeclass and where the dimension
enters each axiom) see `dimension_generic.md`.

## Dependency layers

```
General ──→ Spacetime ──→ Covariance ──→ Schwinger ──→ Measure ──→ OS
  (12)        (9)           (3)           (3)           (6)       (13)
                               ↑
                          Instances (2): the per-dimension closed forms
                          (4D Bessel), consumed only by the d = 4
                          headline theorem and OS/NonTrivial's UV statement
```

All proof files are parameterized by the spacetime dimension `d` and consume the
covariance only through the `GFFPropagator d m` typeclass
(`Covariance/Propagator.lean`).

Imports flow left to right with one cross-cutting edge:

- `Measure/IsGaussian` imports `OS/OS0_Analyticity` to use the proved
  analyticity for the identity-theorem argument S₂ = C.

This is not circular: OS0 depends on `Measure/Construct` (the measure must
exist before we can prove analyticity), and `IsGaussian` feeds back into
the later OS proofs (OS1–OS4 need S₂ = C).

## No assumed axioms

Everything is proved: `#print axioms` for the master theorem (both the
dimension-generic form and its four-dimensional instance) shows exactly Lean's
three foundational axioms — `propext`, `Classical.choice`, `Quot.sound`. The
footprint can be re-checked at any time with
`#print axioms OSforGFF.gaussianFreeField_satisfies_all_OS_axioms`.

## OS3: the longest proof chain

OS3 (reflection positivity) is the most technically involved axiom, spanning
4 files and ~7100 lines. The logical chain:

1. **MixedRepInfra** (~3800 lines): Schwinger parametrization makes all
   integrals absolutely convergent (the naive momentum-space approach fails
   because 1/√(k²+m²) is not L¹ in the spatial momentum space). Proves ~36
   Fubini exchange and integrability lemmas; the single place the hypothesis
   `d ≤ 5` is used (see `dimension_generic.md`).

2. **MixedRep** (~1900 lines): Chains the exchanges to reach the mixed
   representation ⟨Θf, Cf⟩ = ∫ (1/ω)|F_ω(k̄)|² dk̄, going through
   heat kernel → Fourier → Gaussian k₀ integral → Laplace transform.

3. **CovarianceRP** (~460 lines): Defines the star operation
   `(star f)(x) = conj(f(Θx))` on complex test functions and proves
   `Re⟨star f, Cf⟩ ≥ 0` for positive-time f.  The factorization
   |−x₀−y₀| = x₀+y₀ for positive-time support makes the integrand a
   perfect square.  Bridges to real test functions via
   `star (toComplex f) = compTimeReflection (toComplex f)`.

4. **ReflectionPositivity** (~1020 lines): Two independent proofs.

   **Real version** (lines 52–530): Schur–Hadamard lift for real coefficients:
   R_ij = ⟨Θfᵢ, Cfⱼ⟩ is PSD → exp(R) is PSD (Hadamard series) →
   ∑ cᵢcⱼ Z[fᵢ−Θfⱼ] ≥ 0.

   **Complex version** (lines 532–1023): Full Osterwalder–Schrader formulation
   with complex test functions and complex coefficients.  The matrix entry
   factorizes as Z_ℂ[fᵢ − star fⱼ] = Aᵢ · conj(Aⱼ) · exp(Rᵢⱼ) where
   Rᵢⱼ = C(fᵢ, star fⱼ) is Hermitian PSD.  Key ingredients:
   - `star` antilinearity: star(∑ c̄ⱼfⱼ) = ∑ cⱼ star(fⱼ)
   - Hermiticity: R_{ji} = conj(R_{ij}) via C(star f, star g) = conj(C(f,g))
   - Complex Schur product theorem (Kronecker ⊗ diagonal submatrix)
   - Complex entrywise exponential PSD via Hadamard power series limit

## OS4: two-stage argument

1. **Clustering** (OS4_Clustering): Gaussian factorization reduces the
   clustering bound to estimating S₂(f, T_{−s}g), which decays as
   (1+|s|)^{−α} by Schwartz convolution decay with the exponentially decaying
   kernel |C(z)| ≤ A e^{−(m/2)|z|} for |z| ≥ 1 (the mass gap, from the
   proper-time representation).

2. **Ergodicity** (OS4_Ergodicity): Polynomial clustering with α = 6 feeds
   into an L² time-average bound: ‖(1/t)∫₀ᵗ A(T_s φ) ds − 𝔼[A]‖² ≤ C/t → 0.

## Key design choices

- **Schwartz over D**: We use S(ℝ^d) rather than D(ℝ^d) because Mathlib has
  SchwartzSpace but not test function spaces with compact support. Since
  D ⊂ S and S' ⊂ D', our axioms imply the Glimm–Jaffe versions.

- **Schwinger parametrization for OS3**: The direct momentum-space Fubini
  fails (conditional convergence). The Schwinger representation
  C = ∫₀^∞ e^{−sm²} H_s ds introduces the heat kernel as a regularizer,
  making all integrals absolutely convergent.

- **Proper-time kernel for Parseval**: The Parseval identity
  ⟨f, C f̄⟩ = ∫ ‖𝓕f‖²/((2π)²‖k‖²+m²) is derived against the proper-time
  covariance (which is L¹ with an explicit Fourier transform), avoiding
  convergence issues with the bare propagator — no regulator needed
  (`Covariance/ParsevalGeneric.lean`).

- **Closed form behind a typeclass**: Rather than Fourier-transforming the
  propagator directly (conditionally convergent), C(x,y) is the radial profile
  `Cprofile |x−y|` of a `GFFPropagator d m` instance, identified with the
  Schwinger integral by the instance's one obligation `schwinger_eq`. The 4D
  instance supplies (m/4π²r)K₁(mr) (`Instances/Dim4.lean`).

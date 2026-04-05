# Dimension Dependence

This branch works in spacetime dimension $d = 2$ (spatial dimension $d-1 = 1$). The project defines `STDimension := 2` in `Basic.lean`.

## Dimension-specific formulas (d=2)

The following formulas are specific to $d = 2$.

### Covariance kernel (`CovarianceMomentum.lean`)
- **Bessel representation:** `freeCovarianceBessel` gives $C(x,y) = \frac{1}{2\pi} K_0(m\|x-y\|)$, the closed-form specific to $d=2$.
- **Heat kernel:** `heatKernelPositionSpace_2D` evaluates $(4\pi t)^{-d/2}$ to $\frac{1}{4\pi t}$.
- **Singularity:** Logarithmic, $C(x,y) \sim -\frac{1}{2\pi}\log(\|x-y\|)$ as $\|x-y\| \to 0$.
- **Large-distance decay:** $C(x,y) \sim e^{-mr}/\sqrt{r}$ for $r = \|x-y\| \to \infty$.

### Plancherel scaling (`Parseval.lean`)
- The factor $(2\pi)^2$ appears in `regulated_fubini_factorization`, `parseval_covariance_schwartz_regulated`, and related Fourier identities.

### Schwinger proper-time integral (`OS3_MixedRepInfra.lean`)
- Uses the 2D heat kernel $\frac{1}{4\pi t} e^{-r^2/(4t)}$ via `heatKernelPositionSpace_2D` in the Laplace $s$-integral.

### Mixed representation normalization (`OS3_MixedRep.lean`)
- Uses $(2\pi)^2 / (2\pi) = 2\pi$ to factor the mixed representation.

### Bessel function (`BesselFunction.lean`, `BesselK0Proofs.lean`)
- $K_0$ is the modified Bessel function appearing in the $d=2$ covariance. In general dimension $d$, the covariance involves $K_{d/2-1}$.
- $K_1$ is also defined and proved (positivity, asymptotics, Schwinger integral identity) as shared infrastructure with the $d=4$ branch, but is not used in the $d=2$ covariance formula.

### Spatial integrability (`FunctionalAnalysis.lean`, `SchwartzProdIntegrable.lean`)
- `polynomial_decay_integrable_3d` uses $(1+\|x\|)^{-4}$ integrable in $\mathbb{R}^1$ (decay rate $4 > d-1 = 1$).
- `SpatialCoords3` resolves to `EuclideanSpace ℝ (Fin 1)`.
- `Fin.sum_univ_two` expands $\|k\|^2 = k_0^2 + k_1^2$ (in `OS4_Clustering.lean`).

### Local integrability (`OS1_GFF.lean`)
- The 2D covariance has a logarithmic singularity ($K_0(z) \sim -\log(z/2) - \gamma$ near $z=0$), which is locally integrable in $\mathbb{R}^2$. Proved via `locallyIntegrable_of_log_singularity`.

## Structural (dimension-agnostic)

These files reference `STDimension` or `SpaceTime` but work for any $d \ge 2$.

| File | Usage |
|------|-------|
| `Basic.lean` | Defines `STDimension`, `SpaceTime`, `getTimeComponent`, `SpatialCoords`, `spatialPart`, `E` |
| `OS_Axioms.lean` | OS axiom definitions (quantify over test functions on `SpaceTime`) |
| `Euclidean.lean` | Euclidean group $E(d) = O(d) \rtimes \mathbb{R}^d$ |
| `DiscreteSymmetry.lean` | Time reflection matrix in $O(d)$ |
| `TimeTranslation.lean` | Time translation $T_s$ (shift index 0) |
| `SpacetimeDecomp.lean` | Decomposition $\mathbb{R}^d \cong \mathbb{R} \times \mathbb{R}^{d-1}$ |
| `ComplexTestFunction.lean` | Complex test function operations |
| `PositiveTimeTestFunction_real.lean` | Positive-time support predicate |
| `Schwinger.lean` | Schwinger $n$-point functions |
| `SchwingerTwoPointFunction.lean` | Distributional 2-point function |
| `Parseval.lean` | Parseval/Plancherel identity (uses $(2\pi)^d$ scaling, inherits $d=2$) |
| `Covariance.lean` | Bilinear covariance form (uses Parseval, inherits $d=2$) |
| `CovarianceR.lean` | Real covariance, Hilbert space embedding |
| `GaussianFreeField.lean` | GFF measure construction via Minlos |
| `GFFMconstruct.lean` | Measure construction infrastructure |
| `GFFIsGaussian.lean` | Gaussianity verification |
| `GaussianMoments.lean` | Moment computations |
| `Minlos.lean` | Minlos theorem (axiom, dimension-independent) |
| `MinlosAnalytic.lean` | Analytic continuation of characteristic functional |
| `OS0_GFF.lean` | OS0 proof (analyticity) |
| `OS2_GFF.lean` | OS2 proof (Euclidean invariance) |
| `OS3_CovarianceRP.lean` | Covariance reflection positivity (uses mixed rep, inherits $d=2$) |
| `OS3_GFF.lean` | OS3 assembly (includes RP bridge to real formulation) |
| `OS4_MGF.lean` | MGF infrastructure for OS4 |
| `OS4_Ergodicity.lean` | Ergodicity from polynomial clustering |
| `L2TimeIntegral.lean` | $L^2$ time integral estimates |
| `GFFmaster.lean` | Master theorem assembly |
| `FourierTransforms.lean` | 1D Fourier transform identities |
| `LaplaceIntegral.lean` | Laplace/Glasser integrals |
| `HadamardExp.lean` | Hadamard exponential |
| `SchurProduct.lean` | Schur product theorem |
| `FrobeniusPositivity.lean` | Frobenius inner product positivity |
| `PositiveDefinite.lean` | Positive-definite function theory |
| `GaussianRBF.lean` | Gaussian RBF positive definiteness |
| `QuantitativeDecay.lean` | Polynomial decay estimates |
| `SchwartzTranslationDecay.lean` | Bilinear translation decay |
| `SchwartzTonelli.lean` | Tonelli for spacetime integrals |

## Generic QFT framework (new on this branch)

These files provide an abstract `QFTFramework` interface that parameterizes the OS axioms over different spacetime geometries, enabling reuse across flat $\mathbb{R}^d$, cylinder $\mathbb{R} \times \mathbb{T}^{d-1}$, and lattice $a\mathbb{Z}^d$ settings.

| File | Usage |
|------|-------|
| `QFTFramework.lean` | Abstract `QFTFramework` structure: `Spacetime`, `TestFunction`, symmetry group, time reflection/translation |
| `QFTFramework/Instances.lean` | Concrete instances: `QFTFramework.flat d` ($\mathbb{R}^d$), `QFTFramework.lattice d a` ($a\mathbb{Z}^d$) |
| `OS_Axioms_Generic.lean` | OS0–OS4 restated generically over any `QFTFramework` |
| `LatticeSpacetime.lean` | Lattice spacetime $a\mathbb{Z}^d$: `SpaceTimeLattice`, `latticeEmbed`, `TestFunctionLattice`, Riemann-sum pairing |

## Comparison: d=2 vs d=4

The `dimensions` branch carries the $d=4$ version. The table below summarizes the key differences.

| Quantity | $d=2$ (this branch) | $d=4$ (`dimensions` branch) |
|----------|----------------------|------------------------------|
| `STDimension` | `2` | `4` |
| Bessel function in covariance | $K_0$: $C(r) = \frac{1}{2\pi} K_0(mr)$ | $K_1$: $C(r) = \frac{m}{4\pi^2 r} K_1(mr)$ |
| Short-distance singularity | Logarithmic: $-\frac{1}{2\pi}\log r$ | Power-law: $\|x\|^{-(d-2)} = \|x\|^{-2}$ |
| Local integrability proof | `locallyIntegrable_of_log_singularity` | `locallyIntegrable_of_rpow_decay_real` ($\alpha=2 < d=4$) |
| Heat kernel | $(4\pi t)^{-1}$ | $(4\pi t)^{-2} = \frac{1}{16\pi^2 t^2}$ |
| Plancherel factor | $(2\pi)^2$ | $(2\pi)^4$ |
| Mixed rep normalization | $(2\pi)^2/(2\pi) = 2\pi$ | $(2\pi)^4/(2\pi) = (2\pi)^3$ |
| Spatial dimension type | `EuclideanSpace ℝ (Fin 1)` | `EuclideanSpace ℝ (Fin 3)` |
| Spatial integrability lemma | `polynomial_decay_integrable_3d` on $\mathbb{R}^1$ | `polynomial_decay_integrable_3d` on $\mathbb{R}^3$ |
| Norm decomposition | `Fin.sum_univ_two` ($k_0^2 + k_1^2$) | `Fin.sum_univ_four` ($k_0^2+k_1^2+k_2^2+k_3^2$) |
| Generic QFT framework | Present (`QFTFramework`, lattice, generic axioms) | Not present |
| `BesselK0Proofs.lean` | Present (K_0 proofs + shared K_1 infrastructure) | Not present (K_1 proofs inline) |

## Generalization to d=3

To port the project to $d = 3$ (massive free boson in 3D, relevant for statistical mechanics):
1. Change `STDimension` to `3` in `Basic.lean`.
2. Replace $K_0$ with $K_{1/2}$ (which has the elementary form $\sqrt{\pi/(2mr)}\, e^{-mr}$).
3. Update the heat kernel to $(4\pi t)^{-3/2}$.
4. Update Plancherel scaling factors from $(2\pi)^2$ to $(2\pi)^3$.
5. Update spatial integrability: decay rate must exceed $d-1 = 2$ in $\mathbb{R}^2$.
6. Replace `Fin.sum_univ_two` with `Fin.sum_univ_three`.

The d=4 branch is on `dimensions`.

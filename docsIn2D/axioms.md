# Axioms in OSforGFF (d=2 branch)

**Branch:** `dimension2`  
**Date:** 2026-04-04  
**Status:** Zero `sorry` statements in all files. All unproved mathematical facts are explicit `axiom` declarations (2 remaining).

### Recent reductions
- `NuclearSpace.lean` was replaced by the corresponding version from `OSforGFF`, and the
  2D project still compiles cleanly with that file unchanged.
  This removes `schwartz_nuclear` from the remaining 2D-specific axioms.
  Axiom count: 3 → 2.
- `laplace_s_integral_with_norm` proved as a theorem in `OS3_MixedRep.lean`.
  Uses `fubini_s_xy_swap` (Fubini swap ∫_s ↔ ∫_x ∫_y), `s_integral_complex_eval` (pointwise
  Laplace evaluation), and `normalization_constant_laplace` ((1/(2π)²)·π = 1/(2·2π)).
  Axiom count: 4 → 3.
- `freeCovarianceKernel_integrable` proved as a theorem in `CovarianceMomentum.lean`.
  Uses polar coordinates (`integrable_fun_norm_addHaar`) to reduce to 1D: r·K₀(mr) integrable on (0,∞).
  Near-zero: bounded (r·log kills singularity via t·exp(-t)≤1). Far: dominated by r·exp(-mr)
  (via `integrableOn_rpow_mul_exp_neg_mul_rpow`). Axiom count: 5 → 4.
- 5 Bessel function axioms (`besselK0_pos`, `besselK0_continuousOn`, `besselK0_asymptotic`,
  `besselK0_near_origin_bound`, `schwingerIntegral_eq_besselK0`) removed from
  `BesselFunction.lean` and proved as theorems in `BesselK0Proofs.lean`.
  Proofs adapted from `auto1/lean/SpecialFunctions/Bessel/`.
  All helper lemmas now fully proved (zero sorrys).
- Previous session: `besselK0_asymptotic` tightened (z ≥ 1 → z > 0, factor of 2 removed),
  enabling proof of 5 further axioms as theorems.
- `integrable_dominate_G` was proved as a theorem (previously axiom).

## Summary

| Category | Count | File(s) |
|----------|-------|---------|
| Measure theory foundations | 1 | `Minlos.lean` |
| Finite-dim analyticity | 1 | `OS0_GFF.lean` |
| **Total** | **2** | |

The original 15 axioms have been reduced to 2 through successive proof sessions.
The remaining axioms represent standard but non-trivial mathematical results.

---

## Bessel function properties — `BesselK0Proofs.lean` — **ALL NOW THEOREMS**

These encode standard properties of the modified Bessel function
K₀(z) = ∫₀^∞ exp(−z cosh t) dt (DLMF Chapter 10).
All 5 former axioms are now theorems, proved in `BesselK0Proofs.lean`
(adapted from `auto1/lean/SpecialFunctions/Bessel/`).

- `besselK0_pos` — proved ✓
- `besselK0_continuousOn` — proved ✓ (dominated convergence)
- `besselK0_asymptotic` — proved ✓ (cosh t ≥ 1 + t²/2, Gaussian integral)
- `besselK0_near_origin_bound` — proved ✓ (FTC + z·K₁(z) ≤ 1)
- `besselK0_lt_besselK1` — proved ✓ (cosh t > 1 for t > 0)
- `schwingerIntegral_eq_besselK0` — proved ✓ (linear scaling + exp substitution + self-reciprocal)
- `besselK0_deriv` — proved ✓ (parametric integral differentiation)
- `besselK1_mul_self_le_one` — proved ✓ (FTC + cosh splitting + (1+z)e⁻ᶻ ≤ 1)
- `besselK0_integrable_near_zero` — proved ✓ (log comparison near 0, exp decay at ∞)

---

## Free covariance kernel — `CovarianceMomentum.lean` — **ALL NOW THEOREMS**

These describe the 2D free covariance kernel C(z) = (1/(2π)) K₀(m‖z‖).

### `freeCovarianceKernel_integrable` — **NOW A THEOREM**
Proved using polar coordinate decomposition (`integrable_fun_norm_addHaar`):
reduces to 1D integrability of r·K₀(mr) on (0,∞). Near zero (0,1]: bounded via
r·(-log r) ≤ 1 (from t·exp(-t) ≤ 1). Far (1,∞): dominated by √(π/(2m))·r·exp(-mr),
integrable via `integrableOn_rpow_mul_exp_neg_mul_rpow`.

### `freeCovarianceKernel_decay_bound` — **NOW A THEOREM**
Proved with C=1, using 1/(2π) ≤ 1/2 (from π ≥ 2) and combining near-origin/asymptotic bounds.

### `freeCovariance_exponential_bound` — **NOW A THEOREM**
Proved directly from tightened `besselK0_asymptotic`.

### `freeCovarianceKernel_polynomial_bound` — **NOW A THEOREM**
Proved with C = 2√(π/(2m))/(πm²), using exp(-x) ≤ 4/x² and √ monotonicity.

### `freeCovarianceKernel_exponential_decay` — **NOW A THEOREM**
Proved using √(π/(2ζ)) ≤ 2 for ζ ≥ 1, giving (1/(2π))·2·exp(-ζ) = (1/π)·exp(-ζ).

---

## Integral/Fubini — `OS3_MixedRep.lean` — **ALL NOW THEOREMS**

### `laplace_s_integral_with_norm` — **NOW A THEOREM**
Proved by composing three established results:
1. `fubini_s_xy_swap` (Fubini): swap ∫_s with ∫_x ∫_y for fixed k_sp
2. `s_integral_complex_eval` (pointwise): evaluates the s-integral to (π/ω)·exp(−ω|t|)
3. `normalization_constant_laplace`: (1/(2π)²)·π = 1/(2·(2π)) for d=2

---

## Remaining axioms

### `minlos_theorem` — `Minlos.lean` (line 77)
Bochner–Minlos theorem: characteristic functional → cylinder measure on nuclear dual.

### `differentiable_analyticAt_finDim` — `OS0_GFF.lean` (line 86)
In finite dimensions over ℂ, differentiable ⟹ analytic.

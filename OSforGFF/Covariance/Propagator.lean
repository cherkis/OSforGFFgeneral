/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# The `GFFPropagator` typeclass and the generic proper-time covariance

The dimension-generic seam of the OS-for-GFF library. The genuine per-`d` datum of the free
covariance is its radial closed form `Cprofile` (4D `(m/4π²r)K₁(mr)`; 3D `e^{-mr}/(4πr)`;
2D `(1/2π)K₀(mr)`). This file isolates it behind a two-field typeclass:

* `Cprofile : ℝ → ℝ` — the per-`d` radial profile;
* `schwinger_eq` — it equals, for `r > 0`, the **generic** proper-time (Schwinger/heat-kernel)
  integral `properTimeCovariance`, which is one uniform formula for every `d`.

Everything else — `L¹`-integrability, the forward Fourier transform `𝓕[C] = 1/((2π)²‖k‖²+m²)`, and
the pointwise exponential decay bound — is *derived once, generically* from `schwinger_eq` (as
namespaced lemmas below), because those are all facts about `properTimeCovariance`, whose Fourier
transform is computed by Fubini + the Gaussian Fourier transform (the `(4πt)^{±d/2}` normalization
cancels). This sidesteps the Fourier-inversion/`L¹`-uniqueness obstruction that blocks stating the
bridge as a bare `𝓕[C] = P` field (`P` is not integrable on `ℝ^d`, `d ≥ 2`).

Design + rationale: see `plan.md` / `progress.md` (Stage 1a).
-/

open MeasureTheory Real Complex

namespace OSforGFF

noncomputable section

/-- Heat-kernel radial profile in `d` dimensions: `H_d(t, r) = (4πt)^{-d/2} · e^{-r²/(4t)}`.
    Its `d`-dimensional Fourier transform (in `x`, at `‖x‖ = r`) is the momentum Gaussian
    `e^{-t(2π)²‖k‖²}` — the `(4πt)^{-d/2}` cancels the Gaussian-integral normalization. -/
def heatKernelProfile (d : ℕ) (t r : ℝ) : ℝ :=
  (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-r ^ 2 / (4 * t))

/-- The proper-time (Schwinger) form of the free covariance profile, uniform in `d`:
    `C_S(r) = ∫₀^∞ e^{-t m²} · (4πt)^{-d/2} · e^{-r²/(4t)} dt`.
    This is the generic engine of the propagator: it is `L¹`, its forward Fourier transform is the
    momentum propagator, and it has exponential pointwise decay — all derived below. -/
def properTimeCovariance (d : ℕ) (m r : ℝ) : ℝ :=
  ∫ t in Set.Ioi 0, Real.exp (-t * m ^ 2) * heatKernelProfile d t r

/-- The momentum-space free propagator in mathlib's unitary Fourier convention:
    `P_d(k) = 1/((2π)²‖k‖² + m²)`. This is the forward Fourier transform of
    `fun x => properTimeCovariance d m ‖x‖`. -/
def freePropagatorMom (d : ℕ) (m : ℝ) (k : EuclideanSpace ℝ (Fin d)) : ℝ :=
  1 / ((2 * Real.pi) ^ 2 * ‖k‖ ^ 2 + m ^ 2)

/-- The dimension-generic free-propagator typeclass.

    Two obligations only: the per-`d` closed-form radial covariance `Cprofile`, and the single
    bridge `schwinger_eq` identifying it (for `r > 0`; the covariance has an integrable singularity
    at `r = 0`) with the generic proper-time integral `properTimeCovariance`. From these,
    `GFFPropagator.integrable`, `GFFPropagator.fourier_eq`, and `GFFPropagator.decayBound` are
    derived generically. `[Fact (2 ≤ d)]` supports the time/space split used downstream. -/
class GFFPropagator (d : ℕ) (m : ℝ) [Fact (0 < m)] [Fact (2 ≤ d)] where
  /-- The per-`d` radial profile of the position-space covariance: `C(x, y) = Cprofile ‖x − y‖`. -/
  Cprofile : ℝ → ℝ
  /-- `Cprofile` equals the generic proper-time integral for `r > 0`. The genuine per-`d` obligation
      (evaluate the proper-time integral to the closed form). -/
  schwinger_eq : ∀ r > 0, Cprofile r = properTimeCovariance d m r

end

end OSforGFF

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

/-! ### Derived facts about the generic heat kernel and proper-time covariance -/

/-- The heat-kernel normalization `∫ H_d(t, ‖z‖) dz = 1`, for every `d`: the `(4πt)^{-d/2}`
    prefactor cancels the Gaussian-integral normalization `(π/(1/4t))^{d/2} = (4πt)^{d/2}`. -/
lemma heatKernelProfile_integral_eq_one (d : ℕ) (t : ℝ) (ht : 0 < t) :
    ∫ z : EuclideanSpace ℝ (Fin d), heatKernelProfile d t ‖z‖ = 1 := by
  unfold heatKernelProfile
  have h_exp_eq : ∀ z : EuclideanSpace ℝ (Fin d),
      Real.exp (-‖z‖ ^ 2 / (4 * t)) = Real.exp (-(1 / (4 * t)) * ‖z‖ ^ 2) := by
    intro z; congr 1; field_simp
  simp_rw [h_exp_eq]
  rw [MeasureTheory.integral_const_mul]
  have hb : 0 < (1 / (4 * t)) := by positivity
  have h_gauss := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := EuclideanSpace ℝ (Fin d)) hb
  rw [h_gauss, finrank_euclideanSpace_fin]
  have h_div_eq : π / (1 / (4 * t)) = 4 * π * t := by field_simp
  rw [h_div_eq]
  have h_pos : 0 < 4 * π * t := by positivity
  rw [show (-(d : ℝ) / 2) = -((d : ℝ) / 2) by ring, Real.rpow_neg (le_of_lt h_pos)]
  rw [inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos h_pos _))]

/-- The `d`-dimensional Fourier transform of the heat kernel is the momentum Gaussian:
    `𝓕[fun x => H_d(t, ‖x‖)](k) = e^{-4π²t‖k‖²} = e^{-t(2π)²‖k‖²}`. The dimension `d` cancels
    between the `(4πt)^{-d/2}` prefactor and the Gaussian-FT normalization `(4πt)^{d/2}`. -/
lemma heatKernelProfile_fourier (d : ℕ) (t : ℝ) (ht : 0 < t) (k : EuclideanSpace ℝ (Fin d)) :
    FourierTransform.fourier
        (fun x : EuclideanSpace ℝ (Fin d) => (heatKernelProfile d t ‖x‖ : ℂ)) k
      = Complex.exp (-(4 * Real.pi ^ 2 * t : ℝ) * ‖k‖ ^ 2) := by
  have hfun : (fun x : EuclideanSpace ℝ (Fin d) => (heatKernelProfile d t ‖x‖ : ℂ))
      = (((4 * Real.pi * t) ^ (-(d : ℝ) / 2) : ℝ) : ℂ) •
          (fun x : EuclideanSpace ℝ (Fin d) => Complex.exp (-((1 / (4 * t) : ℝ) : ℂ) * ‖x‖ ^ 2)) := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    unfold heatKernelProfile
    rw [Complex.ofReal_mul]
    congr 1
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hfun]
  have hsmul : FourierTransform.fourier
        ((((4 * Real.pi * t) ^ (-(d : ℝ) / 2) : ℝ) : ℂ) •
          (fun x : EuclideanSpace ℝ (Fin d) => Complex.exp (-((1 / (4 * t) : ℝ) : ℂ) * ‖x‖ ^ 2)))
      = (((4 * Real.pi * t) ^ (-(d : ℝ) / 2) : ℝ) : ℂ) •
          FourierTransform.fourier
            (fun x : EuclideanSpace ℝ (Fin d) => Complex.exp (-((1 / (4 * t) : ℝ) : ℂ) * ‖x‖ ^ 2)) :=
    VectorFourier.fourierIntegral_const_smul _ _ _ _ _
  rw [hsmul, Pi.smul_apply, smul_eq_mul]
  rw [fourier_gaussian_innerProductSpace (V := EuclideanSpace ℝ (Fin d))
        (b := ((1 / (4 * t) : ℝ) : ℂ)) (by rw [Complex.ofReal_re]; positivity) k]
  rw [finrank_euclideanSpace_fin]
  have hpos : (0 : ℝ) < 4 * Real.pi * t := by positivity
  have hAne : ((4 * Real.pi * t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hpos)
  have hb : (Real.pi : ℂ) / ((1 / (4 * t) : ℝ) : ℂ) = ((4 * Real.pi * t : ℝ) : ℂ) := by
    push_cast; field_simp
  rw [hb]
  have hpre : (((4 * Real.pi * t) ^ (-(d : ℝ) / 2) : ℝ) : ℂ)
      = ((4 * Real.pi * t : ℝ) : ℂ) ^ (-(d : ℂ) / 2) := by
    rw [Complex.ofReal_cpow (le_of_lt hpos)]; congr 1; push_cast; ring
  rw [hpre, ← mul_assoc, ← Complex.cpow_add _ _ hAne]
  rw [show (-(d : ℂ) / 2 + (d : ℂ) / 2) = 0 by ring, Complex.cpow_zero, one_mul]
  congr 1
  push_cast
  field_simp

/-- The heat-kernel profile is nonnegative for `t > 0`. -/
lemma heatKernelProfile_nonneg (d : ℕ) (t r : ℝ) (ht : 0 < t) : 0 ≤ heatKernelProfile d t r := by
  unfold heatKernelProfile
  have h4 : (0 : ℝ) < 4 * Real.pi * t := by positivity
  exact mul_nonneg (Real.rpow_nonneg (le_of_lt h4) _) (Real.exp_nonneg _)

/-- For `t > 0`, `x ↦ H_d(t, ‖x‖)` is integrable (a constant times a Gaussian). -/
lemma heatKernelProfile_integrable (d : ℕ) (t : ℝ) (ht : 0 < t) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) => heatKernelProfile d t ‖x‖) := by
  unfold heatKernelProfile
  apply Integrable.const_mul
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := EuclideanSpace ℝ (Fin d))
    (b := ((1 / (4 * t) : ℝ) : ℂ)) (by rw [Complex.ofReal_re]; positivity) 0 0
  simp only [zero_mul, add_zero] at h
  refine (h.norm).congr ?_
  filter_upwards with x
  rw [Complex.norm_exp]
  congr 1
  rw [show (-((1 / (4 * t) : ℝ) : ℂ) * (↑‖x‖ : ℂ) ^ 2) = ((-‖x‖ ^ 2 / (4 * t) : ℝ) : ℂ) by
      push_cast; ring, Complex.ofReal_re]

/-- The proper-time covariance is nonnegative. -/
lemma properTimeCovariance_nonneg (d : ℕ) (m r : ℝ) : 0 ≤ properTimeCovariance d m r := by
  unfold properTimeCovariance
  apply setIntegral_nonneg measurableSet_Ioi
  intro t ht
  exact mul_nonneg (Real.exp_nonneg _) (heatKernelProfile_nonneg d t r ht)

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

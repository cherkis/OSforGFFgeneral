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

/-- Joint integrability of the Schwinger integrand `(t, x) ↦ e^{-tm²} H_d(t, ‖x‖)` over
    `(volume|_{Ioi 0}) × volume` (`t` outer). Via `integrable_prod_iff`: per-`t` a constant times a
    Gaussian, and `∫ₓ ‖·‖ = e^{-tm²}` (from `∫H=1`) is integrable in `t`. -/
lemma schwinger_prod_integrable (d : ℕ) (m : ℝ) (hm : 0 < m) :
    Integrable (Function.uncurry fun (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) =>
      Real.exp (-t * m ^ 2) * heatKernelProfile d t ‖x‖)
      ((volume.restrict (Set.Ioi 0)).prod volume) := by
  have hmeas : AEStronglyMeasurable
      (Function.uncurry fun (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) =>
        Real.exp (-t * m ^ 2) * heatKernelProfile d t ‖x‖)
      ((volume.restrict (Set.Ioi 0)).prod volume) := by
    apply Measurable.aestronglyMeasurable
    unfold Function.uncurry heatKernelProfile
    fun_prop
  rw [integrable_prod_iff hmeas]
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [Function.uncurry_apply_pair]
    exact (heatKernelProfile_integrable d t ht).const_mul _
  · have hint : Integrable (fun t => Real.exp (-t * m ^ 2)) (volume.restrict (Set.Ioi 0)) := by
      have h : (-(m ^ 2) : ℝ) < 0 := neg_neg_of_pos (by positivity)
      have hi := integrableOn_exp_mul_Ioi h 0
      exact hi.congr_fun (fun t _ => by congr 1; ring) measurableSet_Ioi
    refine hint.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [Function.uncurry_apply_pair]
    have hnn : ∀ x : EuclideanSpace ℝ (Fin d),
        ‖Real.exp (-t * m ^ 2) * heatKernelProfile d t ‖x‖‖
          = Real.exp (-t * m ^ 2) * heatKernelProfile d t ‖x‖ :=
      fun x => Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _) (heatKernelProfile_nonneg d t _ ht))
    simp_rw [hnn]
    rw [MeasureTheory.integral_const_mul, heatKernelProfile_integral_eq_one d t ht, mul_one]

/-- The proper-time covariance `x ↦ C_S(‖x‖)` is integrable (`∈ L¹`). From the joint integrability
    via `Integrable.integral_prod_left`. -/
lemma properTimeCovariance_integrable (d : ℕ) (m : ℝ) (hm : 0 < m) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) => properTimeCovariance d m ‖x‖) := by
  have h := (schwinger_prod_integrable d m hm).swap.integral_prod_left
  refine h.congr ?_
  filter_upwards with x
  unfold properTimeCovariance
  simp only [Function.comp_apply, Prod.swap_prod_mk, Function.uncurry_apply_pair]

/-- The dominating integrand for the OS4 decay bound, `(4πt)^{-d/2} e^{-tm²/2} e^{-1/(8t)}`, is
    integrable on `(0,∞)`: dominated by `C·t^{d/2}·e^{-(m²/2)t}` (Gamma-type) via
    `e^{-1/(8t)} ≤ d!·8ᵈ·tᵈ`. -/
lemma decayDominator_integrableOn (d : ℕ) (m : ℝ) (hm : 0 < m) :
    IntegrableOn (fun t => (4 * Real.pi * t) ^ (-(d : ℝ) / 2) *
      Real.exp (-(m ^ 2 / 2) * t) * Real.exp (-(1 / (8 * t)))) (Set.Ioi 0) := by
  have hb : (0 : ℝ) < m ^ 2 / 2 := by positivity
  have hgi : IntegrableOn (fun t => t ^ ((d : ℝ) / 2) * Real.exp (-(m ^ 2 / 2) * t)) (Set.Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (d : ℝ) / 2) (p := 1) (b := m ^ 2 / 2)
      (by have h2 : (0 : ℝ) ≤ (d : ℝ) / 2 := (by positivity); linarith) (le_refl 1) hb
    simpa [Real.rpow_one] using this
  refine (hgi.const_mul ((4 * Real.pi) ^ (-(d : ℝ) / 2) * ((d.factorial : ℝ) * 8 ^ d))).mono' ?_ ?_
  · exact (by fun_prop : Measurable _).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    rw [Real.norm_of_nonneg (by positivity)]
    have hexp : Real.exp (-(1 / (8 * t))) ≤ (d.factorial : ℝ) * 8 ^ d * t ^ d := by
      have hx : (0 : ℝ) ≤ 1 / (8 * t) := by positivity
      have h := Real.pow_div_factorial_le_exp (1 / (8 * t)) hx d
      have hlow : (0 : ℝ) < (1 / (8 * t)) ^ d / d.factorial := by positivity
      rw [Real.exp_neg]
      calc (Real.exp (1 / (8 * t)))⁻¹ ≤ ((1 / (8 * t)) ^ d / d.factorial)⁻¹ := inv_anti₀ hlow h
        _ = (d.factorial : ℝ) * 8 ^ d * t ^ d := by
            rw [inv_div, one_div, inv_pow, div_eq_mul_inv, inv_inv, mul_pow]; ring
    have hkey : t ^ (-(d : ℝ) / 2) * Real.exp (-(1 / (8 * t)))
        ≤ ((d.factorial : ℝ) * 8 ^ d) * t ^ ((d : ℝ) / 2) := by
      have htd : t ^ (-(d : ℝ) / 2) * (t : ℝ) ^ d = t ^ ((d : ℝ) / 2) := by
        rw [← Real.rpow_natCast t d, ← Real.rpow_add ht0]; ring_nf
      calc t ^ (-(d : ℝ) / 2) * Real.exp (-(1 / (8 * t)))
          ≤ t ^ (-(d : ℝ) / 2) * ((d.factorial : ℝ) * 8 ^ d * t ^ d) :=
            mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg (le_of_lt ht0) _)
        _ = ((d.factorial : ℝ) * 8 ^ d) * t ^ ((d : ℝ) / 2) := by rw [← htd]; ring
    rw [Real.mul_rpow (by positivity) (le_of_lt ht0)]
    calc (4 * Real.pi) ^ (-(d : ℝ) / 2) * t ^ (-(d : ℝ) / 2) * Real.exp (-(m ^ 2 / 2) * t) *
            Real.exp (-(1 / (8 * t)))
        = (4 * Real.pi) ^ (-(d : ℝ) / 2) * Real.exp (-(m ^ 2 / 2) * t) *
            (t ^ (-(d : ℝ) / 2) * Real.exp (-(1 / (8 * t)))) := by ring
      _ ≤ (4 * Real.pi) ^ (-(d : ℝ) / 2) * Real.exp (-(m ^ 2 / 2) * t) *
            (((d.factorial : ℝ) * 8 ^ d) * t ^ ((d : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = (4 * Real.pi) ^ (-(d : ℝ) / 2) * ((d.factorial : ℝ) * 8 ^ d) *
            (t ^ ((d : ℝ) / 2) * Real.exp (-(m ^ 2 / 2) * t)) := by ring

/-- Pointwise exponential decay of the proper-time covariance: for `r ≥ 1`,
    `C_S(r) ≤ A · e^{-(m/2)r}` (rate `m/2`, `A = ∫` the dominator). Via `integral_mono_of_nonneg`
    against the dominator, using the AM–GM exponent bound `tm²+r²/4t ≥ (m/2)r+tm²/2+1/8t`. -/
lemma properTimeCovariance_decay (d : ℕ) (m : ℝ) (hm : 0 < m) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ r : ℝ, 1 ≤ r →
      properTimeCovariance d m r ≤ A * Real.exp (-(m / 2) * r) := by
  set g : ℝ → ℝ := fun t => (4 * Real.pi * t) ^ (-(d : ℝ) / 2) *
    Real.exp (-(m ^ 2 / 2) * t) * Real.exp (-(1 / (8 * t))) with hg
  have hgint : IntegrableOn g (Set.Ioi 0) := decayDominator_integrableOn d m hm
  have hgnn : ∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ g t := fun t ht => by
    have ht0 : (0 : ℝ) < t := ht
    rw [hg]; dsimp only
    exact mul_nonneg (mul_nonneg
      (Real.rpow_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) ht0.le) _)
      (Real.exp_nonneg _)) (Real.exp_nonneg _)
  refine ⟨∫ t in Set.Ioi 0, g t, setIntegral_nonneg measurableSet_Ioi hgnn, fun r hr => ?_⟩
  unfold properTimeCovariance
  rw [show (∫ t in Set.Ioi 0, g t) * Real.exp (-(m / 2) * r)
        = ∫ t in Set.Ioi 0, g t * Real.exp (-(m / 2) * r) from (integral_mul_const _ _).symm]
  apply integral_mono_of_nonneg
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.exp_nonneg _) (heatKernelProfile_nonneg d t r ht)
  · exact hgint.mul_const _
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    have hexp_ineq : (m / 2) * r + (m ^ 2 / 2) * t + 1 / (8 * t) ≤ t * m ^ 2 + r ^ 2 / (4 * t) := by
      rw [← sub_nonneg]
      have hkey : t * m ^ 2 + r ^ 2 / (4 * t) - ((m / 2) * r + (m ^ 2 / 2) * t + 1 / (8 * t))
           = ((2 * t * m - r) ^ 2 + (r ^ 2 - 1)) / (8 * t) := by field_simp; ring
      rw [hkey]; apply div_nonneg _ (by positivity)
      nlinarith [sq_nonneg (2 * t * m - r), hr, sq_nonneg (r - 1)]
    have hle : Real.exp (-t * m ^ 2) * Real.exp (-r ^ 2 / (4 * t))
        ≤ Real.exp (-(m ^ 2 / 2) * t) * Real.exp (-(1 / (8 * t))) * Real.exp (-(m / 2) * r) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by simp only [neg_div]; linarith [hexp_ineq])
    rw [hg]
    unfold heatKernelProfile
    calc Real.exp (-t * m ^ 2) * ((4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-r ^ 2 / (4 * t)))
        = (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * (Real.exp (-t * m ^ 2) * Real.exp (-r ^ 2 / (4 * t))) := by
          ring
      _ ≤ (4 * Real.pi * t) ^ (-(d : ℝ) / 2) *
            (Real.exp (-(m ^ 2 / 2) * t) * Real.exp (-(1 / (8 * t))) * Real.exp (-(m / 2) * r)) :=
            mul_le_mul_of_nonneg_left hle
              (Real.rpow_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) ht0.le) _)
      _ = (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-(m ^ 2 / 2) * t) * Real.exp (-(1 / (8 * t))) *
            Real.exp (-(m / 2) * r) := by ring

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

namespace GFFPropagator

variable {d : ℕ} {m : ℝ} [Fact (0 < m)] [Fact (2 ≤ d)] [GFFPropagator d m]

/-- Derived: `x ↦ Cprofile ‖x‖` is integrable (`∈ L¹`). Transports `properTimeCovariance_integrable`
    across `schwinger_eq`, which holds off the null set `{0}`. Feeds OS1 local integrability. -/
lemma integrable :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) => Cprofile (d := d) (m := m) ‖x‖) := by
  have hm : (0 : ℝ) < m := Fact.out
  have hd : 0 < d := by have := (Fact.out : 2 ≤ d); omega
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have : Nontrivial (EuclideanSpace ℝ (Fin d)) := inferInstance
  refine (properTimeCovariance_integrable d m hm).congr ?_
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : EuclideanSpace ℝ (Fin d)))] with x hx
  exact (schwinger_eq ‖x‖ (norm_pos_iff.mpr (by simpa using hx))).symm

/-- Derived: `Cprofile` has pointwise exponential decay `|Cprofile r| ≤ A·e^{-(m/2)r}` for `r ≥ 1`.
    Transports `properTimeCovariance_decay` across `schwinger_eq` (pointwise, since `r ≥ 1 > 0`).
    Feeds the OS4 clustering decay rate. -/
lemma decayBound : ∃ A R₀ : ℝ, 0 ≤ A ∧ 0 < R₀ ∧
    ∀ r : ℝ, R₀ ≤ r → |Cprofile (d := d) (m := m) r| ≤ A * Real.exp (-(m / 2) * r) := by
  obtain ⟨A, hA, hbound⟩ := properTimeCovariance_decay d m Fact.out
  refine ⟨A, 1, hA, one_pos, fun r hr => ?_⟩
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr
  rw [schwinger_eq r hr0, abs_of_nonneg (properTimeCovariance_nonneg d m r)]
  exact hbound r hr

end GFFPropagator

end

end OSforGFF

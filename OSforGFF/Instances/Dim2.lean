/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
import OSforGFF.General.BesselK0
import OSforGFF.Covariance.Propagator
import OSforGFF.Measure.Construct

/-!
# The two-dimensional instance — proper-time evaluation

The radial profile of the free covariance in two dimensions is the modified Bessel profile
`K₀(mr)/(2π)`. This file evaluates the underlying proper-time integral in closed form: at `d = 2`
the heat-kernel prefactor is `(4πt)⁻¹`, so after pulling out the constant `(4π)⁻¹` the proper-time
integral is exactly the Schwinger integral
`∫₀^∞ (1/t) e^{-m²t - r²/(4t)} dt = 2 K₀(mr)` (`schwingerIntegral_eq_besselK0`).
-/

noncomputable section

open MeasureTheory Real Set

namespace OSforGFF

/-- The two-dimensional heat-kernel profile with the constant `(4π)⁻¹` pulled out. -/
lemma heatKernelProfile_dim2 (t r : ℝ) :
    heatKernelProfile 2 t r = (4 * Real.pi)⁻¹ * t⁻¹ * Real.exp (-r ^ 2 / (4 * t)) := by
  unfold heatKernelProfile
  rw [show (-((2 : ℕ) : ℝ) / 2) = (-1 : ℝ) by norm_num, Real.rpow_neg_one, mul_inv]

/-- The two-dimensional proper-time covariance is the Bessel-`K₀` profile:
    `properTimeCovariance 2 m r = K₀(mr)/(2π)` for `m, r > 0`. -/
theorem properTimeCovariance_dim2_eq (m r : ℝ) (hm : 0 < m) (hr : 0 < r) :
    properTimeCovariance 2 m r = 1 / (2 * Real.pi) * besselK0 (m * r) := by
  -- Pull the constant `(4π)⁻¹` out; the remaining integral is `schwingerIntegral_eq_besselK0`.
  have hconst : properTimeCovariance 2 m r =
      (4 * Real.pi)⁻¹ *
        ∫ t in Ioi 0, (1 / t) * Real.exp (-m ^ 2 * t - r ^ 2 / (4 * t)) := by
    rw [properTimeCovariance, ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [heatKernelProfile_dim2 t r,
        show -m ^ 2 * t - r ^ 2 / (4 * t) = -t * m ^ 2 + -r ^ 2 / (4 * t) by ring, Real.exp_add]
    ring
  rw [hconst, schwingerIntegral_eq_besselK0 m r hm hr]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

end OSforGFF

/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
import OSforGFF.General.LaplaceIntegral
import OSforGFF.Covariance.Propagator

/-!
# The three-dimensional (Yukawa) instance — proper-time evaluation

The radial profile of the free covariance in three dimensions is the Yukawa potential
`e^{-mr}/(4πr)`. This file evaluates the underlying proper-time integral in closed form by the
reciprocal substitution `t = 1/s`, which reduces it to the Bessel-`K_{1/2}` Laplace identity
`LaplaceIntegral.laplace_integral_half_power` (parameters `a = m²`, `b = r²/4`).
-/

noncomputable section

open MeasureTheory Real Set

namespace OSforGFF

/-- The three-dimensional proper-time integral in closed form:
    `∫₀^∞ t^{-3/2} e^{-m²t - r²/(4t)} dt = (2√π/r) e^{-mr}` for `m, r > 0`. -/
theorem schwingerIntegral_dim3 (m r : ℝ) (hm : 0 < m) (hr : 0 < r) :
    ∫ t in Ioi 0, t ^ (-(3 / 2 : ℝ)) * Real.exp (-m ^ 2 * t - r ^ 2 / (4 * t)) =
      2 * Real.sqrt Real.pi / r * Real.exp (-(m * r)) := by
  -- Reciprocal substitution `t = 1/s` (i.e. `x ↦ x^(-1)`) via `integral_comp_rpow_Ioi`.
  have hcov := integral_comp_rpow_Ioi
      (fun s : ℝ => s ^ (-(1 / 2 : ℝ)) * Real.exp (-(m ^ 2) / s - r ^ 2 / 4 * s))
      (p := -1) (by norm_num)
  -- Identify the target integrand with the substituted `K_{1/2}` integrand.
  have hint : ∫ t in Ioi 0, t ^ (-(3 / 2 : ℝ)) * Real.exp (-m ^ 2 * t - r ^ 2 / (4 * t)) =
      ∫ s in Ioi 0, s ^ (-(1 / 2 : ℝ)) * Real.exp (-(m ^ 2) / s - r ^ 2 / 4 * s) := by
    rw [← hcov]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    have hx0 : (0 : ℝ) < x := hx
    simp only [smul_eq_mul, abs_neg, abs_one, one_mul]
    rw [← mul_assoc]
    congr 1
    · rw [← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
      norm_num
    · rw [Real.rpow_neg_one]
      congr 1
      field_simp
  rw [hint, LaplaceIntegral.laplace_integral_half_power (m ^ 2) (r ^ 2 / 4)
      (by positivity) (by positivity)]
  -- Closed-form arithmetic: `√(π/(r²/4))·e^{-2√(m²·r²/4)} = (2√π/r)·e^{-mr}`.
  have hs1 : Real.sqrt (Real.pi / (r ^ 2 / 4)) = 2 * Real.sqrt Real.pi / r := by
    rw [show Real.pi / (r ^ 2 / 4) = (2 / r) ^ 2 * Real.pi by field_simp; ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    ring
  have hs2 : Real.sqrt (m ^ 2 * (r ^ 2 / 4)) = m * r / 2 := by
    rw [show m ^ 2 * (r ^ 2 / 4) = (m * r / 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  rw [hs1, hs2, show (-2 : ℝ) * (m * r / 2) = -(m * r) by ring]

/-- The three-dimensional heat-kernel profile with the constant `(4π)^{-3/2}` pulled out. -/
lemma heatKernelProfile_dim3 (t : ℝ) (ht : 0 < t) (r : ℝ) :
    heatKernelProfile 3 t r =
      (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * t ^ (-(3 / 2 : ℝ)) * Real.exp (-r ^ 2 / (4 * t)) := by
  unfold heatKernelProfile
  rw [show (-((3 : ℕ) : ℝ) / 2) = -(3 / 2 : ℝ) by norm_num, Real.mul_rpow (by positivity) ht.le]

/-- The three-dimensional proper-time covariance is the Yukawa profile:
    `properTimeCovariance 3 m r = e^{-mr}/(4πr)` for `m, r > 0`. -/
theorem properTimeCovariance_dim3_eq (m r : ℝ) (hm : 0 < m) (hr : 0 < r) :
    properTimeCovariance 3 m r = Real.exp (-(m * r)) / (4 * Real.pi * r) := by
  -- Pull the constant `(4π)^{-3/2}` out; the remaining integral is `schwingerIntegral_dim3`.
  have hconst : properTimeCovariance 3 m r =
      (4 * Real.pi) ^ (-(3 / 2 : ℝ)) *
        ∫ t in Ioi 0, t ^ (-(3 / 2 : ℝ)) * Real.exp (-m ^ 2 * t - r ^ 2 / (4 * t)) := by
    rw [properTimeCovariance, ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := ht
    rw [heatKernelProfile_dim3 t ht0 r,
        show -m ^ 2 * t - r ^ 2 / (4 * t) = -t * m ^ 2 + -r ^ 2 / (4 * t) by ring, Real.exp_add]
    ring
  rw [hconst, schwingerIntegral_dim3 m r hm hr]
  -- `(4π)^{-3/2}·(2√π/r)·e^{-mr} = e^{-mr}/(4πr)`, since `(4π)^{-3/2}·2√π = 1/(4π)`.
  have hc : (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * (2 * Real.sqrt Real.pi) = 1 / (4 * Real.pi) := by
    have hsp : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    have h32 : (4 * Real.pi) ^ (-(3 / 2 : ℝ)) = 1 / (8 * Real.pi * Real.sqrt Real.pi) := by
      rw [Real.rpow_neg (by positivity)]
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by positivity), Real.rpow_one,
          ← Real.sqrt_eq_rpow, show (4 : ℝ) * Real.pi = 2 ^ 2 * Real.pi by ring,
          Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
      ring
    rw [h32]
    field_simp
    ring
  rw [show (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * (2 * Real.sqrt Real.pi / r * Real.exp (-(m * r))) =
        (4 * Real.pi) ^ (-(3 / 2 : ℝ)) * (2 * Real.sqrt Real.pi) * (Real.exp (-(m * r)) / r) by ring,
      hc]
  ring

end OSforGFF

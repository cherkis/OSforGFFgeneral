/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
import OSforGFF.General.LaplaceIntegral

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

end OSforGFF

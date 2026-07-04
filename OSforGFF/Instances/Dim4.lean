/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
import OSforGFF.Spacetime.Basic
import OSforGFF.General.BesselK
import OSforGFF.Covariance.Propagator
import OSforGFF.Measure.Construct

/-!
# The four-dimensional instance of `GFFPropagator`

The radial profile of the free covariance in four dimensions is the Bessel closed form
`(m/(4π²r)) K₁(mr)`; its identification with the generic proper-time integral
`properTimeCovariance` is the evaluation `properTimeCovariance_dim4_eq` (the order `ν = -1` case of
the master identity `schwingerIntegral_eq_besselK1`, `General/BesselK`). At this instance the
generic kernel `freeCovariance 4 m` coincides definitionally with the Bessel kernel
`freeCovariance4 m`, defined here.
-/

noncomputable section

open MeasureTheory Real Set OSforGFF

/-- The four-dimensional proper-time covariance is the Bessel-`K₁` profile:
    `properTimeCovariance 4 m r = (m/(4π²r)) K₁(mr)` for `m, r > 0`. Pull the constant `(4π)^{-2}`
    out; the remaining integral is `schwingerIntegral_eq_besselK1`. -/
theorem properTimeCovariance_dim4_eq (m r : ℝ) (hm : 0 < m) (hr : 0 < r) :
    properTimeCovariance 4 m r = (m / (4 * Real.pi ^ 2 * r)) * besselK1 (m * r) := by
  rw [properTimeCovariance_const_mul 4 m r]
  have hre : (∫ t in Ioi 0,
        t ^ (-((4 : ℕ) : ℝ) / 2) * Real.exp (-m ^ 2 * t - r ^ 2 / (4 * t)))
      = ∫ t in Ioi 0, (1 / t ^ 2) * Real.exp (-m ^ 2 * t - r ^ 2 / (4 * t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := ht
    have hpow : t ^ (-((4 : ℕ) : ℝ) / 2) = 1 / t ^ 2 := by
      rw [show (-((4 : ℕ) : ℝ) / 2) = -(2 : ℝ) by norm_num,
          Real.rpow_neg ht0.le, Real.rpow_two, one_div]
    rw [hpow]
  rw [hre, schwingerIntegral_eq_besselK1 m r hm hr,
      show (-((4 : ℕ) : ℝ) / 2) = -(2 : ℝ) by norm_num,
      Real.rpow_neg (by positivity), Real.rpow_two]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hr' : r ≠ 0 := hr.ne'
  field_simp

/-- `2 ≤ 4`, needed for the time/space split. -/
instance instFactTwoLeFour : Fact ((2 : ℕ) ≤ 4) := ⟨by norm_num⟩

/-- `4 ≤ 5`, the bound entering the OS3 proper-time Fubini domination. -/
instance instFactFourLeFive : Fact ((4 : ℕ) ≤ 5) := ⟨by norm_num⟩

/-- The four-dimensional free propagator: `Cprofile` is the Bessel closed form and the
    Schwinger bridge is the proper-time evaluation of the heat-kernel integral. -/
noncomputable instance instGFFPropagatorDim4 (m : ℝ) [Fact (0 < m)] :
    GFFPropagator 4 m where
  Cprofile r := if r = 0 then 0 else (m / (4 * Real.pi ^ 2 * r)) * besselK1 (m * r)
  schwinger_eq r hr := by
    rw [if_neg (ne_of_gt hr), properTimeCovariance_dim4_eq m r Fact.out hr]

/-- The free covariance in position space via the Bessel representation:
    `C(x, y) = (m/(4π²|x−y|)) K₁(m|x−y|)`, regularized to `0` at coincident points. This is the
    explicit formula for the massive scalar field propagator in four dimensions. -/
noncomputable def freeCovarianceBessel (m : ℝ) (x y : SpaceTime 4) : ℝ :=
  let r := ‖x - y‖
  if r = 0 then 0
  else (m / (4 * Real.pi ^ 2 * r)) * besselK1 (m * r)

/-- The free covariance in position space (abbreviation for the Bessel representation). -/
noncomputable abbrev freeCovariance4 (m : ℝ) (x y : SpaceTime 4) : ℝ :=
  freeCovarianceBessel m x y

/-- At `d = 4` the generic kernel is definitionally the Bessel kernel. -/
lemma freeCovariance_dim4_eq (m : ℝ) [Fact (0 < m)] (x y : SpaceTime 4) :
    freeCovariance 4 m x y = freeCovariance4 m x y := rfl

/-- Shorthand for the free GFF probability measure of the four-dimensional instance. -/
@[simp] abbrev μ_GFF (m : ℝ) [Fact (0 < m)] := gaussianFreeField_free (d := 4) m

end

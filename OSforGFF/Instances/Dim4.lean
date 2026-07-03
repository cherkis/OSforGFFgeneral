/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
import OSforGFF.Instances.Dim4Bessel
import OSforGFF.Covariance.Propagator
import OSforGFF.Measure.Construct

/-!
# The four-dimensional instance of `GFFPropagator`

The radial profile of the free covariance in four dimensions is the Bessel closed form
`(m/(4π²r)) K₁(mr)`; its identification with the generic proper-time integral
`properTimeCovariance` is the Schwinger-representation evaluation
`covarianceSchwingerRep_eq_besselFormula`. At this instance the generic kernel
`freeCovariance STDimension m` coincides definitionally with the Bessel kernel
`freeCovariance4 m`.
-/

noncomputable section

open OSforGFF

/-- The four-dimensional free propagator: `Cprofile` is the Bessel closed form and the
    Schwinger bridge is the proper-time evaluation of the heat-kernel integral. -/
noncomputable instance instGFFPropagatorDim4 (m : ℝ) [Fact (0 < m)] :
    GFFPropagator STDimension m where
  Cprofile r := if r = 0 then 0 else (m / (4 * Real.pi ^ 2 * r)) * besselK1 (m * r)
  schwinger_eq r hr := by
    rw [if_neg (ne_of_gt hr), ← covarianceSchwingerRep_eq_besselFormula m r Fact.out hr]
    rfl

/-- At `d = 4` the generic kernel is definitionally the Bessel kernel. -/
lemma freeCovariance_dim4_eq (m : ℝ) [Fact (0 < m)] (x y : SpaceTime4) :
    freeCovariance STDimension m x y = freeCovariance4 m x y := rfl

/-- Shorthand for the free GFF probability measure of the four-dimensional instance. -/
@[simp] abbrev μ_GFF (m : ℝ) [Fact (0 < m)] := gaussianFreeField_free (d := STDimension) m

end

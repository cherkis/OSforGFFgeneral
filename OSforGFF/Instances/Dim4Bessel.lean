/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
import OSforGFF.Spacetime.Basic
import OSforGFF.General.BesselFunction

/-!
# The four-dimensional Bessel covariance kernel

The position-space free covariance in four dimensions is the explicit Bessel closed form
`C(x, y) = (m/(4π²r)) K₁(mr)` with `r = ‖x − y‖`. This is the sole live remnant of the original
four-dimensional Bessel/momentum development: `Instances/Dim4.lean` uses `freeCovariance4` in a
`rfl` lemma identifying it with the generic kernel `freeCovariance STDimension m`. The proper-time
evaluation of this kernel is now the order `ν = -1` case of the master identity
`schwingerIntegral_eq_besselK` (`General/BesselK`).

The full four-dimensional analytic program (the regulated-covariance / Fubini / momentum-space
development, the `K₁` analytic lemmas, the heat-kernel and Schwinger-representation defs) has been
superseded by the dimension-generic machinery and is preserved off the build graph in
`OSforGFF/Legacy/Dim4Bessel.lean` (see that file's module docstring for the supersession map).
-/

noncomputable section

open Real

/-- The free covariance in position space via the Bessel representation:
    `C(x, y) = (m/(4π²|x−y|)) K₁(m|x−y|)`, regularized to `0` at coincident points. This is the
    explicit formula for the massive scalar field propagator in four dimensions. -/
noncomputable def freeCovarianceBessel (m : ℝ) (x y : SpaceTime4) : ℝ :=
  let r := ‖x - y‖
  if r = 0 then 0
  else (m / (4 * Real.pi ^ 2 * r)) * besselK1 (m * r)

/-- The free covariance in position space (abbreviation for the Bessel representation). -/
noncomputable abbrev freeCovariance4 (m : ℝ) (x y : SpaceTime4) : ℝ :=
  freeCovarianceBessel m x y

end

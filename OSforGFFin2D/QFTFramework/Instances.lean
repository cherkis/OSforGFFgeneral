/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import OSforGFFin2D.QFTFramework
import OSforGFFin2D.Basic
import OSforGFFin2D.Euclidean
import OSforGFFin2D.DiscreteSymmetry
import OSforGFFin2D.PositiveTimeTestFunction_real
import OSforGFFin2D.TimeTranslation
import OSforGFFin2D.LatticeSpacetime

/-!
# QFTFramework Instances

This file constructs `QFTFramework` instances for the three spacetime types:

1. **Flat** `QFTFramework.flat d` — ℝ^d with Schwartz test functions (existing GFF case)
2. **Lattice** `QFTFramework.lattice d a` — aℤ^d (discrete lattice)

Each instance wires together the concrete types, operations, and instances
defined in the respective spacetime files with the abstract `QFTFramework` interface.
-/

open MeasureTheory Complex QFT
open scoped BigOperators

noncomputable section

variable {d : ℕ} [Fact (0 < d)]

/-! ## Flat ℝ^d Instance -/

/-- QFTFramework for flat Euclidean ℝ^d spacetime.

This wraps the existing OSforGFF definitions: Schwartz test functions,
tempered distributions as field configurations, Euclidean group symmetry,
and time translation via the shift operator. -/
def QFTFramework.flat (d : ℕ) [Fact (0 < d)] : QFTFramework where
  Spacetime := SpaceTime d
  TimeParam := ℝ
  TestFun := TestFunction d
  TestFunℂ := TestFunctionℂ d
  FieldConfig := FieldConfiguration d
  SymmetryGroup := @QFT.E d

  -- Test function instances (from SchwartzMap)
  instACG_TF := inferInstance
  instMod_TF := inferInstance
  instTS_TF := inferInstance
  instACG_TFℂ := inferInstance
  instMod_TFℂ := inferInstance

  -- Field configuration instances (from WeakDual)
  instMS_FC := inferInstance
  instTS_FC := inferInstance

  -- Spacetime instances
  instPMS_ST := inferInstance
  instInh_ST := ⟨0⟩

  -- Symmetry group (Euclidean group E(d))
  instGrp_SG := inferInstance

  -- Time parameter (ℝ with standard order and topology)
  instLO_TP := inferInstance
  instTS_TP := inferInstance
  instOT_TP := inferInstance

  -- Generating functionals
  realGenFunctional := GJGeneratingFunctional
  complexGenFunctional := GJGeneratingFunctionalℂ

  -- Symmetry action (Euclidean pullback on complex test functions)
  symmetryAction := QFT.euclidean_action

  -- Time reflection (from DiscreteSymmetry.lean)
  timeReflectionReal := compTimeReflectionReal
  positiveTimeSubmodule := PositiveTimeTestFunctions.submodule

  -- Clustering and ergodicity operations
  translateTestFun := fun a f => f.translate a
  complexPairing := distributionPairingℂ_real
  timeTranslationDist := TimeTranslation.timeTranslationDistribution

/-! ## Lattice aℤ^d Instance -/

/-- QFTFramework for the lattice spacetime aℤ^d.

All types and operations are concrete (no axioms, except for the Group instance
on the lattice symmetry group). The lattice spacing `a` enters via the
PseudoMetricSpace (inherited from the embedding into ℝ^d) and is used
to weight distribution pairings. -/
def QFTFramework.lattice (d : ℕ) (a : ℝ) [Fact (0 < d)] [Fact (0 < a)] :
    QFTFramework where
  Spacetime := SpaceTimeLattice d
  TimeParam := ℤ
  TestFun := TestFunctionLattice d
  TestFunℂ := TestFunctionLatticeℂ d
  FieldConfig := FieldConfigurationLattice d
  SymmetryGroup := LatticeSymmetryGroup d

  -- Test function instances (Pi type — automatic)
  instACG_TF := inferInstance
  instMod_TF := inferInstance
  instTS_TF := inferInstance
  instACG_TFℂ := inferInstance
  instMod_TFℂ := inferInstance

  -- Field configuration instances
  instMS_FC := inferInstance
  instTS_FC := inferInstance

  -- Spacetime instances (lattice metric from embedding)
  instPMS_ST := latticePseudoMetric d a
  instInh_ST := inferInstance

  -- Symmetry group (axiomatized Group)
  instGrp_SG := inferInstance

  -- Time parameter (ℤ with standard order and topology)
  instLO_TP := inferInstance
  instTS_TP := inferInstance
  instOT_TP := inferInstance

  -- Generating functionals (lattice sums)
  realGenFunctional := fun dμ f =>
    ∫ φ, exp (I * (latticeDistributionPairing φ f : ℂ)) ∂dμ.toMeasure
  complexGenFunctional := fun dμ f =>
    ∫ φ, exp (I * latticeDistributionPairingℂ φ f) ∂dμ.toMeasure

  -- Symmetry action (concrete pullback)
  symmetryAction := latticeSymmetryActionℂ

  -- Time reflection and positive time (concrete)
  timeReflectionReal := latticeTimeReflectionCLM
  positiveTimeSubmodule := latticePositiveTimeSubmodule

  -- Clustering and ergodicity operations (concrete)
  translateTestFun := latticeTranslateTestFun
  complexPairing := latticeDistributionPairingℂ
  timeTranslationDist := latticeTimeTranslation

end

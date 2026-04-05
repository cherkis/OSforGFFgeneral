/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.Topology.Order.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# QFT Framework — Abstract Interface

This file defines a bundled `QFTFramework` structure that abstracts over different
spacetime types, enabling the Osterwalder-Schrader axioms to be stated generically.

## Supported spacetime types

1. **Flat** ℝ^d — the existing Gaussian Free Field case
2. **Cylinder** ℝ × T^{d-1}_L — for P(Φ)₂ on ℝ × S¹
3. **Lattice** aℤ^d — discrete lattice with spacing a > 0

## Design choices

- `TimeParam` is ℝ for continuum theories and ℤ for lattice. OS4 ergodicity
  uses `Filter.atTop` on `TimeParam`, which works for both.
- `PseudoMetricSpace` on `Spacetime` supports the torus (compact, not normed)
  and lattice (discrete metric scaled by `a`).
- `LinearOrder` + `OrderTopology` on `TimeParam` suffice for `Filter.atTop`
  and time-ordering.

## References

* Glimm and Jaffe, *Quantum Physics*, Ch. 6
* Osterwalder and Schrader, *Axiom positivity and the Osterwalder-Schrader axioms*
-/

open MeasureTheory Complex
open scoped BigOperators

/-- A bundled framework for Euclidean quantum field theory.

This packages all the data and type-class assumptions needed to state the
Osterwalder-Schrader axioms over an arbitrary spacetime. -/
structure QFTFramework where
  /-- The spacetime manifold (ℝ^d, ℝ × T^{d-1}, ℤ^d, etc.) -/
  Spacetime : Type
  /-- The time parameter type: ℝ for continuum, ℤ for lattice -/
  TimeParam : Type
  /-- Real-valued test functions -/
  TestFun : Type
  /-- Complex-valued test functions -/
  TestFunℂ : Type
  /-- Field configurations (distributions, lattice fields, etc.) -/
  FieldConfig : Type
  /-- The symmetry group (Euclidean, translation, hypercubic, etc.) -/
  SymmetryGroup : Type

  -- Required instances on test functions
  [instACG_TF : AddCommGroup TestFun]
  [instMod_TF : Module ℝ TestFun]
  [instTS_TF : TopologicalSpace TestFun]
  [instACG_TFℂ : AddCommGroup TestFunℂ]
  [instMod_TFℂ : Module ℂ TestFunℂ]

  -- Required instances on field configurations
  [instMS_FC : MeasurableSpace FieldConfig]
  [instTS_FC : TopologicalSpace FieldConfig]

  -- Spacetime geometry
  [instPMS_ST : PseudoMetricSpace Spacetime]
  [instInh_ST : Inhabited Spacetime]

  -- Symmetry group structure
  [instGrp_SG : Group SymmetryGroup]

  -- Time parameter structure
  [instLO_TP : LinearOrder TimeParam]
  [instTS_TP : TopologicalSpace TimeParam]
  [instOT_TP : OrderTopology TimeParam]

  -- Generating functionals (OS0, OS1)
  /-- Real generating functional Z[J] = ∫ exp(i⟨ω, J⟩) dμ(ω) -/
  realGenFunctional : ProbabilityMeasure FieldConfig → TestFun → ℂ
  /-- Complex generating functional for analyticity -/
  complexGenFunctional : ProbabilityMeasure FieldConfig → TestFunℂ → ℂ

  -- OS2: Symmetry invariance
  /-- Action of the symmetry group on complex test functions -/
  symmetryAction : SymmetryGroup → TestFunℂ → TestFunℂ

  -- OS3: Reflection positivity
  /-- Time reflection operator on real test functions -/
  timeReflectionReal : TestFun →L[ℝ] TestFun
  /-- Submodule of real test functions supported at positive time -/
  positiveTimeSubmodule : Submodule ℝ TestFun

  -- OS4: Clustering and ergodicity
  /-- Spatial translation of test functions -/
  translateTestFun : Spacetime → TestFun → TestFun
  /-- Complex pairing ⟨ω, f⟩_ℂ for field configurations with complex test functions -/
  complexPairing : FieldConfig → TestFunℂ → ℂ
  /-- Time translation acting on field configurations -/
  timeTranslationDist : TimeParam → FieldConfig → FieldConfig

namespace QFTFramework

-- Make instances available when working with a framework
attribute [instance] instACG_TF instMod_TF instTS_TF instACG_TFℂ instMod_TFℂ
attribute [instance] instMS_FC instTS_FC instPMS_ST instInh_ST instGrp_SG
attribute [instance] instLO_TP instTS_TP instOT_TP

end QFTFramework

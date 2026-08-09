/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Copyright (c) 2026 Sergey A. Cherkis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
import OSforGFF.Spacetime.Basic
import OSforGFF.Spacetime.DiscreteSymmetry
import OSforGFF.Spacetime.Euclidean
import OSforGFF.Spacetime.PositiveTimeTestFunction

/-!
# LEGACY — unused spacetime-layer declarations (off the build graph)

**Status: legacy.** Proven declarations from the spacetime layer that no declaration on the
build graph consumes. Preserved here with full proofs; **not on the root import graph**.
Verify in isolation with

    lake env lean OSforGFF/Legacy/UnusedSpacetime.lean

Declarations keep their original namespaces; each block re-declares the `open`/`variable`
context of its source file.

## Supersession map

From `Spacetime/Basic.lean`:
- `schwartzMul` — pointwise multiplication lifted to the Schwartz space; the library's
  multiplication needs are served by `pointwiseMulCLM` (which stays on-graph) directly.
- `SpatialL2` — L² space on spatial slices; the OS constructions work with `Lp` types
  spelled out explicitly.

From `Spacetime/DiscreteSymmetry.lean` (the matrix presentation of time reflection —
the library uses the linear-map presentation `timeReflection`/`timeReflectionCLM` and
`QFT.timeReflectionLE` instead):
- `timeReflectionMatrix`, `timeReflectionMatrix_is_orthogonal`, `timeReflectionIsometry` —
  a closed cluster: the matrix, its orthogonality, and its packaging as an element of the
  orthogonal group.

From `Spacetime/Euclidean.lean`:
- `euclidean_actions_unified` — the statement that the test-function and L² Euclidean
  actions are both instances of one abstract pattern; the OS2 proof uses
  `euclidean_action_CLM` and `euclidean_action_L2` separately.

From `Spacetime/PositiveTimeTestFunction.lean`:
- `is_open_positiveTimeSet` — openness of the positive-time region; the positive-time
  submodule is defined via `tsupport` inclusion and never needs openness.
-/

/-! ### From `Spacetime/Basic.lean` -/

section SpacetimeBasic

open MeasureTheory NNReal ENNReal Complex
open TopologicalSpace Measure
open DFunLike (coe)

noncomputable section

variable {d : ℕ}

/-- Multiplication lifted to the Schwartz space. -/
def schwartzMul (g : (TestFunctionℂ d)) : (TestFunctionℂ d) →L[ℂ] (TestFunctionℂ d) :=
  (SchwartzMap.bilinLeftCLM pointwiseMulCLM (SchwartzMap.hasTemperateGrowth_general g))

/-- L² space on spatial slices (real-valued) -/
abbrev SpatialL2 (d : ℕ) := Lp ℝ 2 (volume : Measure (SpatialCoords d))

end

end SpacetimeBasic

/-! ### From `Spacetime/DiscreteSymmetry.lean` -/

section DiscreteSymmetry

open MeasureTheory

namespace QFT

variable {d : ℕ} [Fact (2 ≤ d)]

def timeReflectionMatrix : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.diagonal (fun i => if i = 0 then -1 else 1)

lemma timeReflectionMatrix_is_orthogonal :
   timeReflectionMatrix ∈ Matrix.orthogonalGroup (Fin d) ℝ := by
      simp [Matrix.mem_orthogonalGroup_iff, timeReflectionMatrix, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
      ext i j
      simp [Matrix.one_apply]
      split_ifs <;> norm_num

def timeReflectionIsometry  : Matrix.orthogonalGroup (Fin d) ℝ :=
  ⟨timeReflectionMatrix, timeReflectionMatrix_is_orthogonal⟩

end QFT

end DiscreteSymmetry

/-! ### From `Spacetime/Euclidean.lean` -/

section Euclidean

open MeasureTheory NNReal ENNReal
open TopologicalSpace Measure
open scoped Real InnerProductSpace SchwartzMap

noncomputable section

namespace QFT

variable {d : ℕ}

/-- Both actions are instances of the same abstract pattern. -/
lemma euclidean_actions_unified (g : (E d)) :
    (∃ (T_test : (TestFunctionℂ d) →L[ℂ] (TestFunctionℂ d)),
       ∀ f, euclidean_action g f = T_test f) ∧
    (∃ (T_L2 : Lp ℂ 2 (volume : Measure (SpaceTime d)) → Lp ℂ 2 (volume : Measure (SpaceTime d))),
       ∀ f, euclidean_action_L2 g f = T_L2 f) := by
  constructor
  · use euclidean_action_CLM g
    intro f
    rfl  -- by definition of euclidean_action
  · use euclidean_action_L2 g
    intro f
    rfl  -- by definition of euclidean_action_L2

end QFT

end

end Euclidean

/-! ### From `Spacetime/PositiveTimeTestFunction.lean` -/

section PositiveTimeTestFunction

open TopologicalSpace Function SchwartzMap QFT

noncomputable section

variable {d : ℕ} [Fact (2 ≤ d)]

/-- The positive time set is open -/
lemma is_open_positiveTimeSet : IsOpen (positiveTimeSet (d := d)) :=
  isOpen_lt continuous_const
    (PiLp.continuous_apply 2 (fun _ => ℝ) (⟨0, by have h : 2 ≤ d := Fact.out; omega⟩ : Fin d))

end

end PositiveTimeTestFunction

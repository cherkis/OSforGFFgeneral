/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Copyright (c) 2026 Sergey A. Cherkis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

import OSforGFF.Spacetime.Basic
import OSforGFF.OS.Axioms
import OSforGFF.Measure.Construct
import OSforGFF.Measure.IsGaussian
import OSforGFF.Spacetime.Euclidean
import OSforGFF.Spacetime.DiscreteSymmetry
import OSforGFF.General.FunctionalAnalysis
import OSforGFF.Measure.Minlos
import OSforGFF.Measure.MinlosAnalytic
import OSforGFF.Schwinger.Defs

/-!
# Gaussian Free Field Assembly

Defines gaussianFreeField_free (d := d) m as a ProbabilityMeasure and proves two OS axioms for general Gaussian measures:

- OS0 (alternative via quadratic form): Z[∑ᵢ zᵢJᵢ] = exp(−½ ∑ᵢⱼ zᵢzⱼ⟨Jᵢ,CJⱼ⟩) is entire
  (the primary OS0 proof via Hartogs is in `OS.OS0_Analyticity`)
- OS2 (Euclidean invariance): Z[gf] = Z[f] when covariance is E(d)-invariant
-/

open MeasureTheory Complex
open TopologicalSpace SchwartzMap

noncomputable section

variable {d : ℕ} [Fact (2 ≤ d)]

open scoped BigOperators
open Finset

/-! ## OS2: Euclidean Invariance for Translation-Invariant Gaussian Measures

Euclidean invariance follows if the covariance operator commutes with Euclidean transformations.
For translation-invariant measures, this is equivalent to the covariance depending only on
differences of spacetime points.
-/

/-- Assumption: The covariance is invariant under Euclidean transformations -/
def CovarianceEuclideanInvariant (dμ_config : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∀ (g : QFT.E d) (f h : SchwartzTestFunction d),
    SchwingerFunction₂ dμ_config (QFT.euclidean_action_real g f) (QFT.euclidean_action_real g h) =
    SchwingerFunction₂ dμ_config f h

/-- Assumption: The complex covariance is invariant under Euclidean transformations -/
def CovarianceEuclideanInvariantℂ (dμ_config : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∀ (g : QFT.E d) (f h : SchwartzTestFunctionℂ d),
    SchwingerFunctionℂ₂ dμ_config (QFT.euclidean_action g f) (QFT.euclidean_action g h) =
    SchwingerFunctionℂ₂ dμ_config f h

omit [Fact (2 ≤ d)] in
theorem gaussian_satisfies_OS2
  (dμ_config : ProbabilityMeasure (FieldConfiguration d))
  (h_gaussian : isGaussianGJ dμ_config)
  (h_euclidean_invariant : CovarianceEuclideanInvariantℂ dμ_config)
  : OS2_EuclideanInvariance dμ_config := by
  -- For Gaussian measures: Z[f] = exp(-½⟨f, Cf⟩)
  -- If C commutes with Euclidean transformations g, then:
  -- Z[gf] = exp(-½⟨gf, C(gf)⟩) = exp(-½⟨f, Cf⟩) = Z[f]
  intro g f

  -- Extract Gaussian form for both Z[f] and Z[gf]
  have h_form := h_gaussian.2

  -- Apply Gaussian form to both sides
  rw [h_form f, h_form (QFT.euclidean_action g f)]

  -- Show the exponents are equal: ⟨gf, C(gf)⟩ = ⟨f, Cf⟩
  -- This follows directly from Euclidean invariance of the complex covariance
  congr 2
  -- Use Euclidean invariance directly (symmetric form)
  exact (h_euclidean_invariant g f f).symm

/-! ## Implementation Strategy

To complete these proofs, we need to:

1. **Complete the Glimm-Jaffe reflection positivity argument:**
   - Time reflection properly implemented using `QFT.compTimeReflection` from DiscreteSymmetry ✓
   - Implement `covarianceOperator` as the Riesz representation of the 2-point function
   - Complete the proof of `glimm_jaffe_exponent_reflection_positive`
   - Show that the 4-term expansion in the exponent has non-negative real part

3. **Prove key lemmas:**
   - Schwartz map composition with smooth transformations
   - Properties of the bilinear form `distributionPairingℂ_real`
   - Continuity and analyticity of exponential functionals

4. **Mathematical insights implemented:**
   - **OS0**: Polynomial → exponential → entire function ✓
   - **OS1**: Positive semidefinite covariance → bounded generating functional ✓
   - **OS2**: Covariance commutes with transformations → generating functional invariant ✓
   - **OS3**: Reflection positivity framework following Glimm-Jaffe Theorem 6.2.2 ✓ (structure)
   - **OS4**: Covariance decay → correlation decay ✓

5. **Glimm-Jaffe Theorem 6.2.2 Implementation:**
   - Defined the key expansion: `glimm_jaffe_exponent` captures ⟨F̄ - CF', C(F̄ - CF')⟩
   - Structured the proof around the exponential form Z[F̄ - CF'] = exp(-½⟨F̄ - CF', C(F̄ - CF')⟩)
   - The reflection positivity condition ensures Re⟨F̄ - CF', C(F̄ - CF')⟩ ≥ 0
   - This gives |Z[F̄ - CF']| ≤ 1, which is the heart of reflection positivity

6. **Connection to existing GFF work:**
   - Use results from `GFF.lean` and `GFF2.lean` where applicable
   - Translate L2-based proofs to distribution framework
   - Leverage the explicit Gaussian form of the generating functional

Note: The main theorem `gaussian_satisfies_all_GJ_OS_axioms` shows that Gaussian measures
satisfy all the OS axioms under appropriate assumptions on the covariance. The Glimm-Jaffe
approach for OS3 provides the mathematical foundation for reflection positivity in the
Gaussian Free Field context.
-/



/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import OSforGFFin2D.QFTFramework

/-!
# Generic Osterwalder-Schrader Axioms

This file restates the Osterwalder-Schrader axioms (OS0–OS4) parametrized over
a `QFTFramework`, so that the same axiom definitions apply to flat ℝ^d,
cylinder ℝ × T^{d-1}_L, and lattice aℤ^d spacetimes.

The concrete axioms in `OS_Axioms.lean` remain unchanged and are specific to
the flat ℝ^d case with Schwartz test functions.

## Main Definitions

* `OS0_Analyticity_generic` — Analyticity of the generating functional
* `OS1_Regularity_generic` — Exponential regularity bound
* `OS2_Invariance_generic` — Symmetry group invariance
* `OS3_ReflectionPositivity_generic` — Reflection positivity
* `OS4_Clustering_generic` — Clustering (correlation decay)
* `OS4_Ergodicity_generic` — Ergodicity (time-average convergence)
* `SatisfiesAllOS_generic` — Bundle of all axioms
-/

open MeasureTheory Complex Filter
open scoped BigOperators

noncomputable section

variable (F : QFTFramework)

/-! ## OS-0: Analyticity -/

/-- OS0 (Analyticity): The complex generating functional is analytic in the
    test function coefficients.

    For any finite collection of complex test functions J₁, …, Jₙ, the map
    (z₁, …, zₙ) ↦ Z_ℂ[∑ᵢ zᵢ Jᵢ] is analytic on ℂⁿ. -/
def OS0_Analyticity_generic (dμ : ProbabilityMeasure F.FieldConfig) : Prop :=
  ∀ (n : ℕ) (J : Fin n → F.TestFunℂ),
    AnalyticOn ℂ (fun z : Fin n → ℂ =>
      F.complexGenFunctional dμ (∑ i, z i • J i)) Set.univ

/-! ## OS-1: Regularity -/

/-- OS1 (Regularity): The complex generating functional satisfies an exponential
    bound controlled by a seminorm-like functional `N` on complex test functions.

    ‖Z_ℂ[f]‖ ≤ exp(c · N(f)) for some positive constant c and some
    framework-provided functional N. -/
def OS1_Regularity_generic (dμ : ProbabilityMeasure F.FieldConfig) : Prop :=
  ∃ (c : ℝ) (N : F.TestFunℂ → ℝ), c > 0 ∧
    ∀ (f : F.TestFunℂ), ‖F.complexGenFunctional dμ f‖ ≤ Real.exp (c * N f)

/-! ## OS-2: Symmetry Invariance -/

/-- OS2 (Symmetry Invariance): The generating functional is invariant under
    the symmetry group of the framework.

    Z_ℂ[f] = Z_ℂ[g · f] for all g in the symmetry group. -/
def OS2_Invariance_generic (dμ : ProbabilityMeasure F.FieldConfig) : Prop :=
  ∀ (g : F.SymmetryGroup) (f : F.TestFunℂ),
    F.complexGenFunctional dμ f =
    F.complexGenFunctional dμ (F.symmetryAction g f)

/-! ## OS-3: Reflection Positivity -/

/-- OS3 (Reflection Positivity): For any finite collection of positive-time
    test functions fᵢ and real coefficients cᵢ, the reflection matrix is
    positive semidefinite:

    ∑ᵢ ∑ⱼ cᵢ cⱼ Z[fᵢ - Θ fⱼ] ≥ 0

    where Θ is the time reflection operator. -/
def OS3_ReflectionPositivity_generic (dμ : ProbabilityMeasure F.FieldConfig) : Prop :=
  ∀ (n : ℕ) (f : Fin n → F.positiveTimeSubmodule) (c : Fin n → ℝ),
    0 ≤ ∑ i, ∑ j, c i * c j *
      (F.realGenFunctional dμ
        ((f i).val - F.timeReflectionReal ((f j).val))).re

/-! ## OS-4: Clustering and Ergodicity -/

/-- OS4 Clustering: Correlations between spatially separated regions decay.

    For all test functions f, g and ε > 0, there exists R > 0 such that
    for all spacetime translations a with dist(a, 0) > R:
    ‖Z[f + T_a g] − Z[f] · Z[g]‖ < ε -/
def OS4_Clustering_generic (dμ : ProbabilityMeasure F.FieldConfig) : Prop :=
  ∀ (f g : F.TestFun) (ε : ℝ), ε > 0 →
    ∃ (R : ℝ), R > 0 ∧ ∀ (a : F.Spacetime),
      @dist F.Spacetime F.instPMS_ST.toDist a default > R →
        ‖F.realGenFunctional dμ (f + F.translateTestFun a g) -
         F.realGenFunctional dμ f * F.realGenFunctional dμ g‖ < ε

/-- OS4 Ergodicity: Time averages of observables converge to expectations.

    For generating functions A(ω) = ∑ⱼ zⱼ exp(⟨ω, fⱼ⟩_ℂ), the time-averaged
    observable converges in L²(μ):

    lim_{T → ∞} 𝔼_μ[‖(1/T) ∫₀ᵀ A(T_s ω) ds − 𝔼_μ[A]‖²] = 0

    Uses `Filter.atTop` on `F.TimeParam`, which works for both ℝ (continuum)
    and ℤ (lattice) time parameters. -/
def OS4_Ergodicity_generic (dμ : ProbabilityMeasure F.FieldConfig) : Prop :=
  ∀ (n : ℕ) (z : Fin n → ℂ) (f : Fin n → F.TestFunℂ),
    let μ_meas := dμ.toMeasure
    let A : F.FieldConfig → ℂ := fun ω =>
      ∑ j, z j * exp (F.complexPairing ω (f j))
    Tendsto
      (fun T : F.TimeParam =>
        ∫ ω, ‖A (F.timeTranslationDist T ω)
              - ∫ ω', A ω' ∂μ_meas‖^2 ∂μ_meas)
      atTop
      (nhds 0)

/-! ## Bundled Axiom Conjunction -/

/-- A probability measure on field configurations satisfies all generic
    Osterwalder-Schrader axioms. This bundles OS0–OS4 into a single predicate,
    parametrized over a `QFTFramework`. -/
structure SatisfiesAllOS_generic (dμ : ProbabilityMeasure F.FieldConfig) : Prop where
  os0 : OS0_Analyticity_generic F dμ
  os1 : OS1_Regularity_generic F dμ
  os2 : OS2_Invariance_generic F dμ
  os3 : OS3_ReflectionPositivity_generic F dμ
  os4_clustering : OS4_Clustering_generic F dμ
  os4_ergodicity : OS4_Ergodicity_generic F dμ

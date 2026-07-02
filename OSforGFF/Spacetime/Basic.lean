/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.RCLike.Extend
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Algebra.Module.WeakDual

import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.GroupAction.Basic

-- Import our functional analysis utilities
import OSforGFF.General.FunctionalAnalysis
-- Bochner library provides the cylinder σ-algebra MeasurableSpace instance on WeakDual
import Minlos.NuclearSpace

/-!
# Basic Definitions

Core type definitions for the formalization:

- `SpaceTime4` = EuclideanSpace ℝ (Fin 4), the Euclidean 4-space ℝ⁴
- `TestFunction4` / `TestFunctionℂ4` = real/complex Schwartz functions on ℝ⁴
- `FieldConfiguration4` = tempered distributions S'(ℝ⁴) (WeakDual of Schwartz space)
- `distributionPairing` / `distributionPairingℂ_real` = ⟨ω, f⟩ pairings
- `GJGeneratingFunctional` = Z[J] = ∫ exp(i⟨ω, J⟩) dμ(ω)
-/

/-- Euclidean spacetime of dimension `d`: `ℝ^d` with the Euclidean inner-product structure. -/
abbrev SpaceTime (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The spacetime dimension of the concrete four-dimensional instance. -/
abbrev STDimension := 4

/-- Four-dimensional Euclidean spacetime, `SpaceTime STDimension`. -/
abbrev SpaceTime4 := SpaceTime STDimension

instance : Fact (2 ≤ STDimension) := ⟨by norm_num⟩

noncomputable instance (d : ℕ) : InnerProductSpace ℝ (SpaceTime d) := by infer_instance

/-- The time component `x₀` of a spacetime point (the time/space split needs `d ≥ 2`). -/
abbrev getTimeComponent {d : ℕ} [Fact (2 ≤ d)] (x : SpaceTime d) : ℝ :=
  x ⟨0, by have h : 2 ≤ d := Fact.out; omega⟩

open MeasureTheory NNReal ENNReal Complex
open TopologicalSpace Measure

-- Also open FunLike for SchwartzMap function application
open DFunLike (coe)

noncomputable section

variable {𝕜 : Type} [RCLike 𝕜]

abbrev μ : Measure SpaceTime4 := volume    -- Lebesgue, just named “μ”

/- Distributions and test functions -/

abbrev TestFunction (d : ℕ) : Type := SchwartzMap (SpaceTime d) ℝ
abbrev TestFunction𝕜 (d : ℕ) : Type := SchwartzMap (SpaceTime d) 𝕜
abbrev TestFunctionℂ (d : ℕ) := TestFunction𝕜 (𝕜 := ℂ) d

abbrev TestFunction4 : Type := TestFunction STDimension
abbrev TestFunctionℂ4 := TestFunctionℂ STDimension

example : AddCommGroup TestFunctionℂ4 := by infer_instance
example : Module ℂ TestFunctionℂ4 := by infer_instance

/- Space-time and test function setup -/

variable (x : SpaceTime4)

/- Probability distribution over field configurations (distributions) -/
def pointwiseMulCLM : ℂ →L[ℂ] ℂ →L[ℂ] ℂ := ContinuousLinearMap.mul ℂ ℂ

/-- Multiplication lifted to the Schwartz space. -/
def schwartzMul (g : TestFunctionℂ4) : TestFunctionℂ4 →L[ℂ] TestFunctionℂ4 :=
  (SchwartzMap.bilinLeftCLM pointwiseMulCLM (SchwartzMap.hasTemperateGrowth_general g))



/-! ## Glimm-Jaffe Distribution Framework

The proper mathematical foundation for quantum field theory uses
tempered distributions as field configurations, following Glimm and Jaffe.
This section adds the distribution-theoretic definitions alongside
the existing L2 framework for comparison and gradual transition.
-/

/-- Field configurations as tempered distributions (dual to Schwartz space).
    This follows the Glimm-Jaffe approach where the field measure is supported
    on the space of distributions, not L2 functions.

    Using WeakDual gives the correct weak-* topology on the dual space. -/
abbrev FieldConfiguration (d : ℕ) := WeakDual ℝ (SchwartzMap (SpaceTime d) ℝ)

/-- Field configurations over four-dimensional spacetime, `FieldConfiguration STDimension`. -/
abbrev FieldConfiguration4 := FieldConfiguration STDimension

-- MeasurableSpace on FieldConfiguration4 = WeakDual ℝ TestFunction4 is the cylinder σ-algebra
-- provided by the bochner library: ⨆ f, (borel ℝ).comap (eval f)

/-- The fundamental pairing between a field configuration (distribution) and a test function.
    This is ⟨ω, f⟩ in the Glimm-Jaffe notation.

    Note: FieldConfiguration4 = WeakDual ℝ (SchwartzMap SpaceTime4 ℝ) has the correct
    weak-* topology, making evaluation maps x ↦ ω(x) continuous for each test function x. -/
def distributionPairing (ω : FieldConfiguration4) (f : TestFunction4) : ℝ := ω f

@[simp] lemma distributionPairing_add (ω₁ ω₂ : FieldConfiguration4) (a : TestFunction4) :
    distributionPairing (ω₁ + ω₂) a = distributionPairing ω₁ a + distributionPairing ω₂ a := rfl

@[simp] lemma distributionPairing_smul (s : ℝ) (ω : FieldConfiguration4) (a : TestFunction4) :
    distributionPairing (s • ω) a = s * distributionPairing ω a :=
  -- This follows from the definition of scalar multiplication in WeakDual
  rfl

@[simp] lemma pairing_smul_real (ω : FieldConfiguration4) (s : ℝ) (a : TestFunction4) :
  ω (s • a) = s * (ω a) :=
  -- This follows from the linearity of the dual pairing
  map_smul ω s a

@[simp] def distributionPairingCLM (a : TestFunction4) : FieldConfiguration4 →L[ℝ] ℝ where
  toFun ω := distributionPairing ω a
  map_add' ω₁ ω₂ := by
    -- WeakDual addition is pointwise: (ω₁ + ω₂) a = ω₁ a + ω₂ a
    rfl
  map_smul' s ω := by
    -- WeakDual scalar multiplication is pointwise: (s • ω) a = s * (ω a)
    rfl
  cont := by
    -- The evaluation map is continuous by definition of WeakDual topology
    exact WeakDual.eval_continuous a

@[simp] lemma distributionPairingCLM_apply (a : TestFunction4) (ω : FieldConfiguration4) :
    distributionPairingCLM a ω = distributionPairing ω a := rfl

variable [SigmaFinite μ]

/-! ## Glimm-Jaffe Generating Functional

The generating functional in the distribution framework:
Z[J] = ∫ exp(i⟨ω, J⟩) dμ(ω)
where the integral is over field configurations ω (distributions).
-/

/-- The Glimm-Jaffe generating functional: Z[J] = ∫ exp(i⟨ω, J⟩) dμ(ω)
    This is the fundamental object in constructive QFT. -/
def GJGeneratingFunctional (dμ_config : ProbabilityMeasure FieldConfiguration4)
  (J : TestFunction4) : ℂ :=
  ∫ ω, Complex.exp (Complex.I * (distributionPairing ω J : ℂ)) ∂dμ_config.toMeasure

/-- Helper function to create a Schwartz map from a complex test function by applying a continuous linear map.
    This factors out the common pattern for extracting real/imaginary parts. -/
def schwartz_comp_clm (f : TestFunctionℂ4) (L : ℂ →L[ℝ] ℝ) : TestFunction4 :=
  SchwartzMap.mk (fun x => L (f x)) (by
    -- L is a continuous linear map, hence smooth
    exact ContDiff.comp L.contDiff f.smooth'
  ) (by
    -- Polynomial growth: since |L(z)| ≤ ||L|| * |z|, derivatives are controlled
    intro k n
    obtain ⟨C, hC⟩ := f.decay' k n
    use C * ‖L‖
    intro x
    -- The function (fun x => L (f x)) equals (L ∘ f.toFun)
    have h_eq : (fun y => L (f y)) = L ∘ f.toFun := rfl
    -- Key: iteratedFDeriv of L ∘ f equals L.compContinuousMultilinearMap (iteratedFDeriv f)
    have h_deriv : iteratedFDeriv ℝ n (L ∘ f.toFun) x =
        L.compContinuousMultilinearMap (iteratedFDeriv ℝ n f.toFun x) :=
      ContinuousLinearMap.iteratedFDeriv_comp_left L f.smooth'.contDiffAt (WithTop.coe_le_coe.mpr le_top)
    rw [h_eq, h_deriv]
    -- Use the norm bound: ‖L.compContinuousMultilinearMap m‖ ≤ ‖L‖ * ‖m‖
    calc ‖x‖ ^ k * ‖L.compContinuousMultilinearMap (iteratedFDeriv ℝ n f.toFun x)‖
        ≤ ‖x‖ ^ k * (‖L‖ * ‖iteratedFDeriv ℝ n f.toFun x‖) := by
          apply mul_le_mul_of_nonneg_left
          exact ContinuousLinearMap.norm_compContinuousMultilinearMap_le L _
          exact pow_nonneg (norm_nonneg _) _
      _ = ‖L‖ * (‖x‖ ^ k * ‖iteratedFDeriv ℝ n f.toFun x‖) := by ring
      _ ≤ ‖L‖ * C := by
          apply mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)
      _ = C * ‖L‖ := by ring
  )

omit [SigmaFinite μ]

/-- Evaluate `schwartz_comp_clm` pointwise. -/
@[simp] lemma schwartz_comp_clm_apply (f : TestFunctionℂ4) (L : ℂ →L[ℝ] ℝ) (x : SpaceTime4) :
  (schwartz_comp_clm f L) x = L (f x) := rfl

/-- Decompose a complex test function into its real and imaginary parts as real test functions.
    This is more efficient than separate extraction functions. -/
def complex_testfunction_decompose (f : TestFunctionℂ4) : TestFunction4 × TestFunction4 :=
  (schwartz_comp_clm f Complex.reCLM, schwartz_comp_clm f Complex.imCLM)

/-- First component of the decomposition evaluates to the real part pointwise. -/
@[simp] lemma complex_testfunction_decompose_fst_apply
  (f : TestFunctionℂ4) (x : SpaceTime4) :
  (complex_testfunction_decompose f).1 x = (f x).re := by
  simp [complex_testfunction_decompose]

/-- Second component of the decomposition evaluates to the imaginary part pointwise. -/
@[simp] lemma complex_testfunction_decompose_snd_apply
  (f : TestFunctionℂ4) (x : SpaceTime4) :
  (complex_testfunction_decompose f).2 x = (f x).im := by
  simp [complex_testfunction_decompose]

/-- Coerced-to-ℂ version (useful for complex-side algebra). -/
@[simp] lemma complex_testfunction_decompose_fst_apply_coe
  (f : TestFunctionℂ4) (x : SpaceTime4) :
  ((complex_testfunction_decompose f).1 x : ℂ) = ((f x).re : ℂ) := by
  simp [complex_testfunction_decompose]

/-- Coerced-to-ℂ version (useful for complex-side algebra). -/
@[simp] lemma complex_testfunction_decompose_snd_apply_coe
  (f : TestFunctionℂ4) (x : SpaceTime4) :
  ((complex_testfunction_decompose f).2 x : ℂ) = ((f x).im : ℂ) := by
  simp [complex_testfunction_decompose]

/-- Recomposition at a point via the decomposition. -/
lemma complex_testfunction_decompose_recompose
  (f : TestFunctionℂ4) (x : SpaceTime4) :
  f x = ((complex_testfunction_decompose f).1 x : ℂ)
          + Complex.I * ((complex_testfunction_decompose f).2 x : ℂ) := by
  -- Reduce to the standard identity z = re z + i im z
  have h1 : f x = (Complex.re (f x) : ℂ) + (Complex.im (f x) : ℂ) * Complex.I :=
    (Complex.re_add_im (f x)).symm
  have h2 : f x = (Complex.re (f x) : ℂ) + Complex.I * (Complex.im (f x) : ℂ) := by
    simpa [mul_comm] using h1
  -- Rewrite re/im via the decomposition
  simpa using h2

/-- Complex version of the pairing: real field configuration with complex test function
    We extend the pairing by treating the complex test function as f(x) = f_re(x) + i*f_im(x)
    and defining ⟨ω, f⟩ = ⟨ω, f_re⟩ + i*⟨ω, f_im⟩ -/
def distributionPairingℂ_real (ω : FieldConfiguration4) (f : TestFunctionℂ4) : ℂ :=
  -- Extract real and imaginary parts using our efficient decomposition
  let ⟨f_re, f_im⟩ := complex_testfunction_decompose f
  -- Pair with the real field configuration and combine
  (ω f_re : ℂ) + Complex.I * (ω f_im : ℂ)

/-- Complex version of the generating functional -/
def GJGeneratingFunctionalℂ (dμ_config : ProbabilityMeasure FieldConfiguration4)
  (J : TestFunctionℂ4) : ℂ :=
  ∫ ω, Complex.exp (Complex.I * (distributionPairingℂ_real ω J)) ∂dμ_config.toMeasure

/-- The mean field in the Glimm-Jaffe framework -/
def GJMean (dμ_config : ProbabilityMeasure FieldConfiguration4)
  (φ : TestFunction4) : ℝ :=
  ∫ ω, distributionPairing ω φ ∂dμ_config.toMeasure

/-! ## Spatial Geometry and Energy Operators -/

/-- Spatial coordinates: ℝ^{d-1} (space without time) as EuclideanSpace for L2 norm -/
abbrev SpatialCoords := EuclideanSpace ℝ (Fin (STDimension - 1))

/-- L² space on spatial slices (real-valued) -/
abbrev SpatialL2 := Lp ℝ 2 (volume : Measure SpatialCoords)

/-- Extract spatial part of spacetime coordinate -/
def spatialPart (x : SpaceTime4) : SpatialCoords :=
  (EuclideanSpace.equiv (Fin (STDimension - 1)) ℝ).symm
    (fun i => x ⟨i.val + 1, by simp [STDimension]; omega⟩)

/-- The energy function E(k) = √(‖k‖² + m²) on spatial momentum space -/
def E (m : ℝ) (k : SpatialCoords) : ℝ :=
  Real.sqrt (‖k‖^2 + m^2)

end

/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
import Mathlib.Analysis.Fourier.Inversion
import OSforGFF.Spacetime.Basic
import OSforGFF.Covariance.Propagator

/-!
# The dimension-generic Parseval bridge

The complex covariance pairings of Schwartz test functions against the radial kernel
`freeCovariance d m`, and their momentum-space form. The central identity is the Parseval
bridge for the quadratic pairing,

`(freeCovarianceℂ m f f).re = ∫ k, ‖𝓕f(k)‖² · P(k) dk`,

with `P = freePropagatorMom d m` the momentum-space propagator; positivity of the covariance
pairing follows. The kernel enters only through its `L¹`-integrability and the Fourier
transform of the proper-time covariance (`properTimeCovariance_fourier`), so the whole bridge
is uniform in the dimension `d`.

## Main definitions

- `freeCovarianceℂ_bilinear`: the bilinear pairing `∫∫ f(x) C(x,y) g(y)`
- `freeCovarianceℂ`: the sesquilinear pairing `∫∫ f(x) C(x,y) conj (g y)`

## Main results

- `freeCovarianceℂ_bilinear_integrable`: product-space integrability of the pairing integrand
-/

open MeasureTheory Complex OSforGFF
open scoped RealInnerProductSpace

noncomputable section

namespace OSforGFF

/-- The proper-time covariance is a measurable function of the radius. -/
lemma properTimeCovariance_measurable (d : ℕ) (m : ℝ) :
    Measurable (properTimeCovariance d m) := by
  have h : StronglyMeasurable (Function.uncurry fun (r t : ℝ) =>
      Real.exp (-t * m ^ 2) * heatKernelProfile d t r) := by
    apply Measurable.stronglyMeasurable
    unfold Function.uncurry heatKernelProfile
    fun_prop
  exact (h.integral_prod_right' (ν := volume.restrict (Set.Ioi 0))).measurable

/-- `x ↦ C_S(‖x‖)` is measurable on `ℝ^d`. -/
lemma properTimeCovariance_norm_measurable (d : ℕ) (m : ℝ) :
    Measurable fun x : EuclideanSpace ℝ (Fin d) => properTimeCovariance d m ‖x‖ :=
  (properTimeCovariance_measurable d m).comp measurable_norm

end OSforGFF

/-- The complex covariance bilinear pairing of two complex test functions against the
    free-covariance kernel: `⟨f, C g⟩ = ∫∫ f(x) · C(x, y) · g(y) dx dy`. -/
def freeCovarianceℂ_bilinear {d : ℕ} (m : ℝ) [Fact (0 < m)] [Fact (2 ≤ d)]
    [GFFPropagator d m] (f g : TestFunctionℂ d) : ℂ :=
  ∫ x, ∫ y, f x * (freeCovariance d m x y : ℂ) * g y

/-- The complex covariance sesquilinear pairing:
    `⟨f, C ḡ⟩ = ∫∫ f(x) · C(x, y) · conj (g y) dx dy`. -/
def freeCovarianceℂ {d : ℕ} (m : ℝ) [Fact (0 < m)] [Fact (2 ≤ d)]
    [GFFPropagator d m] (f g : TestFunctionℂ d) : ℂ :=
  ∫ x, ∫ y, f x * (freeCovariance d m x y : ℂ) * (starRingEnd ℂ (g y))

section ProperTimeKernel

variable {d : ℕ} {m : ℝ} [Fact (0 < m)] [Fact (2 ≤ d)]

/-- The diagonal `{(x, y) | x = y}` is null for the product volume. -/
lemma diagonal_null_prod :
    ((volume : Measure (SpaceTime d)).prod volume)
      {p : SpaceTime d × SpaceTime d | p.1 - p.2 = 0} = 0 := by
  have hd : 0 < d := by have := (Fact.out : 2 ≤ d); omega
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have : Nontrivial (SpaceTime d) := inferInstance
  have hmeas : MeasurableSet {p : SpaceTime d × SpaceTime d | p.1 - p.2 = 0} :=
    (measurable_fst.sub measurable_snd) (measurableSet_singleton 0)
  rw [Measure.prod_apply hmeas]
  have hslice : ∀ x : SpaceTime d,
      (Prod.mk x ⁻¹' {p : SpaceTime d × SpaceTime d | p.1 - p.2 = 0}) = {x} := by
    intro x
    ext y
    simp [sub_eq_zero, eq_comm]
  simp [hslice]

/-- Away from the (null) diagonal the covariance kernel agrees with the proper-time kernel:
    a.e.-equality on the product space. -/
lemma freeCovariance_ae_properTime [GFFPropagator d m] :
    (fun p : SpaceTime d × SpaceTime d => freeCovariance d m p.1 p.2)
      =ᵐ[(volume : Measure (SpaceTime d)).prod volume]
    fun p => properTimeCovariance d m ‖p.1 - p.2‖ := by
  filter_upwards [compl_mem_ae_iff.mpr (diagonal_null_prod (d := d))] with p hp
  have hne : p.1 - p.2 ≠ 0 := hp
  unfold freeCovariance
  exact GFFPropagator.schwinger_eq ‖p.1 - p.2‖ (norm_pos_iff.mpr hne)

omit [Fact (2 ≤ d)] in
/-- The Schwartz-pair integrand against the proper-time kernel is integrable on the product
    space: the bound `‖f‖_∞ · C_S(‖x − y‖) · ‖g(y)‖` is a shear transport of a product of
    integrable functions. -/
lemma properTime_bilinear_integrable (f g : TestFunctionℂ d) :
    Integrable (fun p : SpaceTime d × SpaceTime d =>
      f p.1 * (properTimeCovariance d m ‖p.1 - p.2‖ : ℂ) * g p.2)
      ((volume : Measure (SpaceTime d)).prod volume) := by
  have hm : (0 : ℝ) < m := Fact.out
  obtain ⟨M, hM0, hMd⟩ := f.decay 0 0
  have hM : ∀ x, ‖f x‖ ≤ M := by
    intro x
    have := hMd x
    simpa [norm_iteratedFDeriv_zero] using this
  have hCS : Integrable (fun z : SpaceTime d => properTimeCovariance d m ‖z‖) :=
    properTimeCovariance_integrable d m hm
  have hgM : Integrable (fun y : SpaceTime d => M * ‖g y‖) := g.integrable.norm.const_mul M
  have hprod : Integrable (fun q : SpaceTime d × SpaceTime d =>
      properTimeCovariance d m ‖q.1‖ * (M * ‖g q.2‖))
      ((volume : Measure (SpaceTime d)).prod volume) := hCS.mul_prod hgM
  have hshear : Integrable (fun p : SpaceTime d × SpaceTime d =>
      properTimeCovariance d m ‖p.1 - p.2‖ * (M * ‖g p.2‖))
      ((volume : Measure (SpaceTime d)).prod volume) := by
    have h := (measurePreserving_sub_prod (volume : Measure (SpaceTime d))
      volume).integrable_comp_of_integrable hprod
    simpa [Function.comp_def] using h
  have hmeas : AEStronglyMeasurable (fun p : SpaceTime d × SpaceTime d =>
      f p.1 * (properTimeCovariance d m ‖p.1 - p.2‖ : ℂ) * g p.2)
      ((volume : Measure (SpaceTime d)).prod volume) := by
    refine AEStronglyMeasurable.mul (AEStronglyMeasurable.mul ?_ ?_) ?_
    · exact f.continuous.aestronglyMeasurable.comp_fst
    · exact (Complex.measurable_ofReal.comp ((properTimeCovariance_norm_measurable d m).comp
        (measurable_fst.sub measurable_snd))).aestronglyMeasurable
    · exact g.continuous.aestronglyMeasurable.comp_snd
  refine hshear.mono' hmeas ?_
  filter_upwards with p
  have h1 : 0 ≤ properTimeCovariance d m ‖p.1 - p.2‖ := properTimeCovariance_nonneg _ _ _
  calc ‖f p.1 * (properTimeCovariance d m ‖p.1 - p.2‖ : ℂ) * g p.2‖
      = ‖f p.1‖ * properTimeCovariance d m ‖p.1 - p.2‖ * ‖g p.2‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg h1]
    _ ≤ M * properTimeCovariance d m ‖p.1 - p.2‖ * ‖g p.2‖ := by
        gcongr
        exact hM p.1
    _ = properTimeCovariance d m ‖p.1 - p.2‖ * (M * ‖g p.2‖) := by ring

end ProperTimeKernel

/-- The bilinear-pairing integrand is integrable on the product space. -/
theorem freeCovarianceℂ_bilinear_integrable {d : ℕ} (m : ℝ) [Fact (0 < m)] [Fact (2 ≤ d)]
    [GFFPropagator d m] (f g : TestFunctionℂ d) :
    Integrable (fun p : SpaceTime d × SpaceTime d =>
      f p.1 * (freeCovariance d m p.1 p.2 : ℂ) * g p.2) volume := by
  rw [Measure.volume_eq_prod]
  refine (properTime_bilinear_integrable (m := m) f g).congr ?_
  filter_upwards [freeCovariance_ae_properTime (d := d) (m := m)] with p hp
  rw [hp]

end

/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Basic
import OSforGFF.General.FunctionalAnalysis
import OSforGFF.Spacetime.Basic


open MeasureTheory SchwartzMap Real Set Metric
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace SchwartzLinearBound

end SchwartzLinearBound

/-! ## Time-slice machinery for `SpaceTime d`

The time coordinate of `x : SpaceTime d` is accessed via `x 0`.
These lemmas match the signatures needed in OS3_MixedRepInfra.lean.
-/

section TimeSlice

variable {d : ℕ} [Fact (2 ≤ d)]

/-- For a Schwartz function vanishing on {x₀ ≤ 0}, the linear bound ‖f(x)‖ ≤ C · x₀ holds.
    Follows from mean value theorem + global derivative bounds on Schwartz functions. -/
theorem schwartz_vanishing_linear_bound (f : TestFunctionℂ d)
    (hf_supp : ∀ x : SpaceTime d, x 0 ≤ 0 → f x = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : SpaceTime d, 0 < x 0 → ‖f x‖ ≤ C * (x 0) := by
  -- Step 1: Get a global bound on the first derivative from Schwartz decay
  -- f.decay' 0 1 gives: ∃ C, ∀ x, ‖x‖^0 * ‖iteratedFDeriv ℝ 1 f x‖ ≤ C
  obtain ⟨C_deriv, hC_deriv⟩ := f.decay' 0 1

  -- The derivative bound (simplified from decay)
  have h_deriv_bound : ∀ y : SpaceTime d, ‖iteratedFDeriv ℝ 1 f y‖ ≤ C_deriv := by
    intro y
    have := hC_deriv y
    simp only [pow_zero, one_mul] at this
    exact this

  -- Use C_deriv + 1 to ensure positivity
  use C_deriv + 1
  constructor
  · -- C_deriv + 1 > 0 because C_deriv ≥ 0 (it bounds a norm)
    have h_nonneg : 0 ≤ C_deriv := by
      have := h_deriv_bound 0
      exact le_trans (norm_nonneg _) this
    linarith

  -- Step 2: For each x with x₀ > 0, show ‖f x‖ ≤ (C_deriv + 1) * x₀
  intro x hx_pos

  -- Construct the boundary point: x with time component set to 0
  -- x₀_bdy = x - (x 0) • e₀ where e₀ = EuclideanSpace.single 0 1
  let e₀ : SpaceTime d := EuclideanSpace.single 0 1
  let x₀_bdy : SpaceTime d := x - (x 0) • e₀

  -- Verify x₀_bdy 0 = 0
  -- (x - (x 0) • e₀) 0 = x 0 - (x 0) * (e₀ 0) = x 0 - (x 0) * 1 = 0
  have h_bdy_time : x₀_bdy 0 = 0 := by
    -- Need to work with the underlying Pi type through WithLp coercions
    -- x₀_bdy 0 = (x - (x 0) • e₀) 0 = x 0 - (x 0) * (e₀ 0) = x 0 - x 0 = 0
    show (WithLp.ofLp x₀_bdy) 0 = 0
    simp only [x₀_bdy, e₀, WithLp.ofLp_sub, WithLp.ofLp_smul, Pi.sub_apply, Pi.smul_apply,
               smul_eq_mul, EuclideanSpace.single_apply, ite_true, mul_one, sub_self]

  -- f vanishes at the boundary
  have hf_bdy : f x₀_bdy = 0 := hf_supp x₀_bdy (le_of_eq h_bdy_time)

  -- Compute ‖x - x₀_bdy‖ = |x 0|
  -- x - x₀_bdy = x - (x - (x 0) • e₀) = (x 0) • e₀
  -- ‖(x 0) • e₀‖ = |x 0| * ‖e₀‖ = |x 0| * 1 = |x 0|
  have h_dist : ‖x - x₀_bdy‖ = |x 0| := by
    have h1 : x - x₀_bdy = (x 0) • e₀ := by simp only [x₀_bdy]; abel
    rw [h1, norm_smul, Real.norm_eq_abs]
    have h_e₀_norm : ‖e₀‖ = 1 := by
      simp only [e₀]
      rw [EuclideanSpace.norm_single, norm_one]
    rw [h_e₀_norm, mul_one]

  -- Since x 0 > 0, we have |x 0| = x 0
  rw [abs_of_pos hx_pos] at h_dist

  -- SpaceTime d is convex
  have h_convex : Convex ℝ (Set.univ : Set (SpaceTime d)) := convex_univ

  -- Schwartz functions have FDeriv everywhere
  have h_hasFDeriv : ∀ y ∈ (Set.univ : Set (SpaceTime d)),
      HasFDerivWithinAt f (fderiv ℝ f y) Set.univ y := by
    intro y _
    exact f.differentiableAt.hasFDerivAt.hasFDerivWithinAt

  -- Connection: ‖fderiv ℝ f y‖ = ‖iteratedFDeriv ℝ 1 f y‖ (via curry isomorphism)
  have h_fderiv_bound : ∀ y ∈ (Set.univ : Set (SpaceTime d)), ‖fderiv ℝ f y‖ ≤ C_deriv := by
    intro y _
    -- Use: ‖iteratedFDeriv ℝ 1 f y‖ = ‖fderiv ℝ f y‖
    -- This follows from iteratedFDeriv 1 f = curryLeftEquiv.symm ∘ fderiv f ∘ iteratedFDeriv 0 f
    -- where curryLeftEquiv is an isometry
    have h_norm_eq : ‖iteratedFDeriv ℝ 1 f y‖ = ‖fderiv ℝ f y‖ := by
      -- iteratedFDeriv_succ_eq_comp_left gives:
      -- iteratedFDeriv ℝ 1 f = curryLeftEquiv.symm ∘ fderiv ℝ (iteratedFDeriv ℝ 0 f)
      -- And iteratedFDeriv ℝ 0 f = f via continuousMultilinearCurryFin0
      rw [← iteratedFDerivWithin_univ, ← fderivWithin_univ]
      exact norm_iteratedFDerivWithin_one f uniqueDiffWithinAt_univ
    linarith [h_deriv_bound y]

  -- Apply the Mean Value Theorem (Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le)
  -- Note: The lemma gives ‖f y - f x‖ ≤ C * ‖y - x‖, so we need to swap x and x₀_bdy
  have h_mvt := h_convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
    h_hasFDeriv h_fderiv_bound (Set.mem_univ x₀_bdy) (Set.mem_univ x)

  -- Final calculation: ‖f x‖ = ‖f x - f x₀_bdy‖ ≤ C_deriv * ‖x - x₀_bdy‖ = C_deriv * (x 0)
  calc ‖f x‖ = ‖f x - 0‖ := by rw [sub_zero]
    _ = ‖f x - f x₀_bdy‖ := by rw [hf_bdy]
    _ ≤ C_deriv * ‖x - x₀_bdy‖ := h_mvt
    _ = C_deriv * (x 0) := by rw [h_dist]
    _ ≤ (C_deriv + 1) * (x 0) := by nlinarith [hx_pos]

/-! ## Integrate over space first (Fubini approach)

The key insight is to decompose `SpaceTime d` = ℝ × ℝ^(d-1) and integrate over spatial
coordinates first. For a Schwartz function f : SpaceTime d → ℂ vanishing at t ≤ 0:

1. Define G(t) = ∫_{ℝ³} ‖f(t, x)‖ dx  (the spatial integral of the norm)
2. G is well-defined and finite for all t (f is Schwartz)
3. G(t) = 0 for t ≤ 0 (f vanishes there)
4. G satisfies a linear bound: G(t) ≤ C·t for t > 0

Then by Fubini/Tonelli:
  ∫∫ ‖f(p₁)‖·‖f(p₂)‖/(t₁+t₂)² = ∫∫ G(t₁)·G(t₂)/(t₁+t₂)² dt₁ dt₂

Using G(t) ≤ C·t and AM-GM: t₁t₂/(t₁+t₂)² ≤ 1/4, the integrand is ≤ C²/4.
On the bounded time domain {0 < t₁, 0 < t₂, t₁+t₂ < 1}, this gives integrability.
-/

/-- The spatial slice of 4D spacetime: ℝ³. -/
abbrev SpatialCoords3 : Type := EuclideanSpace ℝ (Fin 3)

/-- Decomposition of spacetime as time × space: `(t, x) ↦ (t, x₁, …, x_{d-1})`. -/
noncomputable def spacetimeOfTimeSpace (t : ℝ) (x : SpatialCoords d) : SpaceTime d :=
  EuclideanSpace.equiv (Fin d) ℝ |>.symm fun i =>
    Fin.cons (α := fun _ => ℝ) t (fun j => x j)
      (Fin.cast (by have h : 2 ≤ d := Fact.out; omega) i)

/-- The time coordinate of spacetimeOfTimeSpace is t. -/
lemma spacetimeOfTimeSpace_time (t : ℝ) (x : SpatialCoords d) :
    (spacetimeOfTimeSpace t x) 0 = t := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by have h : 2 ≤ d := Fact.out; omega⟩
  simp [spacetimeOfTimeSpace, EuclideanSpace.equiv, Fin.cast, Fin.cons, Fin.cases]

/-- Access the i-th spatial component of spacetimeOfTimeSpace.
    Mathematical fact: (spacetimeOfTimeSpace t x) (i+1) = x i -/
lemma spacetimeOfTimeSpace_spatial (t : ℝ) (x : SpatialCoords d) (i : Fin (d - 1)) :
    (spacetimeOfTimeSpace t x) ⟨i.val + 1, by have := i.isLt; omega⟩ = x i := rfl

/-- The decomposition: spacetimeOfTimeSpace t x = timeOrigin t + spatialEmbed x.
    This is the key structural fact: (t, x) = (t, 0) + (0, x). -/
lemma spacetimeOfTimeSpace_decompose (t : ℝ) (x : SpatialCoords d) :
    spacetimeOfTimeSpace t x = spacetimeOfTimeSpace t 0 + spacetimeOfTimeSpace 0 x := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by have h : 2 ≤ d := Fact.out; omega⟩
  ext j
  cases' j using Fin.cases with j
  · -- time coordinate
    simp [spacetimeOfTimeSpace, EuclideanSpace.equiv, Fin.cast, Fin.cons, Fin.cases]
  · -- spatial coordinates
    simp [spacetimeOfTimeSpace, EuclideanSpace.equiv, Fin.cast, Fin.cons, Fin.cases]

/-- Norm comparison: the spacetime norm dominates the spatial norm. -/
lemma spacetimeOfTimeSpace_norm_ge (t : ℝ) (x : SpatialCoords d) :
    ‖spacetimeOfTimeSpace t x‖ ≥ ‖x‖ := by
  have hsq : ‖spacetimeOfTimeSpace t x‖ ^ 2 = t ^ 2 + ‖x‖ ^ 2 := by
    obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by have h : 2 ≤ d := Fact.out; omega⟩
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
    congr 1
    · rw [show (spacetimeOfTimeSpace t x).ofLp 0 = t from spacetimeOfTimeSpace_time t x]
      simp [Real.norm_eq_abs, sq_abs]
    · rw [EuclideanSpace.norm_sq_eq]
      exact Finset.sum_congr rfl fun j _ => by
        rw [show (spacetimeOfTimeSpace t x).ofLp j.succ = x j from rfl]
  have hsq_le : ‖x‖ ^ 2 ≤ ‖spacetimeOfTimeSpace t x‖ ^ 2 := by
    rw [hsq]; nlinarith [sq_nonneg t]
  have hx : 0 ≤ ‖x‖ := norm_nonneg _
  have hy : 0 ≤ ‖spacetimeOfTimeSpace t x‖ := norm_nonneg _
  exact (sq_le_sq₀ hx hy).mp hsq_le

/-- Linear embedding of space into spacetime as the spatial subspace at time 0.
    This maps x ↦ (0, x₁, …, x_{d-1}), i.e., spacetimeOfTimeSpace 0 x. -/
noncomputable def spatialEmbed : SpatialCoords d →ₗ[ℝ] SpaceTime d where
  toFun := fun x => spacetimeOfTimeSpace 0 x
  map_add' := fun x y => by
    obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by have h : 2 ≤ d := Fact.out; omega⟩
    ext j
    cases' j using Fin.cases with j
    · simp [spacetimeOfTimeSpace, EuclideanSpace.equiv, Fin.cast, Fin.cons, Fin.cases]
    · simp [spacetimeOfTimeSpace, EuclideanSpace.equiv, Fin.cast, Fin.cons, Fin.cases]
  map_smul' := fun r x => by
    obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by have h : 2 ≤ d := Fact.out; omega⟩
    ext j
    cases' j using Fin.cases with j
    · simp [spacetimeOfTimeSpace, EuclideanSpace.equiv, Fin.cast, Fin.cons, Fin.cases]
    · simp [spacetimeOfTimeSpace, EuclideanSpace.equiv, Fin.cast, Fin.cons, Fin.cases]

/-- The spatial embedding is continuous (being linear on finite-dim spaces). -/
lemma spatialEmbed_continuous : Continuous (spatialEmbed (d := d)) :=
  LinearMap.continuous_of_finiteDimensional spatialEmbed

/-- The spatial embedding as a CLM. -/
noncomputable def spatialEmbedCLM : SpatialCoords d →L[ℝ] SpaceTime d :=
  ⟨spatialEmbed, spatialEmbed_continuous⟩

/-- The time-origin point `(t, 0, …, 0)`. -/
noncomputable def timeOrigin (t : ℝ) : SpaceTime d :=
  spacetimeOfTimeSpace t 0

/-- spacetimeOfTimeSpace is continuous in the spatial argument for fixed time. -/
lemma continuous_spacetimeOfTimeSpace_right (t : ℝ) :
    Continuous (spacetimeOfTimeSpace (d := d) t) := by
  -- spacetimeOfTimeSpace t x = timeOrigin t + spatialEmbedCLM x
  -- The first term is constant, the second is a CLM applied to x
  have h_decompose : ∀ x : SpatialCoords d,
      spacetimeOfTimeSpace t x = timeOrigin t + spatialEmbedCLM x := by
    intro x
    rw [spacetimeOfTimeSpace_decompose]
    rfl
  have h_cont : Continuous (fun x : SpatialCoords d => timeOrigin t + spatialEmbedCLM x) :=
    continuous_const.add spatialEmbedCLM.continuous
  exact (continuous_congr h_decompose).mpr h_cont

/-- The squared norm splits into time and spatial parts:
    `‖(t, x)‖² = t² + ‖x‖²`. -/
lemma spacetimeOfTimeSpace_norm_sq (t : ℝ) (x : SpatialCoords d) :
    ‖spacetimeOfTimeSpace t x‖ ^ 2 = t ^ 2 + ‖x‖ ^ 2 := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by have h : 2 ≤ d := Fact.out; omega⟩
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
  congr 1
  · rw [show (spacetimeOfTimeSpace t x).ofLp 0 = t from spacetimeOfTimeSpace_time t x]
    simp [Real.norm_eq_abs, sq_abs]
  · rw [EuclideanSpace.norm_sq_eq]
    exact Finset.sum_congr rfl fun j _ => by
      rw [show (spacetimeOfTimeSpace t x).ofLp j.succ = x j from rfl]

/-- The time-axis point `(s, 0, …, 0)` is `s` times the time unit vector. -/
lemma spacetimeOfTimeSpace_eq_smul_single (s : ℝ) :
    spacetimeOfTimeSpace (d := d) s 0 = s • (EuclideanSpace.single (0 : Fin d) (1 : ℝ)) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by have h : 2 ≤ d := Fact.out; omega⟩
  ext j
  cases' j using Fin.cases with j
  · simp [spacetimeOfTimeSpace, EuclideanSpace.equiv, Fin.cast, Fin.cons, Fin.cases,
          EuclideanSpace.single_apply]
  · have hne : Fin.succ j ≠ 0 := Fin.succ_ne_zero j
    simp [spacetimeOfTimeSpace, EuclideanSpace.equiv, Fin.cast, Fin.cons, Fin.cases,
          EuclideanSpace.single_apply, hne]

/-- The polynomial decay `1/(1+‖x‖)^d` is integrable on the spatial slice `ℝ^(d-1)`
    (the exponent `d` exceeds the dimension `d - 1`). -/
lemma polynomial_decay_integrable_spatial :
    Integrable (fun x : SpatialCoords d => 1 / (1 + ‖x‖) ^ d) volume := by
  have h1d : 1 ≤ d := by have h : 2 ≤ d := Fact.out; omega
  have hdim_lt : (Module.finrank ℝ (SpatialCoords d) : ℝ) < ((d : ℕ) : ℝ) := by
    rw [finrank_euclideanSpace_fin]
    have : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by push_cast [h1d]; ring
    rw [this]; linarith
  have h_int := integrable_one_add_norm (E := SpatialCoords d) (μ := volume)
    (r := ((d : ℕ) : ℝ)) hdim_lt
  convert h_int using 1
  ext x
  have h_pos : 0 < 1 + ‖x‖ := by linarith [norm_nonneg x]
  simp only [Real.rpow_neg (le_of_lt h_pos), one_div]
  congr 1
  exact (Real.rpow_natCast (1 + ‖x‖) d).symm

/-- A Schwartz function restricted to a fixed time slice is integrable over the spatial slice.
    Uses decay transfer: d-dimensional Schwartz decay implies (d-1)-dimensional integrability
    via norm comparison. -/
lemma schwartz_time_slice_integrable (f : TestFunctionℂ d) (t : ℝ) :
    Integrable (fun x : SpatialCoords d => f (spacetimeOfTimeSpace t x)) volume := by
  -- Strategy: Show the function has rapid decay and use integrability of decay functions
  --
  -- Key facts:
  -- 1. f is Schwartz, so |f(y)| ≤ C/(1 + ‖y‖)^N for any N
  -- 2. For fixed t, ‖spacetimeOfTimeSpace t x‖ ≥ ‖x‖
  -- 3. So |f(spacetimeOfTimeSpace t x)| ≤ C/(1 + ‖x‖)^N which is integrable for N > d - 1
  have h1d : 1 ≤ d := by have h : 2 ≤ d := Fact.out; omega
  have hST_dim : Module.finrank ℝ (SpaceTime d) < d + 1 := by
    rw [finrank_euclideanSpace_fin]; omega
  obtain ⟨C, hC_pos, hf_decay⟩ := schwartz_integrable_decay f (d + 1) hST_dim

  -- The dominator function: x ↦ C / (1 + ‖x‖)^(d+1)
  have h_dom_integrable : Integrable (fun x : SpatialCoords d => C / (1 + ‖x‖) ^ (d + 1)) volume := by
    have h_dim : (Module.finrank ℝ (SpatialCoords d) : ℝ) < ((d + 1 : ℕ) : ℝ) := by
      rw [finrank_euclideanSpace_fin]
      have : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by push_cast [h1d]; ring
      rw [this]; push_cast; linarith
    have h_int := integrable_one_add_norm (E := SpatialCoords d) (μ := volume)
      (r := ((d + 1 : ℕ) : ℝ)) h_dim
    have h_eq : ∀ x : SpatialCoords d,
        C / (1 + ‖x‖) ^ (d + 1) = C * (1 + ‖x‖) ^ (-((d + 1 : ℕ) : ℝ)) := by
      intro x
      have h_pos : 0 < 1 + ‖x‖ := by linarith [norm_nonneg x]
      have h1 : ((1 + ‖x‖) ^ (d + 1) : ℝ)⁻¹ = (1 + ‖x‖) ^ (-((d + 1 : ℕ) : ℝ)) := by
        rw [← Real.rpow_natCast (1 + ‖x‖) (d + 1), ← Real.rpow_neg (le_of_lt h_pos)]
      rw [div_eq_mul_inv, h1]
    simp_rw [h_eq]
    exact h_int.const_mul C

  -- Pointwise bound via the spacetime-vs-spatial norm comparison
  have h_bound : ∀ x : SpatialCoords d,
      ‖f (spacetimeOfTimeSpace t x)‖ ≤ C / (1 + ‖x‖) ^ (d + 1) := by
    intro x
    have h1 := hf_decay (spacetimeOfTimeSpace t x)
    have h_norm_ge : ‖spacetimeOfTimeSpace t x‖ ≥ ‖x‖ :=
      spacetimeOfTimeSpace_norm_ge t x
    have h_bracket_ge : 1 + ‖spacetimeOfTimeSpace t x‖ ≥ 1 + ‖x‖ := by linarith
    have h_bracket_pos : 0 < 1 + ‖x‖ := by linarith [norm_nonneg x]
    have h_pow_le : (1 + ‖x‖) ^ (d + 1) ≤ (1 + ‖spacetimeOfTimeSpace t x‖) ^ (d + 1) := by
      apply pow_le_pow_left₀ (by linarith [norm_nonneg x]) h_bracket_ge
    calc ‖f (spacetimeOfTimeSpace t x)‖
        ≤ C / (1 + ‖spacetimeOfTimeSpace t x‖) ^ (d + 1) := h1
      _ ≤ C / (1 + ‖x‖) ^ (d + 1) := by
          apply div_le_div_of_nonneg_left (le_of_lt hC_pos) (by positivity) h_pow_le

  -- Apply Integrable.mono
  apply Integrable.mono h_dom_integrable
    (f.continuous.comp (continuous_spacetimeOfTimeSpace_right t)).aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_of_nonneg (by positivity : 0 ≤ C / (1 + ‖x‖) ^ (d + 1))]
  exact h_bound x

/-- The spatial integral G(t) = ∫ ‖f(t, x)‖ dx over the spatial slice. -/
noncomputable def spatialNormIntegral (f : TestFunctionℂ d) (t : ℝ) : ℝ :=
  ∫ x : SpatialCoords d, ‖f (spacetimeOfTimeSpace t x)‖

/-- G(t) = 0 for t ≤ 0 when f vanishes on {t ≤ 0}. -/
lemma spatialNormIntegral_zero_of_neg (f : TestFunctionℂ d)
    (hf_supp : ∀ x : SpaceTime d, x 0 ≤ 0 → f x = 0) (t : ℝ) (ht : t ≤ 0) :
    spatialNormIntegral f t = 0 := by
  simp only [spatialNormIntegral]
  have h_zero : ∀ x : SpatialCoords d, ‖f (spacetimeOfTimeSpace t x)‖ = 0 := by
    intro x
    have h : (spacetimeOfTimeSpace t x) 0 ≤ 0 := by
      rw [spacetimeOfTimeSpace_time]; exact ht
    simp [hf_supp _ h]
  simp [h_zero]

/-- G(t) is nonnegative. -/
lemma spatialNormIntegral_nonneg (f : TestFunctionℂ d) (t : ℝ) :
    0 ≤ spatialNormIntegral f t :=
  integral_nonneg (fun _ => norm_nonneg _)

/-! ### FTC-based decay bound for Schwartz functions vanishing at t=0 -/

/-- **Combined FTC + Schwartz decay bound**: For a Schwartz function f vanishing at t ≤ 0,
    we have ‖f(t, x_sp)‖ ≤ C · t / (1 + ‖x_sp‖)^d.

    **Mathematical content**:

    Since f(0, x_sp) = 0 for all x_sp (by vanishing condition), the fundamental theorem
    of calculus gives:
      f(t, x_sp) = ∫₀^t ∂f/∂τ(τ, x_sp) dτ

    Therefore:
      ‖f(t, x_sp)‖ ≤ ∫₀^t ‖∂f/∂τ(τ, x_sp)‖ dτ ≤ t · sup_{τ∈[0,t]} ‖∂f/∂τ(τ, x_sp)‖

    The time derivative ∂f/∂τ is also Schwartz (derivatives of Schwartz functions are Schwartz),
    so it has fast spatial decay. For τ in any bounded interval [0, T]:
      ‖∂f/∂τ(τ, x_sp)‖ ≤ C_deriv / (1 + ‖x_sp‖)^d

    Combining: ‖f(t, x_sp)‖ ≤ t · C_deriv / (1 + ‖x_sp‖)^d

    **Key insight**: This bound is BOTH linear in t (from FTC) AND has spatial decay (from
    Schwartz property of the derivative). This combination is what makes the spatial
    integral ∫ ‖f(t, ·)‖ dx bounded by C·t.

    **Used by**: `spatialNormIntegral_linear_bound` and `F_norm_bound_via_linear_vanishing`. -/
lemma schwartz_vanishing_ftc_decay (f : TestFunctionℂ d)
    (hf_supp : ∀ x : SpaceTime d, x 0 ≤ 0 → f x = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (_ht : 0 < t) (x_sp : SpatialCoords d),
      ‖f (spacetimeOfTimeSpace t x_sp)‖ ≤ C * t / (1 + ‖x_sp‖) ^ d := by
  have hd0 : d ≠ 0 := by have h : 2 ≤ d := Fact.out; omega
  -- Step 1: Get derivative bounds from Schwartz decay
  -- f.decay' d 1 gives: ‖y‖^d * ‖iteratedFDeriv ℝ 1 f y‖ ≤ C_decay (for large ‖y‖)
  -- f.decay' 0 1 gives: ‖iteratedFDeriv ℝ 1 f y‖ ≤ C_unif (uniform bound for all y)
  obtain ⟨C_decay, hC_decay⟩ := f.decay' d 1
  obtain ⟨C_unif, hC_unif⟩ := f.decay' 0 1

  have h_unif : ∀ y : SpaceTime d, ‖iteratedFDeriv ℝ 1 f y‖ ≤ C_unif := by
    intro y; have := hC_unif y; simp only [pow_zero, one_mul] at this; exact this

  have hC_decay_nn : 0 ≤ C_decay := by
    have := hC_decay 0
    simp only [norm_zero, zero_pow hd0, zero_mul] at this; exact this

  have hC_unif_nn : 0 ≤ C_unif := le_trans (norm_nonneg _) (h_unif 0)

  have h2d_pos : (0 : ℝ) < 2 ^ d := by positivity

  -- Combined constant: handles both large ‖y‖ (via 2^d*C_decay) and small ‖y‖ (via 2^d*C_unif)
  -- For ‖y‖ ≥ 1: ‖Df‖ ≤ C_decay/‖y‖^d ≤ 2^d*C_decay/(1+‖y‖)^d
  -- For ‖y‖ < 1: ‖Df‖ ≤ C_unif ≤ 2^d*C_unif/(1+‖y‖)^d since (1+‖y‖)^d < 2^d
  let C := 2 ^ d * (C_decay + C_unif) + 1

  have hC_pos : 0 < C := by
    simp only [C]
    nlinarith [mul_nonneg (le_of_lt h2d_pos) (add_nonneg hC_decay_nn hC_unif_nn)]

  -- Key bound: ‖fderiv ℝ f y‖ ≤ C / (1 + ‖y‖)^d
  have h_fderiv_decay : ∀ y : SpaceTime d, ‖fderiv ℝ f y‖ ≤ C / (1 + ‖y‖) ^ d := by
    intro y
    -- Convert iteratedFDeriv to fderiv
    have h_norm_eq : ‖iteratedFDeriv ℝ 1 f y‖ = ‖fderiv ℝ f y‖ := by
      rw [← iteratedFDerivWithin_univ, ← fderivWithin_univ]
      exact norm_iteratedFDerivWithin_one f uniqueDiffWithinAt_univ
    have h1y : 0 < 1 + ‖y‖ := by linarith [norm_nonneg y]
    have h1y_pow : 0 < (1 + ‖y‖) ^ d := pow_pos h1y d
    by_cases hy_large : 1 ≤ ‖y‖
    · -- Large ‖y‖ case: use decay' d 1
      have hy_pos : 0 < ‖y‖ := by linarith
      have hy_pow : 0 < ‖y‖ ^ d := pow_pos hy_pos d
      have h_raw := hC_decay y
      -- From ‖y‖^d * ‖iteratedFDeriv 1 f y‖ ≤ C_decay, get ‖fderiv f y‖ ≤ C_decay / ‖y‖^d
      have h_fderiv_raw : ‖fderiv ℝ f y‖ ≤ C_decay / ‖y‖ ^ d := by
        rw [← h_norm_eq, le_div_iff₀ hy_pow]
        calc ‖iteratedFDeriv ℝ 1 f y‖ * ‖y‖ ^ d = ‖y‖ ^ d * ‖iteratedFDeriv ℝ 1 f y‖ := by ring
          _ ≤ C_decay := h_raw
      -- Convert: 1 + ‖y‖ ≤ 2‖y‖ implies (1+‖y‖)^d ≤ 2^d*‖y‖^d
      have h_2d : (1 + ‖y‖) ^ d ≤ 2 ^ d * ‖y‖ ^ d := by
        have h1 : (1 + ‖y‖) ^ d ≤ (2 * ‖y‖) ^ d := by
          apply pow_le_pow_left₀ (by linarith [norm_nonneg y]); linarith
        calc (1 + ‖y‖) ^ d ≤ (2 * ‖y‖) ^ d := h1
          _ = 2 ^ d * ‖y‖ ^ d := mul_pow 2 ‖y‖ d
      have h_norm_ge : ‖y‖ ^ d ≥ (1 + ‖y‖) ^ d / 2 ^ d := by
        rw [ge_iff_le, div_le_iff₀ h2d_pos]; linarith [h_2d]
      calc ‖fderiv ℝ f y‖ ≤ C_decay / ‖y‖ ^ d := h_fderiv_raw
        _ ≤ C_decay / ((1 + ‖y‖) ^ d / 2 ^ d) := by
            apply div_le_div_of_nonneg_left hC_decay_nn (div_pos h1y_pow h2d_pos) h_norm_ge
        _ = 2 ^ d * C_decay / (1 + ‖y‖) ^ d := by
            rw [div_div_eq_mul_div, mul_comm]
        _ ≤ C / (1 + ‖y‖) ^ d := by
            apply div_le_div_of_nonneg_right _ (le_of_lt h1y_pow)
            simp only [C]; nlinarith [mul_nonneg (le_of_lt h2d_pos) hC_unif_nn]
    · -- Small ‖y‖ case: use uniform bound C_unif
      push_neg at hy_large
      -- For ‖y‖ < 1: (1+‖y‖)^d < 2^d, so C_unif ≤ 2^d*C_unif/(1+‖y‖)^d
      have h_bracket_small : (1 + ‖y‖) ^ d ≤ 2 ^ d := by
        apply pow_le_pow_left₀ (by linarith [norm_nonneg y]); linarith
      calc ‖fderiv ℝ f y‖ = ‖iteratedFDeriv ℝ 1 f y‖ := h_norm_eq.symm
        _ ≤ C_unif := h_unif y
        _ = C_unif * 1 := by ring
        _ ≤ C_unif * ((1 + ‖y‖) ^ d / (1 + ‖y‖) ^ d) := by rw [div_self (ne_of_gt h1y_pow)]
        _ = C_unif * (1 + ‖y‖) ^ d / (1 + ‖y‖) ^ d := by ring
        _ ≤ C_unif * 2 ^ d / (1 + ‖y‖) ^ d := by
            apply div_le_div_of_nonneg_right _ (le_of_lt h1y_pow)
            exact mul_le_mul_of_nonneg_left h_bracket_small hC_unif_nn
        _ = 2 ^ d * C_unif / (1 + ‖y‖) ^ d := by ring
        _ ≤ C / (1 + ‖y‖) ^ d := by
            apply div_le_div_of_nonneg_right _ (le_of_lt h1y_pow)
            simp only [C]; nlinarith [mul_nonneg (le_of_lt h2d_pos) hC_decay_nn]

  -- Use C as the constant
  use C
  constructor
  · exact hC_pos

  -- Introduce t and x_sp
  intro t ht x_sp

  -- Step 2: Segment bound - on the path from (0, x_sp) to (t, x_sp)
  -- ‖(s, x_sp)‖² = s² + ‖x_sp‖² ≥ ‖x_sp‖², so (1+‖(s,x_sp)‖)^d ≥ (1+‖x_sp‖)^d
  have h_fderiv_segment : ∀ s : ℝ, 0 ≤ s → s ≤ t →
      ‖fderiv ℝ f (spacetimeOfTimeSpace s x_sp)‖ ≤ C / (1 + ‖x_sp‖) ^ d := by
    intros s _ _
    have h_decay := h_fderiv_decay (spacetimeOfTimeSpace s x_sp)
    have h_norm_ge : ‖spacetimeOfTimeSpace s x_sp‖ ≥ ‖x_sp‖ := spacetimeOfTimeSpace_norm_ge s x_sp
    have h1x : 0 < 1 + ‖x_sp‖ := by linarith [norm_nonneg x_sp]
    have h1x_pow : 0 < (1 + ‖x_sp‖) ^ d := pow_pos h1x d
    have h_bracket : (1 + ‖spacetimeOfTimeSpace s x_sp‖) ^ d ≥ (1 + ‖x_sp‖) ^ d := by
      apply pow_le_pow_left₀ (by linarith [norm_nonneg x_sp])
      linarith [h_norm_ge]
    calc ‖fderiv ℝ f (spacetimeOfTimeSpace s x_sp)‖
        ≤ C / (1 + ‖spacetimeOfTimeSpace s x_sp‖) ^ d := h_decay
      _ ≤ C / (1 + ‖x_sp‖) ^ d := by
          apply div_le_div_of_nonneg_left (le_of_lt hC_pos) h1x_pow h_bracket

  -- Step 3: Apply 1D MVT along the time direction
  let x := spacetimeOfTimeSpace t x_sp
  let x₀_bdy := spacetimeOfTimeSpace 0 x_sp

  have hf_bdy : f x₀_bdy = 0 := hf_supp x₀_bdy (by rw [spacetimeOfTimeSpace_time])

  have h1x : 0 < 1 + ‖x_sp‖ := by linarith [norm_nonneg x_sp]
  have h1x_pow : 0 < (1 + ‖x_sp‖) ^ d := pow_pos h1x d

  -- Compute ‖x - x₀_bdy‖ = t
  have h_dist : ‖x - x₀_bdy‖ = t := by
    have h_diff : x - x₀_bdy = spacetimeOfTimeSpace t 0 := by
      simp only [x, x₀_bdy]
      rw [spacetimeOfTimeSpace_decompose t x_sp, spacetimeOfTimeSpace_decompose 0 x_sp]
      abel
    rw [h_diff]
    have hsq : ‖spacetimeOfTimeSpace (d := d) t (0 : SpatialCoords d)‖ ^ 2 = t ^ 2 := by
      rw [spacetimeOfTimeSpace_norm_sq]
      simp
    have hnorm : 0 ≤ ‖spacetimeOfTimeSpace (d := d) t (0 : SpatialCoords d)‖ := norm_nonneg _
    nlinarith [hsq, ht]

  -- Parameterize F(s) = f(spacetimeOfTimeSpace s x_sp); the path is affine in s
  let F := fun s : ℝ => f (spacetimeOfTimeSpace s x_sp)

  -- The time unit vector
  let e₀ : SpaceTime d := EuclideanSpace.single 0 1

  -- The path s ↦ spacetimeOfTimeSpace s x_sp equals spacetimeOfTimeSpace 0 x_sp + s • e₀
  have h_path_eq : ∀ s : ℝ, spacetimeOfTimeSpace s x_sp = spacetimeOfTimeSpace 0 x_sp + s • e₀ := by
    intro s
    rw [spacetimeOfTimeSpace_decompose s x_sp, spacetimeOfTimeSpace_eq_smul_single, add_comm]

  have h_F_diff : DifferentiableOn ℝ F (Set.Icc 0 t) := by
    intro s _
    simp only [F]
    apply DifferentiableAt.differentiableWithinAt
    apply f.differentiableAt.comp
    have h_eq : (fun s => spacetimeOfTimeSpace (d := d) s x_sp) =
                (fun s => spacetimeOfTimeSpace 0 x_sp + s • e₀) := funext h_path_eq
    rw [h_eq]
    exact (differentiable_const _).add (differentiable_id.smul_const e₀) |>.differentiableAt

  have h_e₀_norm : ‖e₀‖ = 1 := by
    simp only [e₀]
    rw [EuclideanSpace.norm_single, norm_one]

  have h_deriv_bound : ∀ s ∈ Set.Ico 0 t,
      ‖derivWithin F (Set.Icc 0 t) s‖ ≤ C / (1 + ‖x_sp‖) ^ d := by
    intro s hs
    have h_seg := h_fderiv_segment s hs.1 (le_of_lt hs.2)
    -- The path derivative is e₀
    have h_path_diff : HasDerivAt (fun s => spacetimeOfTimeSpace (d := d) s x_sp) e₀ s := by
      have h_eq : (fun s => spacetimeOfTimeSpace (d := d) s x_sp) =
                  (fun s => spacetimeOfTimeSpace 0 x_sp + s • e₀) := funext h_path_eq
      rw [h_eq]
      have h1 : HasDerivAt (fun _ : ℝ => spacetimeOfTimeSpace (d := d) 0 x_sp) 0 s :=
        hasDerivAt_const s _
      have h2 : HasDerivAt (fun r : ℝ => r • e₀) ((1 : ℝ) • e₀) s := hasDerivAt_id s |>.smul_const e₀
      convert h1.add h2 using 1
      simp only [zero_add, one_smul]

    -- Chain rule for F = f ∘ path
    have h_in_Icc : s ∈ Set.Icc 0 t := ⟨hs.1, le_of_lt hs.2⟩
    have h_F_deriv : HasDerivWithinAt F ((fderiv ℝ f (spacetimeOfTimeSpace s x_sp)) e₀)
                                       (Set.Icc 0 t) s := by
      apply HasFDerivAt.comp_hasDerivWithinAt s
      · exact f.differentiableAt.hasFDerivAt
      · exact h_path_diff.hasDerivWithinAt

    have h_deriv_eq : derivWithin F (Set.Icc 0 t) s = (fderiv ℝ f (spacetimeOfTimeSpace s x_sp)) e₀ :=
      h_F_deriv.derivWithin (uniqueDiffOn_Icc (by linarith : (0 : ℝ) < t) s h_in_Icc)

    rw [h_deriv_eq]
    calc ‖(fderiv ℝ f (spacetimeOfTimeSpace s x_sp)) e₀‖
        ≤ ‖fderiv ℝ f (spacetimeOfTimeSpace s x_sp)‖ * ‖e₀‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ f (spacetimeOfTimeSpace s x_sp)‖ := by rw [h_e₀_norm, mul_one]
      _ ≤ C / (1 + ‖x_sp‖) ^ d := h_seg

  -- Apply norm_image_sub_le_of_norm_deriv_le_segment
  have h_mvt := norm_image_sub_le_of_norm_deriv_le_segment h_F_diff h_deriv_bound t
    (Set.right_mem_Icc.mpr (le_of_lt ht))

  -- F(0) = f(x₀_bdy) = 0
  have hF0 : F 0 = 0 := hf_bdy

  calc ‖f x‖ = ‖F t‖ := rfl
    _ = ‖F t - 0‖ := by rw [sub_zero]
    _ = ‖F t - F 0‖ := by rw [hF0]
    _ ≤ C / (1 + ‖x_sp‖) ^ d * (t - 0) := h_mvt
    _ = C * t / (1 + ‖x_sp‖) ^ d := by ring

/-- The key linear bound: G(t) ≤ C·t for t > 0.

    This follows from integrating the pointwise bound ‖f(t,x)‖ ≤ C·t
    over the spatial coordinates. Since Schwartz functions have fast decay,
    the spatial integral is finite. -/
theorem spatialNormIntegral_linear_bound (f : TestFunctionℂ d)
    (hf_supp : ∀ x : SpaceTime d, x 0 ≤ 0 → f x = 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → spatialNormIntegral f t ≤ C * t := by
  -- Step 1: Get the pointwise FTC + decay bound from helper lemma
  obtain ⟨C_pt, hC_pt_pos, h_pt_bound⟩ := schwartz_vanishing_ftc_decay f hf_supp

  -- Step 2: Integrability of the decay function
  have h_decay_int := polynomial_decay_integrable_spatial (d := d)

  -- Step 3: Define the constant K = ∫ 1/(1+‖x‖)^d dx (finite by h_decay_int)
  let K := ∫ x : SpatialCoords d, 1 / (1 + ‖x‖) ^ d

  -- K is nonnegative (integral of nonnegative function)
  have hK_nonneg : 0 ≤ K := integral_nonneg (fun x => by positivity)

  -- Use C = C_pt * (K + 1) to ensure positivity
  use C_pt * (K + 1)
  constructor
  · apply mul_pos hC_pt_pos; linarith

  intro t ht

  -- Step 4: Apply integral monotonicity
  have h_pointwise : ∀ x : SpatialCoords d,
      ‖f (spacetimeOfTimeSpace t x)‖ ≤ C_pt * t / (1 + ‖x‖) ^ d := fun x => h_pt_bound t ht x

  -- The bound function is integrable (scale of polynomial_decay_integrable_spatial)
  have h_bound_int : Integrable (fun x : SpatialCoords d => C_pt * t / (1 + ‖x‖) ^ d) volume := by
    have h1 : Integrable (fun x : SpatialCoords d => 1 / (1 + ‖x‖) ^ d) volume := h_decay_int
    have h_eq : (fun x : SpatialCoords d => C_pt * t / (1 + ‖x‖) ^ d) =
                (fun x : SpatialCoords d => (C_pt * t) * (1 / (1 + ‖x‖) ^ d)) := by
      ext x; ring
    rw [h_eq]
    exact h1.const_mul (C_pt * t)

  -- The integrand ‖f ...‖ is integrable (bounded by integrable function)
  have h_f_int : Integrable (fun x : SpatialCoords d => ‖f (spacetimeOfTimeSpace t x)‖) volume := by
    apply h_bound_int.mono
    · exact (f.continuous.comp (continuous_spacetimeOfTimeSpace_right t)).aestronglyMeasurable.norm
    · filter_upwards with x
      rw [norm_norm]
      have h1x : 0 < 1 + ‖x‖ := by linarith [norm_nonneg x]
      have h1x_pow : 0 < (1 + ‖x‖) ^ d := pow_pos h1x d
      have hCt : 0 ≤ C_pt * t := mul_nonneg (le_of_lt hC_pt_pos) (le_of_lt ht)
      calc ‖f (spacetimeOfTimeSpace t x)‖
          ≤ C_pt * t / (1 + ‖x‖) ^ d := h_pointwise x
        _ ≤ |C_pt * t / (1 + ‖x‖) ^ d| := le_abs_self _
        _ = ‖C_pt * t / (1 + ‖x‖) ^ d‖ := (Real.norm_eq_abs _).symm

  -- Convert pointwise bound to ae bound
  have h_ae_bound : ∀ᵐ x ∂(volume : Measure (SpatialCoords d)),
      ‖f (spacetimeOfTimeSpace t x)‖ ≤ C_pt * t / (1 + ‖x‖) ^ d :=
    ae_of_all _ h_pointwise

  -- Apply integral monotonicity
  have h_mono := integral_mono_of_nonneg
    (f := fun x => ‖f (spacetimeOfTimeSpace t x)‖)
    (g := fun x => C_pt * t / (1 + ‖x‖) ^ d)
    (ae_of_all _ (fun x => norm_nonneg _))
    h_bound_int
    h_ae_bound

  -- Pull out constants: ∫ (C_pt * t) / (1 + ‖x‖)^d = (C_pt * t) * ∫ 1 / (1 + ‖x‖)^d
  have h_factor : ∫ x : SpatialCoords d, C_pt * t / (1 + ‖x‖) ^ d = C_pt * t * K := by
    have h_eq : (fun x : SpatialCoords d => C_pt * t / (1 + ‖x‖) ^ d) =
                (fun x : SpatialCoords d => (C_pt * t) * (1 / (1 + ‖x‖) ^ d)) := by ext x; ring
    rw [h_eq]
    simp only [← smul_eq_mul, integral_smul]
    rfl

  -- Combine inequalities
  calc spatialNormIntegral f t
      = ∫ x : SpatialCoords d, ‖f (spacetimeOfTimeSpace t x)‖ := rfl
    _ ≤ ∫ x : SpatialCoords d, C_pt * t / (1 + ‖x‖) ^ d := h_mono
    _ = C_pt * t * K := h_factor
    _ ≤ C_pt * t * (K + 1) := by nlinarith [mul_pos hC_pt_pos ht]
    _ = C_pt * (K + 1) * t := by ring

end TimeSlice


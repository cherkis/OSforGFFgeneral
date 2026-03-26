/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
import OSforGFFin3D.Euclidean
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Data.Real.Basic

/-!
# Modified Bessel Function K

This file defines the modified Bessel function K(ν,z) via its integral representation
and establishes key properties needed for the free covariance in AQFT.

## Main definitions

* `besselK` - The modified Bessel function K(ν,z) = ∫₀^∞ exp(-z cosh(t)) cosh(ν t) dt
* `besselKhalf` - The special case K_{1/2}(z), which is the kernel for the 3D spacetime covariance

## Main results

* `besselK_pos` - K(ν,z) > 0 for z > 0
* `besselK_asymptotic` - Bound K(ν,z) ≤ ((sinh ν)/ν + 2) · exp(-z) for z ≥ 1, 0 < ν ≤ 1
* `schwingerIntegral_eq_besselK` - Identity connecting the Schwinger integral to K(ν,mr)

## Notes

The cosh integral representation is particularly useful because:
1. It's manifestly real and positive for positive arguments
2. The integrand decays exponentially in t for any z > 0
3. It directly shows the analytic structure in z

For the massive scalar field in 3D Euclidean space, the exact formula is:
  C(x,y) = exp(- m |x-y|) / (4π |x-y|)
-/

open MeasureTheory Set Filter Asymptotics Real

/-- The modified Bessel function K(ν,z) via cosh integral representation.
  K(ν,z) = ∫₀^∞ exp(-z cosh(t)) cosh(ν * t) dt
    This is well-defined and positive for z > 0. -/
noncomputable def besselK (ν z : ℝ) : ℝ :=
  ∫ t : ℝ in Ici 0, exp (-z * cosh t) * cosh (ν * t)

/-- The modified Bessel function K_{1/2}(z), the kernel for the 3D spacetime covariance.
    besselKhalf z = besselK (1/2) z = ∫₀^∞ exp(-z cosh(t)) cosh(t/2) dt -/
noncomputable def besselKhalf (z : ℝ) : ℝ := besselK (1/2) z

private lemma cosh_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) : cosh x ≤ exp x := by
  rw [cosh_eq, div_le_iff₀' two_pos, two_mul, add_le_add_iff_left,
    ← mul_le_mul_iff_left₀ (exp_pos x), exp_neg]
  rw [inv_mul_cancel₀ (exp_ne_zero x), ← exp_add, one_le_exp_iff]
  linarith

private lemma cosh_mul_le_exp_abs_mul {ν t : ℝ} (ht : 0 ≤ t) :
    cosh (ν * t) ≤ exp (|ν| * t) := by
  have h_nonneg : 0 ≤ |ν| * t := mul_nonneg (abs_nonneg ν) ht
  calc
    cosh (ν * t) = cosh |ν * t| := by
      by_cases h : 0 ≤ ν * t
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg (lt_of_not_ge h), cosh_neg]
    _ = cosh (|ν| * t) := by rw [abs_mul, abs_of_nonneg ht]
    _ ≤ exp (|ν| * t) := cosh_le_exp_of_nonneg h_nonneg

private lemma cosh_mul_le_exp_of_nonneg_of_le_one {ν t : ℝ}
    (hν_nonneg : 0 ≤ ν) (hν_le : ν ≤ 1) (ht : 0 ≤ t) :
    cosh (ν * t) ≤ exp t := by
  calc
    cosh (ν * t) ≤ exp (|ν| * t) := cosh_mul_le_exp_abs_mul ht
    _ = exp (ν * t) := by rw [abs_of_nonneg hν_nonneg]
    _ ≤ exp (1 * t) := exp_le_exp.mpr (mul_le_mul_of_nonneg_right hν_le ht)
    _ = exp t := by simp

-- The Bessel-K integrand is integrable on `(0, ∞)` because the exponential term
-- decays super-exponentially and dominates the `cosh (ν * t)` growth.
private lemma besselK_integrableOn_Ioi {ν z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun t : ℝ => exp (-z * cosh t) * cosh (ν * t)) (Ioi 0) volume := by
  set f : ℝ → ℝ := fun t => exp (-z * cosh t) * cosh (ν * t) with hf_def
  have hf_cont : Continuous f := by
    apply Continuous.mul
    · exact continuous_exp.comp (continuous_const.mul continuous_cosh)
    · exact continuous_cosh.comp (continuous_const.mul continuous_id)
  have hf_nonneg : ∀ t, 0 ≤ f t := fun t => by
    apply mul_nonneg (exp_nonneg _) (cosh_pos (ν * t)).le
  apply integrable_of_isBigO_exp_neg (b := 1) one_pos hf_cont.continuousOn
  rw [isBigO_iff]
  use 1
  have h_ratio_tendsto : Tendsto (fun t => f t / exp (-t)) atTop (nhds 0) := by
    have h_eq : ∀ t, f t / exp (-t) = cosh (ν * t) * exp (t - z * cosh t) := by
      intro t
      simp only [f]
      field_simp
      rw [mul_comm, ← exp_add]
      ring_nf
    simp_rw [h_eq]
    have hbound : ∀ t, 0 ≤ t →
        cosh (ν * t) * exp (t - z * cosh t) ≤ exp ((|ν| + 1) * t - z * exp t / 2) := by
      intro t ht
      have h_cosh_ge : cosh t ≥ exp t / 2 := by
        rw [cosh_eq]
        have : exp (-t) ≥ 0 := exp_nonneg _
        linarith
      calc cosh (ν * t) * exp (t - z * cosh t)
          ≤ exp (|ν| * t) * exp (t - z * cosh t) := by
              apply mul_le_mul_of_nonneg_right (cosh_mul_le_exp_abs_mul ht) (exp_nonneg _)
        _ ≤ exp (|ν| * t) * exp (t - z * (exp t / 2)) := by
              apply mul_le_mul_of_nonneg_left _ (exp_nonneg _)
              apply exp_le_exp.mpr
              have : -z * cosh t ≤ -z * (exp t / 2) := by
                apply mul_le_mul_of_nonpos_left h_cosh_ge (by linarith)
              linarith
        _ = exp ((|ν| + 1) * t - z * exp t / 2) := by
              rw [← exp_add]
              ring_nf
    have h_exp_to_zero : Tendsto (fun t => exp ((|ν| + 1) * t - z * exp t / 2))
        atTop (nhds 0) := by
      apply tendsto_exp_atBot.comp
      have hexp_inf : Tendsto (fun t : ℝ => z * exp t / 2) atTop atTop := by
        apply Tendsto.atTop_div_const (by linarith : (0 : ℝ) < 2)
        exact Tendsto.const_mul_atTop hz tendsto_exp_atTop
      have h_ratio : Tendsto (fun t : ℝ => t / exp t) atTop (nhds 0) := by
        have h := tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
        simp only [pow_one] at h
        convert h using 1
        ext t
        rw [exp_neg, div_eq_mul_inv]
      have h_scaled : Tendsto (fun t : ℝ => 2 * (|ν| + 1) / z * (t / exp t)) atTop
          (nhds (2 * (|ν| + 1) / z * 0)) :=
        h_ratio.const_mul (2 * (|ν| + 1) / z)
      simp only [mul_zero] at h_scaled
      have h_shifted : Tendsto (fun t : ℝ => 2 * (|ν| + 1) / z * (t / exp t) - 1)
          atTop (nhds (-1)) := by
        convert h_scaled.sub_const 1 using 1
        simp
      have h_prod : Tendsto
          (fun t : ℝ => (z * exp t / 2) * (2 * (|ν| + 1) / z * (t / exp t) - 1)) atTop atBot :=
        Tendsto.atTop_mul_neg (by norm_num : (-1 : ℝ) < 0) hexp_inf h_shifted
      convert h_prod using 1
      ext t
      field_simp
    have hpos : ∀ t, 0 ≤ cosh (ν * t) * exp (t - z * cosh t) := by
      intro t
      apply mul_nonneg (cosh_pos (ν * t)).le (exp_nonneg _)
    refine squeeze_zero' (Eventually.of_forall hpos) ?_ h_exp_to_zero
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact hbound t ht
  have h_eventually_le : ∀ᶠ t in atTop, f t ≤ exp (-1 * t) := by
    have h1 : ∀ᶠ t in atTop, |f t / exp (-t)| < 1 := by
      have := Metric.tendsto_nhds.mp h_ratio_tendsto 1 one_pos
      filter_upwards [this] with t ht
      simp only [Real.dist_eq, sub_zero] at ht
      exact ht
    filter_upwards [h1] with t ht
    have hgt : 0 < exp (-t) := exp_pos _
    rw [abs_lt] at ht
    have hle : f t / exp (-t) < 1 := ht.2
    have : f t < exp (-t) := (div_lt_one hgt).mp hle
    simp only [neg_mul, one_mul]
    linarith
  filter_upwards [h_eventually_le] with t ht
  rw [Real.norm_of_nonneg (hf_nonneg t), Real.norm_of_nonneg (exp_nonneg _)]
  simp only [one_mul]
  exact ht

private lemma exp_mul_exp_neg_cosh_integrableOn_Ioi (ν z : ℝ) (hz : 0 < z) :
    IntegrableOn (fun u => exp (ν * u) * exp (-z * cosh u)) (Ioi 0) := by
  apply integrable_of_isBigO_exp_neg (a := 0) (b := 1)
  · exact one_pos
  · apply ContinuousOn.mul
    · exact (continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn
    · exact (continuous_exp.comp (continuous_const.mul continuous_cosh)).continuousOn
  · apply Asymptotics.IsBigO.of_bound 1
    set cutoff : ℝ := max 4 (4 * (|ν| + 1) / z)
    filter_upwards [eventually_ge_atTop cutoff] with u hu
    simp only [Real.norm_eq_abs, one_mul, neg_mul]
    rw [abs_of_pos (mul_pos (exp_pos _) (exp_pos _))]
    rw [abs_of_pos (exp_pos _)]
    have hu4 : u ≥ 4 := le_trans (le_max_left _ _) hu
    have hucut : u ≥ 4 * (|ν| + 1) / z := le_trans (le_max_right _ _) hu
    have hzu : z * u ≥ 4 * (|ν| + 1) := by
      calc z * u ≥ z * (4 * (|ν| + 1) / z) := by nlinarith [hucut]
        _ = 4 * (|ν| + 1) := by field_simp [hz.ne']
    have h_cosh_eq : cosh u = (exp u + exp (-u)) / 2 := cosh_eq u
    have h_cosh_lower : cosh u ≥ exp u / 2 := by
      rw [h_cosh_eq]
      have := exp_pos (-u)
      linarith
    have h_exp_ge_usq : exp u ≥ u ^ 2 / 2 := by
      have h_exp1 : exp 1 > 2.7 := by
        have := Real.exp_one_gt_d9
        linarith
      have h_exp2 : exp 2 > 7 := by
        have h : exp 2 = exp 1 * exp 1 := by rw [← exp_add]; norm_num
        nlinarith [h]
      have h_exp4 : exp 4 > 49 := by
        have h : exp 4 = exp 2 * exp 2 := by rw [← exp_add]; norm_num
        nlinarith [h]
      have h_strict_mono : StrictMonoOn (fun v => exp v - v ^ 2 / 2) (Set.Ici 4) := by
        apply strictMonoOn_of_deriv_pos (convex_Ici 4)
        · exact (continuous_exp.sub (continuous_pow 2 |>.div_const 2)).continuousOn
        · intro x hx
          simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi] at hx
          have hderiv : deriv (fun v => exp v - v ^ 2 / 2) x = exp x - x := by
            have hd1 : DifferentiableAt ℝ (fun v => exp v) x := differentiableAt_exp
            have hd2 : DifferentiableAt ℝ (fun v => v ^ 2 / 2) x :=
              (differentiableAt_pow 2).div_const 2
            have heq : (fun v => exp v - v ^ 2 / 2) = (fun v => exp v) - (fun v => v ^ 2 / 2) := by
              ext v
              simp [sub_eq_add_neg]
            rw [heq, deriv_sub hd1 hd2, deriv_div_const]
            simp only [Real.deriv_exp]
            have hpow : deriv (fun v : ℝ => v ^ (2 : ℕ)) x = (2 : ℝ) * x ^ (2 - 1) := deriv_pow_field 2
            simp only [pow_one, Nat.add_one_sub_one] at hpow
            rw [hpow]
            ring
          rw [hderiv]
          have := add_one_le_exp x
          linarith
      by_cases hu4eq : u = 4
      · simp only [hu4eq]
        linarith [h_exp4]
      · have hug4 : u > 4 := lt_of_le_of_ne hu4 (Ne.symm hu4eq)
        have h_at_4 : exp 4 - (4 : ℝ) ^ 2 / 2 > 0 := by
          norm_num
          linarith [h_exp4]
        have := h_strict_mono (Set.self_mem_Ici) (le_of_lt hug4) hug4
        linarith
    have h_cosh_bound : (|ν| + 1) * u ≤ z * cosh u := by
      have h1 : z * cosh u ≥ z * (exp u / 2) := by nlinarith [h_cosh_lower]
      have h2 : z * (exp u / 2) ≥ z * (u ^ 2 / 2) / 2 := by nlinarith [h_exp_ge_usq, hz]
      have h3 : z * (u ^ 2 / 2) / 2 = z * u ^ 2 / 4 := by ring
      have h4 : z * u ^ 2 / 4 = (z * u / 4) * u := by ring
      have h5 : z * u / 4 ≥ |ν| + 1 := by linarith [hzu]
      have h6 : (z * u / 4) * u ≥ (|ν| + 1) * u := by
        have hu_nonneg : 0 ≤ u := by linarith
        nlinarith
      linarith
    have hu_nonneg : 0 ≤ u := by linarith
    have hνu_le : ν * u ≤ |ν| * u := by
      have hleabs : ν * u ≤ |ν * u| := le_abs_self (ν * u)
      rw [abs_mul, abs_of_nonneg hu_nonneg] at hleabs
      exact hleabs
    have h_ineq : ν * u - z * cosh u ≤ -u := by
      have : ν * u + u ≤ z * cosh u := by
        have habs : |ν| * u + u ≤ z * cosh u := by
          simpa [mul_add, add_mul, one_mul] using h_cosh_bound
        linarith
      linarith
    calc exp (ν * u) * exp (-(z * cosh u))
        = exp (ν * u + (-(z * cosh u))) := by rw [← exp_add]
      _ = exp (ν * u - z * cosh u) := by ring_nf
      _ ≤ exp (-u) := exp_le_exp.mpr h_ineq

private lemma exp_tail_model_integrable_integral (z : ℝ) (hz : 0 < z) :
    IntegrableOn (fun t : ℝ => exp t * exp (-z * exp t / 2)) (Ioi 1) ∧
  ∫ t in Ioi 1, exp t * exp (-z * exp t / 2) = 2 / z * exp (-z * exp 1 / 2) := by
  set g : ℝ → ℝ := fun t => exp t * exp (-z * exp t / 2)
  set F : ℝ → ℝ := fun t => -2 / z * exp (-z * exp t / 2)
  have hg_nonneg : ∀ t, 0 ≤ g t := fun t => mul_nonneg (exp_nonneg _) (exp_nonneg _)
  have hF_deriv : ∀ t, HasDerivAt F (g t) t := by
    intro t
    have h1 : HasDerivAt (fun s => -z * exp s / 2) (-z / 2 * exp t) t := by
      have := (hasDerivAt_exp t).const_mul (-z / 2)
      convert this using 1
      funext s
      ring
    have h2 :
        HasDerivAt (fun s => exp (-z * exp s / 2))
          (exp (-z * exp t / 2) * (-z / 2 * exp t)) t :=
      (hasDerivAt_exp _).comp t h1
    simp only [g]
    convert h2.const_mul (-2 / z) using 1
    field_simp
  have hF_cont : ContinuousWithinAt F (Ici 1) 1 := by
    apply ContinuousAt.continuousWithinAt
    exact continuousAt_const.mul
      (continuous_exp.continuousAt.comp
        ((continuousAt_const.mul continuous_exp.continuousAt).div_const _))
  have hF_tendsto : Tendsto F atTop (nhds 0) := by
    have h1 : Tendsto (fun t => exp (-z * exp t / 2)) atTop (nhds 0) := by
      apply tendsto_exp_atBot.comp
      have h3 : Tendsto (fun t : ℝ => z / 2 * exp t) atTop atTop :=
        tendsto_exp_atTop.const_mul_atTop (by linarith : 0 < z / 2)
      have h4 : Tendsto (fun t => -(z / 2 * exp t)) atTop atBot :=
        Filter.tendsto_neg_atTop_atBot.comp h3
      convert h4 using 1
      ext t
      ring
    simpa [F] using h1.const_mul (-2 / z)
  have hg_int : IntegrableOn g (Ioi 1) := by
    apply integrableOn_Ioi_deriv_of_nonneg hF_cont
    · intro x _
      exact hF_deriv x
    · intro x _
      exact hg_nonneg x
    · exact hF_tendsto
  have h_int_g : ∫ t in Ioi 1, g t = 2 / z * exp (-z * exp 1 / 2) := by
    rw [integral_Ioi_of_hasDerivAt_of_tendsto hF_cont (fun x _ => hF_deriv x) hg_int hF_tendsto]
    simp only [F]
    ring
  constructor
  · simpa [g] using hg_int
  · simpa [g] using h_int_g

private lemma ici_zero_eq_Icc_zero_one_union_Ici_one : Ici (0 : ℝ) = Icc 0 1 ∪ Ici 1 := by
  ext x
  simp only [mem_Ici, mem_union, mem_Icc]
  constructor
  · intro hx
    rcases le_or_gt x 1 with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr h.le
  · rintro (⟨hx, _⟩ | hx)
    · exact hx
    · linarith

private lemma ici_zero_eq_Ico_zero_one_union_Ici_one : Ici (0 : ℝ) = Ico 0 1 ∪ Ici 1 := by
  ext x
  simp only [mem_Ici, mem_union, mem_Ico]
  constructor
  · intro hx
    rcases lt_or_ge x 1 with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr h
  · rintro (⟨hx, _⟩ | hx)
    · exact hx
    · linarith

private lemma disjoint_Ico_zero_one_Ici_one : Disjoint (Ico (0 : ℝ) 1) (Ici 1) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  simp only [mem_Ico] at hx
  simp only [mem_Ici] at hx'
  linarith

private lemma setIntegral_Ici_eq_Ioi_one (f : ℝ → ℝ) :
    ∫ t in Ici 1, f t = ∫ t in Ioi 1, f t :=
  setIntegral_congr_set Ioi_ae_eq_Ici.symm

private lemma setIntegral_Ico_eq_Icc_zero_one (f : ℝ → ℝ) :
    ∫ t in Ico 0 1, f t = ∫ t in Icc 0 1, f t :=
  setIntegral_congr_set Ico_ae_eq_Icc

/-- K(ν,z) is positive for z > 0. -/
lemma besselK_pos (ν z : ℝ) (hz : 0 < z) : 0 < besselK ν z := by
  unfold besselK
  -- The integrand f(t) = exp(-z cosh(t)) * cosh(ν * t) is strictly positive for all t
  set f : ℝ → ℝ := fun t => exp (-z * cosh t) * cosh (ν * t) with hf_def
  -- f is nonnegative (actually positive)
  have hf_nonneg : ∀ t, 0 ≤ f t := fun t => by
    apply mul_nonneg (exp_nonneg _) (cosh_pos (ν * t)).le
  have hf_pos : ∀ t, 0 < f t := fun t => by
    apply mul_pos (exp_pos _) (cosh_pos (ν * t))
  -- f is continuous
  have hf_cont : Continuous f := by
    apply Continuous.mul
    · exact continuous_exp.comp (continuous_const.mul continuous_cosh)
    · exact continuous_cosh.comp (continuous_const.mul continuous_id)
  have hf_int : IntegrableOn f (Ici 0) volume := by
    have h_int_Ioi : IntegrableOn f (Ioi 0) volume := by
      simpa [f, hf_def] using (besselK_integrableOn_Ioi (ν := ν) (z := z) hz)
    exact h_int_Ioi.congr_set_ae Ioi_ae_eq_Ici.symm
  -- The support of f intersected with [0, ∞) is [0, ∞) since f is everywhere positive
  have h_support : Function.support f ∩ Ici 0 = Ici 0 := by
    ext t
    simp only [Function.mem_support, mem_inter_iff, mem_Ici, ne_eq]
    constructor
    · intro ⟨_, ht⟩; exact ht
    · intro ht; exact ⟨(hf_pos t).ne', ht⟩
  -- The measure of [0, ∞) is positive (it's infinite, actually)
  have h_meas_pos : 0 < volume (Function.support f ∩ Ici 0) := by
    rw [h_support, Real.volume_Ici]
    exact ENNReal.zero_lt_top
  -- Apply the positivity criterion
  rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae
      (Eventually.of_forall (fun t => hf_nonneg t)) hf_int]
  exact h_meas_pos


/-- K(ν,.) is continuous on (0, ∞). This follows from dominated convergence since the integrand
    z ↦ exp(-z cosh(t)) cosh(ν t) is continuous in z and dominated by exp(-ε cosh(t)) cosh(ν t)
    for z ≥ ε, which is integrable.

    The formal proof uses MeasureTheory.continuousOn_of_dominated_of_compact:
    for z in compact K ⊆ (0, ∞), bound by exp(-min(K) * cosh(t)) * cosh(ν t). -/
lemma besselK_continuousOn {ν : ℝ} : ContinuousOn (besselK ν) (Ioi 0) := by
  -- Show ContinuousAt at each z₀ > 0 using dominated convergence
  rw [isOpen_Ioi.continuousOn_iff]
  intro z₀ hz₀
  simp only [mem_Ioi] at hz₀
  unfold besselK
  -- Use bound: exp(-(z₀/2) * cosh t) * cosh(ν t) for z ≥ z₀/2
  set bound : ℝ → ℝ := fun t => exp (-(z₀/2) * cosh  t) * cosh (ν * t) with hbound_def
  apply MeasureTheory.continuousAt_of_dominated (bound := bound)
  -- AEStronglyMeasurable for z near z₀
  · filter_upwards with z
    apply (((continuous_exp.comp (continuous_const.mul continuous_cosh)).mul
      (continuous_cosh.comp (continuous_const.mul continuous_id))).aestronglyMeasurable).restrict
  -- Dominated by bound for z in neighborhood of z₀
  · have hne : Ioi (z₀/2) ∈ nhds z₀ := Ioi_mem_nhds (by linarith : z₀/2 < z₀)
    filter_upwards [hne] with z hz
    filter_upwards with t
    rw [Real.norm_of_nonneg (mul_nonneg (exp_nonneg _) (cosh_pos (ν * t)).le)]
    simp only [mem_Ioi] at hz
    -- exp(-z * cosh t) ≤ exp(-(z₀/2) * cosh t) since z > z₀/2 and cosh t > 0
    apply mul_le_mul_of_nonneg_right _ (cosh_pos (ν * t)).le
    apply exp_le_exp.mpr
    -- Need: -z * cosh t ≤ -(z₀/2) * cosh t, i.e., (z₀/2) * cosh t ≤ z * cosh t
    have hcosh : 0 < cosh t := cosh_pos t
    nlinarith [hcosh, hz]
  -- Bound is integrable (same proof as in besselK_pos)
  · have hz₀' : 0 < z₀ / 2 := by linarith
    have hcont : Continuous bound := (continuous_exp.comp (continuous_const.mul continuous_cosh)).mul (continuous_cosh.comp (continuous_const.mul continuous_id))
    rw [ici_zero_eq_Icc_zero_one_union_Ici_one]
    apply IntegrableOn.union
    · exact hcont.continuousOn.integrableOn_compact isCompact_Icc
    · have h_Ioi0 : IntegrableOn bound (Ioi 0) volume := by
        simpa [bound, hbound_def] using
          (besselK_integrableOn_Ioi (ν := ν) (z := z₀ / 2) hz₀')
      have h_Ioi1 : IntegrableOn bound (Ioi 1) volume :=
        h_Ioi0.mono_set (fun x hx => by simp only [mem_Ioi] at hx ⊢; linarith)
      exact h_Ioi1.congr_set_ae Ioi_ae_eq_Ici.symm
  -- Integrand is continuous in z for each t
  · filter_upwards with t
    apply Continuous.continuousAt
    apply Continuous.mul
    · exact continuous_exp.comp (continuous_id.neg.mul continuous_const)
    · exact continuous_const

/-- K(ν,.) has exponential decay: K(ν,z) ≤ ((sinh ν)/ν + 2) · exp(-z) for z ≥ 1 and 0 < ν ≤ 1.
    This bound is sufficient for proving integrability of the free covariance kernel.
    The proof uses the same technique as besselK_mul_self_le but for z ≥ 1. -/
lemma besselK_asymptotic (νpos : 0 < ν) (νle : ν ≤ 1) (z : ℝ) (hz : 1 ≤ z) :
    besselK ν z ≤ ((sinh ν )/ν  + 2) * exp (-z) := by
  unfold besselK
  set f : ℝ → ℝ := fun t => exp (-z * cosh t) * cosh (ν * t) with hf_def
  have hf_cont : Continuous f := (continuous_exp.comp (continuous_const.mul continuous_cosh)).mul (continuous_cosh.comp (continuous_const.mul continuous_id))
  have hf_nonneg : ∀ t, 0 ≤ f t := fun t => mul_nonneg (exp_nonneg _) (cosh_pos (ν * t)).le
  -- Split [0, ∞) = [0, 1] ∪ [1, ∞)
  have hf_int_Icc : IntegrableOn f (Icc 0 1) := hf_cont.continuousOn.integrableOn_compact isCompact_Icc
  have hf_int_Ici1 : IntegrableOn f (Ici 1) := by
    have h_Ioi0 : IntegrableOn f (Ioi 0) volume := by
      simpa [f, hf_def] using (besselK_integrableOn_Ioi (ν := ν) (z := z) (by linarith : 0 < z))
    exact h_Ioi0.mono_set (fun x hx => by simp only [mem_Ioi, mem_Ici] at *; linarith)
  -- Part 1: ∫₀^1 f ≤ exp(-z) sinh(ν) / ν since f(t) ≤ exp(-z) cosh(ν * t) and cosh(ν * t) ≥ 1
  have h_part1 : ∫ t in Icc 0 1, f t ≤ rexp (-z) * (sinh ν) / ν  := by
    have h_pointwise : ∀ t ∈ Icc (0:ℝ) 1, f t ≤ rexp (-z) * cosh (ν * t) := by
      intro t ⟨ht0, ht1⟩
      simp only [hf_def]
      have h1 : 1 ≤ cosh t := one_le_cosh t
      have h2 : -z * cosh t ≤ -z := by nlinarith
      exact mul_le_mul_of_nonneg_right (exp_le_exp.mpr h2) (cosh_pos (ν *t)).le
    have h_int_bound : ∫ t in Icc 0 1, f t ≤ ∫ t in Icc 0 1, exp (-z) * cosh (ν * t) := by
      apply setIntegral_mono_on hf_int_Icc _ measurableSet_Icc h_pointwise
      exact (continuous_const.mul (continuous_cosh.comp (continuous_const.mul (continuous_id)))).integrableOn_Icc
    have h_val : ∫ t in Icc 0 1, exp (-z) * cosh (ν * t) = exp (-z) * (sinh ν)/ ν := by
      -- Compute integral of exp(-z) * cosh(ν*t) on [0,1] via FTC
      -- Antiderivative for cosh(ν*t): F(t) = sinh(ν * t) / ν
      have hν_ne : ν ≠ 0 := ne_of_gt νpos
      have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (by norm_num : (0:ℝ) ≤ 1)
        (show ContinuousOn (fun t => sinh (ν * t) / ν) (Icc 0 1) from
          ((continuous_sinh.comp (continuous_const.mul continuous_id)).div_const ν).continuousOn)
        (fun x _ => by
          have h1 : HasDerivAt (fun t => ν * t) ν x := by
            simpa [mul_comm] using (hasDerivAt_id x).const_mul ν
          have h2 : HasDerivAt (fun t => sinh (ν * t)) (cosh (ν * x) * ν) x :=
            (hasDerivAt_sinh (ν * x)).comp x h1
          have h3 : HasDerivAt (fun t => sinh (ν * t) / ν) (cosh (ν * x)) x := by
            have h3' := h2.div_const ν; convert h3' using 1; field_simp
          exact h3.hasDerivWithinAt)
        ((continuous_cosh.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 1)
      simp only [mul_one, mul_zero, sinh_zero, zero_div, sub_zero] at h
      rw [MeasureTheory.integral_const_mul]
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
      have h_base : ∫ x in 0..1, cosh (ν * x) = sinh ν / ν := by
        simpa using h
      rw [h_base]
      ring
    linarith
  -- Part 2: ∫₁^∞ f ≤ 2 exp(-z) using the same FTC argument as in besselK_mul_self_le
  have h_part2 : ∫ t in Ici 1, f t ≤ 2 * exp (-z) := by
    set g : ℝ → ℝ := fun t => exp t * exp (-z * exp t / 2)
    have h_bound' : ∀ t ≥ (1:ℝ), f t ≤ g t := by
      intro t ht; simp only [hf_def, g]
      have h_cosh_ge : cosh t ≥ exp t / 2 := by rw [cosh_eq]; linarith [exp_nonneg (-t)]
      have h_cosh_nu_le : cosh (ν * t) ≤ exp t := by
        exact cosh_mul_le_exp_of_nonneg_of_le_one νpos.le νle (by linarith)
      calc exp (-z * cosh t) * cosh (ν * t)
          ≤ exp (-z * (exp t / 2)) * cosh (ν * t) := by
              apply mul_le_mul_of_nonneg_right _ (cosh_pos (ν * t)).le
              apply exp_le_exp.mpr
              have : -z * cosh t ≤ -z * (exp t / 2) := by
                apply mul_le_mul_of_nonpos_left h_cosh_ge
                linarith
              exact this
        _ = exp (-z * exp t / 2) * cosh (ν * t) := by ring_nf
        _ ≤ exp (-z * exp t / 2) * exp t := by
          apply mul_le_mul_of_nonneg_left h_cosh_nu_le (exp_nonneg _)
        _ = g t := by simp [g]; ring
    have h_tail := exp_tail_model_integrable_integral z (by linarith : 0 < z)
    have hg_int : IntegrableOn g (Ioi 1) := by simpa [g] using h_tail.1
    have h_int_g : ∫ t in Ioi 1, g t = 2 / z * exp (-z * exp 1 / 2) := by
      simpa [g] using h_tail.2
    have hf_int_Ioi : IntegrableOn f (Ioi 1) := hf_int_Ici1.mono_set Ioi_subset_Ici_self
    have h_mono : ∫ t in Ioi 1, f t ≤ ∫ t in Ioi 1, g t := by
      apply setIntegral_mono_on hf_int_Ioi hg_int measurableSet_Ioi (fun t ht => h_bound' t (le_of_lt ht))
    calc ∫ t in Ici 1, f t = ∫ t in Ioi 1, f t := setIntegral_Ici_eq_Ioi_one f
      _ ≤ ∫ t in Ioi 1, g t := h_mono
      _ = 2/z * exp (-z * exp 1 / 2) := h_int_g
      _ ≤ 2 * exp (-z) := by
          have he : exp 1 > 0 := exp_pos 1
          have hz' : z > 0 := by linarith
          -- Key: exp 1 ≥ 2 from 1 + 1 ≤ exp 1 (using add_one_le_exp)
          have he2 : 2 ≤ exp (1:ℝ) := by linarith [add_one_le_exp (1:ℝ)]
          -- Therefore exp 1 / 2 ≥ 1, so z * exp 1 / 2 ≥ z, so -z * exp 1 / 2 ≤ -z
          have h_exp_bound : exp (-z * exp 1 / 2) ≤ exp (-z) := by
            apply exp_le_exp.mpr
            have h1 : z * exp 1 / 2 ≥ z * 2 / 2 := by nlinarith
            linarith
          -- 2/z ≤ 2 since z ≥ 1
          have hz_bound : 2 / z ≤ 2 := by
            have h1 : 2 ≤ 2 * z := by linarith
            exact (div_le_iff₀ hz').mpr h1
          calc 2/z * exp (-z * exp 1 / 2)
              ≤ 2/z * exp (-z) := by
                apply mul_le_mul_of_nonneg_left h_exp_bound
                positivity
            _ ≤ 2 * exp (-z) := by
                apply mul_le_mul_of_nonneg_right hz_bound
                positivity
  -- Combine using Ico for proper disjointness
  have hf_int_Ico : IntegrableOn f (Ico 0 1) := hf_int_Icc.mono_set Ico_subset_Icc_self
  rw [ici_zero_eq_Ico_zero_one_union_Ici_one,
    setIntegral_union disjoint_Ico_zero_one_Ici_one measurableSet_Ici hf_int_Ico hf_int_Ici1]
  calc (∫ t in Ico 0 1, f t) + (∫ t in Ici 1, f t)
      = (∫ t in Icc 0 1, f t) + (∫ t in Ici 1, f t) := by
          rw [setIntegral_Ico_eq_Icc_zero_one f]
    _ ≤ exp (-z) * (sinh ν) / ν + 2 * exp (-z) := add_le_add h_part1 h_part2
    _ = ((sinh ν) / ν + 2) * exp (-z) := by ring


/-- For z ∈ (0, 1] and ν ∈ (0, 1], we have z · K(ν,z) ≤ cosh(ν) + 2.
    This follows from splitting the integral at t = 1:
    - On [0,1]: z · ∫₀¹ exp(-z cosh t) cosh(νt) dt ≤ z · cosh(ν) ≤ cosh(ν)
    - On [1,∞): z · ∫₁^∞ exp(-z cosh t) cosh(νt) dt ≤ 2 (via exponential bound, using ν ≤ 1) -/
lemma besselK_mul_self_le {ν : ℝ} (νpos : 0 < ν) (νle : ν ≤ 1) (z : ℝ) (hz : 0 < z) (hz_le : z ≤ 1) :
    z * besselK ν z ≤ cosh ν + 2 := by
  unfold besselK
  set f : ℝ → ℝ := fun t => exp (-z * cosh t) * cosh (ν * t) with hf_def
  -- f is continuous and nonnegative
  have hf_cont : Continuous f := (continuous_exp.comp (continuous_const.mul continuous_cosh)).mul
    (continuous_cosh.comp (continuous_const.mul continuous_id))
  have hf_nonneg : ∀ t, 0 ≤ f t := fun t => mul_nonneg (exp_nonneg _) (cosh_pos (ν * t)).le
  -- Split [0,∞) = [0,1] ∪ [1,∞)
  -- Integrability on both parts
  have hf_int_Icc : IntegrableOn f (Icc 0 1) := hf_cont.continuousOn.integrableOn_compact isCompact_Icc
  have hf_int_Ici : IntegrableOn f (Ici 1) := by
    have h_Ioi0 : IntegrableOn f (Ioi 0) volume := by
      simpa [f, hf_def] using (besselK_integrableOn_Ioi (ν := ν) (z := z) hz)
    exact h_Ioi0.mono_set (fun x hx => by simp only [mem_Ioi, mem_Ici] at *; linarith)
  -- Part 1: Bound on [0,1]
  have h_part1 : ∫ t in Icc 0 1, f t ≤ cosh ν := by
    -- f(t) ≤ cosh(ν) on [0,1] since exp(-z cosh t) ≤ 1 and cosh(νt) ≤ cosh(ν)
    have h_pointwise : ∀ t ∈ Icc (0:ℝ) 1, f t ≤ cosh ν := by
      intro t ⟨ht0, ht1⟩
      simp only [hf_def]
      have h_exp_le : exp (-z * cosh t) ≤ 1 := by
        rw [exp_le_one_iff]; nlinarith [cosh_pos t]
      have h_cosh_le : cosh (ν * t) ≤ cosh ν := by
        -- cosh is even and increasing on [0,∞), and |ν * t| ≤ |ν| for t ∈ [0,1]
        rw [cosh_le_cosh]
        rw [abs_of_nonneg (mul_nonneg νpos.le ht0), abs_of_pos νpos]
        nlinarith
      calc exp (-z * cosh t) * cosh (ν * t) ≤ 1 * cosh (ν * t) := by nlinarith [cosh_pos (ν * t)]
        _ ≤ cosh ν := by simp [h_cosh_le]
    have h_meas_finite : volume (Icc (0:ℝ) 1) < ⊤ := measure_Icc_lt_top
    have h_meas_ne_top : volume (Icc (0:ℝ) 1) ≠ ⊤ := h_meas_finite.ne
    have h_const_int : IntegrableOn (fun _ => cosh ν) (Icc (0:ℝ) 1) := integrableOn_const (hs := h_meas_ne_top)
    have h_mono : ∫ t in Icc 0 1, f t ≤ ∫ _ in Icc (0:ℝ) 1, cosh ν := by
      apply setIntegral_mono_on hf_int_Icc h_const_int measurableSet_Icc
      exact h_pointwise
    have h_const_val : ∫ _ in Icc (0:ℝ) 1, cosh ν = cosh ν := by
      rw [setIntegral_const, volume_real_Icc]
      simp only [sub_zero, max_eq_left (by linarith : (0:ℝ) ≤ 1), one_smul]
    linarith
  -- Part 2: Bound z * ∫₁^∞ f(t) dt ≤ 2
  -- Using cosh(νt) ≤ exp(t) (since ν ≤ 1) and cosh(t) ≥ exp(t)/2, we bound the integral
  have h_part2 : z * ∫ t in Ici 1, f t ≤ 2 := by
    -- Key bound: f(t) = exp(-z cosh t) * cosh(νt) ≤ exp(-z exp(t)/2) * exp(t)
    have h_bound : ∀ t ≥ 1, f t ≤ exp (-z * exp t / 2) * exp t := by
      intro t ht
      simp only [hf_def]
      have h_cosh_ge : cosh t ≥ exp t / 2 := by rw [cosh_eq]; linarith [exp_nonneg (-t)]
      -- cosh(νt) ≤ exp(νt) ≤ exp(t) since ν ≤ 1
      have h_cosh_nu_le : cosh (ν * t) ≤ exp t := by
        exact cosh_mul_le_exp_of_nonneg_of_le_one νpos.le νle (by linarith)
      have h_exp_eq : -z * (exp t / 2) = -z * exp t / 2 := by ring
      calc exp (-z * cosh t) * cosh (ν * t)
          ≤ exp (-z * (exp t / 2)) * cosh (ν * t) := by
            apply mul_le_mul_of_nonneg_right _ (cosh_pos (ν * t)).le
            apply exp_le_exp.mpr
            have : -z * cosh t ≤ -z * (exp t / 2) := by nlinarith
            exact this
        _ = exp (-z * exp t / 2) * cosh (ν * t) := by rw [h_exp_eq]
        _ ≤ exp (-z * exp t / 2) * exp t := by
            apply mul_le_mul_of_nonneg_left h_cosh_nu_le (exp_nonneg _)
    -- Define bounding function g(t) = exp(t) * exp(-z exp(t)/2) and its antiderivative
    set g : ℝ → ℝ := fun t => exp t * exp (-z * exp t / 2)
    -- Rewrite h_bound in terms of g
    have h_bound' : ∀ t ≥ (1:ℝ), f t ≤ g t := by
      intro t ht; simp only [g]; rw [mul_comm]; exact h_bound t ht
    have h_tail := exp_tail_model_integrable_integral z hz
    have hg_int : IntegrableOn g (Ioi 1) := by simpa [g] using h_tail.1
    have h_int_g : ∫ t in Ioi 1, g t = 2 / z * exp (-z * exp 1 / 2) := by
      simpa [g] using h_tail.2
    -- f is integrable on (1, ∞) by comparison with g
    have hf_int_Ioi : IntegrableOn f (Ioi 1) :=
      hf_int_Ici.mono_set (fun x hx => by exact mem_Ici_of_Ioi hx)
    have h_mono : ∫ t in Ioi 1, f t ≤ ∫ t in Ioi 1, g t := by
      apply setIntegral_mono_on hf_int_Ioi hg_int measurableSet_Ioi
      intro t ht; exact h_bound' t (le_of_lt ht)
    calc z * ∫ t in Ici 1, f t
        = z * ∫ t in Ioi 1, f t := by rw [setIntegral_Ici_eq_Ioi_one f]
      _ ≤ z * ∫ t in Ioi 1, g t := mul_le_mul_of_nonneg_left h_mono hz.le
      _ = z * (2 / z * exp (-z * exp 1 / 2)) := by rw [h_int_g]
      _ = 2 * exp (-z * exp 1 / 2) := by field_simp
      _ ≤ 2 * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
          rw [exp_le_one_iff]
          have he : exp 1 > 0 := exp_pos 1
          nlinarith
      _ = 2 := by ring
  -- Combine: Use Ico instead of Icc for proper disjointness
  have hf_int_Ico : IntegrableOn f (Ico 0 1) := hf_int_Icc.mono_set Ico_subset_Icc_self
  have h_part1' : z * ∫ t in Ico 0 1, f t ≤ cosh ν := by
    have h_int_le : ∫ t in Ico 0 1, f t ≤ cosh ν := by
      rw [setIntegral_Ico_eq_Icc_zero_one f]
      exact h_part1
    have h_z_mul_le : z * ∫ t in Ico 0 1, f t ≤ z * cosh ν :=
      mul_le_mul_of_nonneg_left h_int_le hz.le
    have h_z_cosh_le : z * cosh ν ≤ 1 * cosh ν := by nlinarith [cosh_pos ν]
    linarith
  have h_split : ∫ t in Ici 0, f t = (∫ t in Ico 0 1, f t) + (∫ t in Ici 1, f t) := by
    rw [ici_zero_eq_Ico_zero_one_union_Ici_one]
    exact setIntegral_union disjoint_Ico_zero_one_Ici_one measurableSet_Ici hf_int_Ico hf_int_Ici
  have h_distrib : z * ∫ t in Ici 0, f t = (z * ∫ t in Ico 0 1, f t) + (z * ∫ t in Ici 1, f t) := by
    rw [h_split, mul_add]
  rw [h_distrib]
  exact add_le_add h_part1' h_part2

/-- Near-origin bound for K(ν,z): K(ν,z) ≤ (cosh(ν) + 2)/z for z ∈ (0, 1] and ν ∈ (0, 1].
    This follows from z · K(ν,z) ≤ cosh(ν) + 2 (proved in besselK_mul_self_le). -/
lemma besselK_near_origin_bound {ν : ℝ} (νpos : 0 < ν) (νle : ν ≤ 1) (z : ℝ) (hz : 0 < z) (hz_small : z ≤ 1) :
    besselK ν z ≤ (cosh ν + 2) / z := by
  have h_bound := besselK_mul_self_le νpos νle z hz hz_small
  -- z * K(ν,z) ≤ cosh(ν) + 2, so K(ν,z) ≤ (cosh(ν) + 2) / z
  exact (le_div_iff₀' hz).mpr h_bound

private lemma radial_besselK_continuousOn {ν m : ℝ} (hm : 0 < m) :
    ContinuousOn (fun r => r ^ 2 * besselK ν (m * r)) (Ioi 0) := by
  apply ContinuousOn.mul (continuous_pow 2).continuousOn
  apply (besselK_continuousOn (ν := ν)).comp (continuous_mul_left m).continuousOn
  intro r hr
  simp only [mem_Ioi] at hr ⊢
  exact mul_pos hm hr

private lemma radial_besselK_aestronglyMeasurable_Ioc {ν m : ℝ} (hm : 0 < m) :
    AEStronglyMeasurable (fun r => r ^ 2 * besselK ν (m * r)) (volume.restrict (Ioc 0 (1 / m))) := by
  have hsub : Ioc 0 (1 / m) ⊆ Ioi 0 := fun r ⟨hr, _⟩ => hr
  exact (radial_besselK_continuousOn (ν := ν) hm).mono hsub |>.aestronglyMeasurable measurableSet_Ioc

private lemma radial_besselK_aestronglyMeasurable_Ioi {ν m : ℝ} (hm : 0 < m) :
    AEStronglyMeasurable (fun r => r ^ 2 * besselK ν (m * r)) (volume.restrict (Ioi (1 / m))) := by
  have hsub : Ioi (1 / m) ⊆ Ioi 0 := fun r hr => by
    simp only [mem_Ioi] at hr ⊢
    linarith [one_div_pos.mpr hm]
  exact (radial_besselK_continuousOn (ν := ν) hm).mono hsub |>.aestronglyMeasurable measurableSet_Ioi

private lemma radial_besselK_nonneg {ν m r : ℝ} (hm : 0 < m) (hr : 0 < r) :
    0 ≤ r ^ 2 * besselK ν (m * r) := by
  apply mul_nonneg (sq_nonneg r)
  exact (besselK_pos ν (m * r) (mul_pos hm hr)).le

/-- The radial integrand r² K(ν,mr) is integrable on (0, ∞) for m > 0 and ν ∈ (0, 1].

    **Mathematical justification:**
  - Near 0: the bound K(ν,mr) ≤ (cosh ν + 2) / (mr) gives r² K(ν,mr) ≤ (cosh ν + 2) r / m,
    which is integrable near 0
    - At ∞: K(ν,mr) ~ e^{-mr}/√(mr), so r² K(ν,mr) decays exponentially

    This is a key ingredient for showing the free covariance kernel is L¹. -/
lemma radial_besselK_integrable {ν : ℝ} (νpos : 0 < ν) (νle : ν ≤ 1) (m : ℝ) (hm : 0 < m) :
    IntegrableOn (fun r => r ^ 2 * besselK ν (m * r)) (Set.Ioi 0) volume := by
  -- Split (0, ∞) = (0, 1/m] ∪ (1/m, ∞)
  have h_split : Ioi (0 : ℝ) = Ioc 0 (1/m) ∪ Ioi (1/m) := by
    rw [Ioc_union_Ioi_eq_Ioi]
    positivity
  rw [h_split]
  apply IntegrableOn.union
  -- Part 1: Integrability on (0, 1/m]
  · -- Near origin: r² K(ν,mr) ≤ r² * ((cosh ν + 2)/(mr)) = (cosh ν + 2)*r/m
    -- For r ∈ (0, 1/m], we have mr ∈ (0, 1], so K(ν,mr) ≤ (cosh ν + 2)/(mr)
    -- The function (cosh ν + 2)*r/m is integrable on (0, 1/m]
    set C := cosh ν + 2 with hC_def
    have hC_pos : 0 < C := by simp only [hC_def]; linarith [cosh_pos ν]
    -- Bound: r² K(ν,mr) ≤ C * r / m for r ∈ (0, 1/m]
    have h_bound : ∀ r ∈ Ioc (0:ℝ) (1/m), r ^ 2 * besselK ν (m * r) ≤ C * r / m := by
      intro r ⟨hr_pos, hr_le⟩
      have hmr_pos : 0 < m * r := by positivity
      have hmr_le : m * r ≤ 1 := by
        calc m * r ≤ m * (1/m) := by nlinarith
          _ = 1 := by field_simp
      have h := besselK_near_origin_bound νpos νle (m * r) hmr_pos hmr_le
      calc r ^ 2 * besselK ν (m * r)
          ≤ r ^ 2 * (C / (m * r)) := by nlinarith [besselK_pos ν (m * r) hmr_pos]
        _ = C * r / m := by field_simp [ne_of_gt hr_pos, ne_of_gt hm]
    -- The bounding function C*r/m is integrable on (0, 1/m]
    have h_bound_int : IntegrableOn (fun r => C * r / m) (Ioc 0 (1/m)) := by
      have h_cont : Continuous (fun r : ℝ => C * r / m) := by continuity
      exact h_cont.integrableOn_Ioc
    have hf_meas := radial_besselK_aestronglyMeasurable_Ioc (ν := ν) hm
    have h_norm_bound : ∀ᵐ r ∂(volume.restrict (Ioc 0 (1/m))), ‖r ^ 2 * besselK ν (m * r)‖ ≤ C * r / m := by
      rw [ae_restrict_iff' measurableSet_Ioc]
      apply Eventually.of_forall
      intro r hr
      rw [Real.norm_of_nonneg (radial_besselK_nonneg hm hr.1)]
      exact h_bound r hr
    exact Integrable.mono' h_bound_int hf_meas h_norm_bound
  -- Part 2: Integrability on (1/m, ∞)
  · -- At infinity: use besselK_asymptotic for exponential decay
    -- For r > 1/m, we have mr > 1, so K(ν,mr) ≤ (((sinh ν) / ν) + 2) * exp(-mr)
    set C := (sinh ν) / ν + 2 with hC_def
    have hC_pos : 0 < C := by simp only [hC_def]; apply add_pos; positivity; linarith
    -- Bound: r² K(ν,mr) ≤ C * r² * exp(-mr) for r > 1/m
    have h_bound : ∀ r ∈ Ioi (1/m : ℝ), r ^ 2 * besselK ν (m * r) ≤ C * r ^ 2 * exp (-m * r) := by
      intro r hr
      have hmr_ge : m * r ≥ 1 := by
        simp only [mem_Ioi] at hr
        have h1 : m * (1/m) = 1 := by field_simp
        have h2 : m * r > m * (1/m) := mul_lt_mul_of_pos_left hr hm
        linarith
      have hK_bound := besselK_asymptotic νpos νle (m * r) hmr_ge
      calc r ^ 2 * besselK ν (m * r)
          ≤ r ^ 2 * (C * exp (-(m * r))) := by
            apply mul_le_mul_of_nonneg_left hK_bound (sq_nonneg r)
        _ = C * r ^ 2 * exp (-m * r) := by ring_nf
    -- The bounding function C * r² * exp(-mr) is integrable on (1/m, ∞)
    -- r² exp(-mr) is integrable because polynomial growth is beaten by exponential decay
    have h_bound_int : IntegrableOn (fun r => C * r ^ 2 * exp (-m * r)) (Ioi (1/m)) := by
      -- Use integrable_of_isBigO_exp_neg: polynomial times exponential is integrable
      have h_int' : IntegrableOn (fun r => r ^ 2 * exp (-m * r)) (Ioi (1/m)) := by
        -- r² * exp(-mr) = O(exp(-m/2 * r)) since r² * exp(-mr/2) → 0
        apply integrable_of_isBigO_exp_neg (by linarith : 0 < m/2)
        · -- ContinuousOn (fun r => r² * exp(-mr)) (Ici (1/m))
          apply ContinuousOn.mul (continuous_pow 2).continuousOn
          have hcont : Continuous (fun r : ℝ => exp (-m * r)) := by continuity
          exact hcont.continuousOn
        · -- r² * exp(-mr) = O(exp(-m/2 * r)) at infinity
          -- First establish that r² * exp(-mr/2) → 0, so eventually r² * exp(-mr/2) ≤ 1
          have h_tendsto := tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
          -- Scale: (m/2 * r)² * exp(-(m/2)*r) → 0, so r² * exp(-(m/2)*r) → 0
          have h_scale : Tendsto (fun r => r ^ 2 * exp (-(m/2) * r)) atTop (nhds 0) := by
            have hm2 : 0 < m / 2 := by linarith
            have h1 := h_tendsto.comp (tendsto_id.const_mul_atTop hm2)
            -- Simplify h1 from composition form
            simp only [Function.comp_def, id] at h1
            -- (m/2 * r)² * exp(-(m/2 * r)) = (m/2)² * r² * exp(-(m/2)*r)
            have h2 : (fun r => (m/2 * r) ^ 2 * exp (-(m/2 * r))) =
                      (fun r => (m/2)^2 * (r ^ 2 * exp (-(m/2) * r))) := by
              ext r; ring_nf
            rw [h2] at h1
            have h3 : (m/2)^2 ≠ 0 := by positivity
            -- Use tendsto_const_smul_iff₀: if c ≠ 0 then (c • f → c • a) ↔ (f → a)
            -- In ℝ, c • x = c * x, so this applies
            have h1' : Tendsto (fun r => (m/2)^2 • (r ^ 2 * exp (-(m/2) * r))) atTop (nhds ((m/2)^2 • 0)) := by
              simp only [smul_eq_mul, mul_zero]; exact h1
            rw [tendsto_const_smul_iff₀ h3] at h1'
            exact h1'
          -- Eventually r² * exp(-mr/2) ≤ 1
          have h_ev : ∀ᶠ r in atTop, r ^ 2 * exp (-(m/2) * r) ≤ 1 :=
            (Metric.tendsto_nhds.mp h_scale 1 one_pos).mono fun r h => by
              simp only [Real.dist_eq, sub_zero] at h; rw [abs_lt] at h; linarith
          -- Now prove the IsBigO
          apply Asymptotics.IsBigO.of_bound 1
          filter_upwards [eventually_ge_atTop (1:ℝ), h_ev] with r hr h_le
          rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg r) (exp_nonneg _)), one_mul,
              Real.norm_of_nonneg (exp_nonneg _)]
          -- r² * exp(-mr) = (r² * exp(-mr/2)) * exp(-mr/2) ≤ 1 * exp(-mr/2)
          have hexp : exp (-m * r) = exp (-(m/2) * r) * exp (-(m/2) * r) := by
            rw [← exp_add]; congr 1; ring
          calc r ^ 2 * exp (-m * r)
              = r ^ 2 * (exp (-(m/2) * r) * exp (-(m/2) * r)) := by rw [hexp]
            _ = (r ^ 2 * exp (-(m/2) * r)) * exp (-(m/2) * r) := by ring
            _ ≤ 1 * exp (-(m/2) * r) := by nlinarith [exp_pos (-(m/2) * r)]
            _ = exp (-(m/2) * r) := one_mul _
      have h_eq : (fun r => C * r ^ 2 * exp (-m * r)) = (fun r => C * (r ^ 2 * exp (-m * r))) := by
        ext r; ring
      rw [h_eq]
      exact h_int'.const_mul C
    have hf_meas := radial_besselK_aestronglyMeasurable_Ioi (ν := ν) hm
    have h_norm_bound : ∀ᵐ r ∂(volume.restrict (Ioi (1/m))), ‖r ^ 2 * besselK ν (m * r)‖ ≤ C * r ^ 2 * exp (-m * r) := by
      rw [ae_restrict_iff' measurableSet_Ioi]
      apply Eventually.of_forall
      intro r hr
      rw [Real.norm_of_nonneg (radial_besselK_nonneg hm (by
        simp only [mem_Ioi] at hr
        linarith [one_div_pos.mpr hm]))]
      exact h_bound r hr
    exact Integrable.mono' h_bound_int hf_meas h_norm_bound

/-- Symmetry lemma: the full-line integral of exp(-νu) * exp(-z cosh u) equals
    twice the half-line cosh integral, which is 2 * K(ν,z).

    ∫_{-∞}^∞ exp(-νu) * exp(-z cosh u) du = 2 ∫_0^∞ cosh(νu) * exp(-z cosh u) du

  This follows from splitting at 0 and using cosh(-u) = cosh(u).

  The proof works for arbitrary real ν: the tail integrability estimates use |ν|
  rather than requiring ν > 0. -/
lemma bessel_symmetry_integral {ν : ℝ} (z : ℝ) (hz : 0 < z) :
    ∫ u : ℝ, exp (-ν * u) * exp (-z * cosh u) = 2 * besselK ν z := by
  -- Integrability conditions (both decay super-exponentially as u → ∞)
  have hg_int : IntegrableOn (fun u => exp (ν * u) * exp (-z * cosh u)) (Ioi 0) :=
    exp_mul_exp_neg_cosh_integrableOn_Ioi ν z hz
  have hf_int_Ioi : IntegrableOn (fun u => exp (- ν * u) * exp (-z * cosh u)) (Ioi 0) := by
    simpa [neg_mul] using exp_mul_exp_neg_cosh_integrableOn_Ioi (-ν) z hz
  have hf_int_Iic : IntegrableOn (fun u => exp (- ν * u) * exp (-z * cosh u)) (Iic 0) := by
    -- hg_int.comp_neg: g(-u) integrable on -Ioi 0, where g(u) = exp(u) * exp(-z*cosh(u))
    -- g(-u) = exp(-u) * exp(-z*cosh(-u)) = exp(-u) * exp(-z*cosh(u)) = f(u) (since cosh is even)
    have h1 : IntegrableOn (fun u => exp (ν * (-u)) * exp (-z * cosh (-u))) (-(Ioi (0 : ℝ))) :=
      (exp_mul_exp_neg_cosh_integrableOn_Ioi ν z hz).comp_neg
    -- Use cosh(-u) = cosh(u)
    have h2 : IntegrableOn (fun u => exp (- ν * u) * exp (-z * cosh u)) (-(Ioi (0 : ℝ))) := by
      simpa [neg_mul, cosh_neg] using h1
    -- -(Ioi 0) = Iio 0
    have hIio_eq : -(Ioi (0 : ℝ)) = Iio 0 := by
      ext x; simp only [Set.mem_neg, Set.mem_Ioi, Set.mem_Iio]; constructor <;> intro h <;> linarith
    rw [hIio_eq] at h2
    -- Iic 0 and Iio 0 are a.e. equal
    exact h2.congr_set_ae Iio_ae_eq_Iic.symm
  -- 1. Split the integral over ℝ into (-∞, 0] and (0, ∞) using intervalIntegral.integral_Iic_add_Ioi
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := 0) hf_int_Iic hf_int_Ioi]
  -- 2. Transform the negative part (Iic 0) using u ↦ -u
  --    ∫_{-∞}^0 f(u) du = ∫_0^∞ f(-u) du = ∫_0^∞ g(u) du  (via u → -u, using cosh(-u) = cosh(u))
  have h_neg_part : ∫ u in Iic 0, exp (- ν * u) * exp (-z * cosh u) =
                    ∫ u in Ioi 0, exp (ν * u) * exp (-z * cosh u) := by
    have h := integral_comp_neg_Iic (f := fun u => exp (ν * u) * exp (-z * cosh u)) 0
    simp only [neg_zero] at h
    rw [← h]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Iic
    intro u _
    simp [neg_mul, cosh_neg]
  -- 3. Substitute and combine
  rw [h_neg_part, ← MeasureTheory.integral_add hg_int hf_int_Ioi]
  -- Combine integrands: (e^u + e^-u) * exp(-z cosh u) = 2 cosh(u) * exp(-z cosh u)
  have h_combine : ∫ u in Ioi 0, exp (ν * u) * exp (-z * cosh u) + exp (- ν * u) * exp (-z * cosh u) =
      ∫ u in Ioi 0, 2 * cosh (ν * u) * exp (-z * cosh u) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro u _
    have hcosh : exp (ν * u) + exp (-ν * u) = 2 * cosh (ν * u) := by
      rw [cosh_eq]
      ring_nf
    calc
      exp (ν * u) * exp (-z * cosh u) + exp (-ν * u) * exp (-z * cosh u)
        = (exp (ν * u) + exp (-ν * u)) * exp (-z * cosh u) := by ring
      _ = 2 * cosh (ν * u) * exp (-z * cosh u) := by rw [hcosh]
  rw [h_combine]
  -- Factor out the 2
  have h_factor : ∫ u in Ioi 0, 2 * cosh (ν * u) * exp (-z * cosh u) =
      2 * ∫ u in Ioi 0, cosh (ν * u) * exp (-z * cosh u) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro u _; ring
  rw [h_factor]
  -- Match with besselK definition (which uses Ici 0 = [0, ∞))
  have h_Ioi_Ici : ∫ u in Ioi 0, cosh (ν * u) * exp (-z * cosh u) =
      ∫ u in Ici 0, cosh (ν * u) * exp (-z * cosh u) := setIntegral_congr_set Ioi_ae_eq_Ici
  rw [h_Ioi_Ici]
  unfold besselK
  congr 1
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ici
  intro u _; ring

private lemma strictMono_mul_exp (c : ℝ) (hc : 0 < c) : StrictMono (fun u : ℝ => c * exp u) := by
  intro a b hab
  exact mul_lt_mul_of_pos_left (exp_lt_exp.mpr hab) hc

private lemma image_mul_exp_univ (c : ℝ) (hc : 0 < c) :
    (fun u : ℝ => c * exp u) '' Set.univ = Ioi 0 := by
  ext t
  simp only [Set.mem_image, Set.mem_univ, true_and, mem_Ioi]
  constructor
  · rintro ⟨u, rfl⟩
    exact mul_pos hc (exp_pos u)
  · intro ht
    refine ⟨Real.log (t / c), ?_⟩
    rw [exp_log (by positivity : 0 < t / c)]
    field_simp

private lemma hasDerivWithinAt_mul_exp_univ (c u : ℝ) :
    HasDerivWithinAt (fun u : ℝ => c * exp u) (c * exp u) Set.univ u := by
  exact ((hasDerivAt_exp u).const_mul c).hasDerivWithinAt

private lemma integral_Ioi_substitution_mul_exp
    (c : ℝ) (hc : 0 < c) (g h : ℝ → ℝ) (A : ℝ)
    (htransform : ∀ u, (c * exp u) * g (c * exp u) = A * h u) :
    ∫ t in Ioi 0, g t = A * ∫ u, h u := by
  let φ := fun u => c * exp u
  calc
    ∫ t in Ioi 0, g t = ∫ t in φ '' Set.univ, g t := by rw [image_mul_exp_univ c hc]
    _ = ∫ u in Set.univ, (c * exp u) • g (φ u) :=
        integral_image_eq_integral_deriv_smul_of_monotoneOn MeasurableSet.univ
          (fun u _ => hasDerivWithinAt_mul_exp_univ c u)
          ((strictMono_mul_exp c hc).monotone.monotoneOn Set.univ) g
    _ = ∫ u, A * h u := by
        rw [setIntegral_univ]
        apply MeasureTheory.integral_congr_ae
        filter_upwards with u
        simpa [smul_eq_mul, φ] using htransform u
    _ = A * ∫ u, h u := by rw [MeasureTheory.integral_const_mul]

private lemma schwinger_exponential_substitution_cosh (m r u : ℝ) (hm : 0 < m) (hr : 0 < r) :
    m ^ 2 * (r / (2 * m) * exp u) + r ^ 2 / (4 * (r / (2 * m) * exp u)) = (m * r) * cosh u := by
  have he : exp u * exp (-u) = 1 := by
    rw [exp_neg]
    exact mul_inv_cancel₀ (exp_pos u).ne'
  field_simp [hm.ne', hr.ne']
  rw [cosh_eq]
  ring_nf
  rw [he]
  ring

private lemma schwinger_jacobian_factor (ν c u : ℝ) (hc : 0 < c) :
    (c * exp u) * (1 / (c * exp u) ^ (ν + 1)) = c ^ (-ν) * exp (-ν * u) := by
  have ha : 0 < c * exp u := mul_pos hc (exp_pos u)
  have hrpow_ne : (c * exp u) ^ ν ≠ 0 := by positivity
  have hpow : (c * exp u) ^ (ν + 1) = (c * exp u) ^ ν * (c * exp u) := by
    rw [show ν + 1 = ν + (1 : ℝ) by ring, Real.rpow_add ha, Real.rpow_one]
  calc
    (c * exp u) * (1 / (c * exp u) ^ (ν + 1))
        = (c * exp u) / ((c * exp u) ^ ν * (c * exp u)) := by
            rw [hpow, div_eq_mul_inv]
            ring
    _ = ((c * exp u) ^ ν)⁻¹ := by
        field_simp [ha.ne', hrpow_ne]
    _ = (c * exp u) ^ (-ν) := by rw [Real.rpow_neg (le_of_lt ha)]
    _ = c ^ (-ν) * (exp u) ^ (-ν) := by
        rw [Real.mul_rpow (le_of_lt hc) (le_of_lt (exp_pos u))]
    _ = c ^ (-ν) * exp (u * (-ν)) := by rw [← Real.exp_mul]
    _ = c ^ (-ν) * exp (-ν * u) := by ring_nf

private lemma schwinger_prefactor_eq (ν m r : ℝ) (hm : 0 < m) (hr : 0 < r) :
    (r / (2 * m)) ^ (-ν) = (2 * m / r) ^ ν := by
  calc
    (r / (2 * m)) ^ (-ν) = ((r / (2 * m)) ^ ν)⁻¹ := by
      rw [Real.rpow_neg (by positivity : 0 ≤ r / (2 * m))]
    _ = ((r ^ ν) / ((2 * m) ^ ν))⁻¹ := by
      rw [Real.div_rpow (le_of_lt hr) (by positivity : 0 ≤ 2 * m) ν]
    _ = (2 * m) ^ ν / r ^ ν := by rw [inv_div]
    _ = (2 * m / r) ^ ν := by
      symm
      rw [Real.div_rpow (by positivity : 0 ≤ 2 * m) (le_of_lt hr) ν]

/-- Key identity connecting the Schwinger proper-time integral to K_ν:
    ∫₀^∞ t^{-(ν + 1)} exp(-m²t - r²/(4t)) dt = 2 * (2*m/r)^ν · K(ν,mr)

    This is proven directly via the substitution t = (r/(2m)) exp(u),
    which transforms the integral to the cosh representation of K_ν. -/
lemma schwingerIntegral_eq_besselK (ν : ℝ) (m r : ℝ) (hm : 0 < m) (hr : 0 < r) :
    ∫ t in Ioi 0, (1 / t^(ν + 1)) * exp (-m^2 * t - r^2 / (4 * t)) =
    2 * (2 * m / r)^ν * besselK ν (m * r) := by
  /-
  Direct proof via substitution t = (r/(2m)) exp(u):

  With this substitution:
  - dt = (r/(2m)) exp(u) du
  - t ranges (0, ∞) as u ranges (-∞, ∞)
  - m²t + r²/(4t) = m²(r/(2m))exp(u) + r²/(4(r/(2m))exp(u))
                  = (mr/2)(exp(u) + exp(-u)) = mr cosh(u)
  - (1/t^(ν + 1))) dt = (2m/r)^(ν + 1) exp(- (ν + 1)u) · (r/(2m)) exp(u) du = (2m/r)^ν exp(- ν * u) du

  Therefore:
  ∫₀^∞ t^{-(ν + 1)} exp(-m²t - r²/(4t)) dt = (2m/r)^ν ∫_{-∞}^∞ exp(-ν * u) exp(-m * r * cosh u) du
                                   = (2m/r)^ν · 2 K(ν,mr)    [by symmetry lemma]
                                   = 2 (2m/r)^ν K(ν,mr)
  -/
  let z := m * r
  have hz : 0 < z := mul_pos hm hr
  rw [mul_comm 2, mul_assoc, ← bessel_symmetry_integral (ν := ν) z hz]

  -- Define the substitution φ(u) = (r/(2m)) exp(u)
  let c := r / (2 * m)
  let g : ℝ → ℝ := fun t => 1 / t ^ (ν + 1) * exp (-m ^ 2 * t - r ^ 2 / (4 * t))
  have hc : 0 < c := by simp only [c]; positivity
  have h_transform : ∀ u : ℝ,
      (c * exp u) * g (c * exp u) = c^(-ν) * (exp (-ν * u) * exp (-z * cosh u)) := by
    intro u
    have h_sum' : m ^ 2 * (c * exp u) + r ^ 2 / (4 * (c * exp u)) = z * cosh u := by
      simpa [c, z] using schwinger_exponential_substitution_cosh m r u hm hr
    have h_jacobian : (c * exp u) * (1 / (c * exp u) ^ (ν + 1)) = c ^ (-ν) * exp (-ν * u) :=
      schwinger_jacobian_factor ν c u hc
    have h_exp_arg : -(m ^ 2 * (c * exp u)) - r ^ 2 / (4 * (c * exp u)) = -(z * cosh u) := by
      linarith [h_sum']
    calc
      (c * exp u) * g (c * exp u)
          = ((c * exp u) * (1 / (c * exp u) ^ (ν + 1))) *
              exp (-(m ^ 2 * (c * exp u)) - r ^ 2 / (4 * (c * exp u))) := by
                simp [g]; ring
      _ = (c ^ (-ν) * exp (-ν * u)) * exp (-(z * cosh u)) := by rw [h_jacobian, h_exp_arg]
      _ = c ^ (-ν) * (exp (-ν * u) * exp (-z * cosh u)) := by ring_nf
  rw [integral_Ioi_substitution_mul_exp c hc g (fun u => exp (-ν * u) * exp (-z * cosh u)) (c ^ (-ν))
    h_transform]
  rw [show c ^ (-ν) = (2 * m / r) ^ ν by simpa [c] using schwinger_prefactor_eq ν m r hm hr]

/-- The special-order positivity lemma for `besselKhalf`. -/
private lemma besselKhalf_order_pos : (0 : ℝ) < 1 / 2 := by
  norm_num

private lemma besselKhalf_order_le_one : (1 / 2 : ℝ) ≤ 1 := by
  norm_num

lemma besselKhalf_pos (z : ℝ) (hz : 0 < z) : 0 < besselKhalf z := by
  unfold besselKhalf
  simpa using besselK_pos (ν := (1 / 2 : ℝ)) z hz

/-- The special-order continuity lemma for `besselKhalf`. -/
lemma besselKhalf_continuousOn : ContinuousOn besselKhalf (Ioi 0) := by
  unfold besselKhalf
  simpa using besselK_continuousOn (ν := (1 / 2 : ℝ))

/-- The special-order asymptotic bound for `besselKhalf`. -/
lemma besselKhalf_asymptotic (z : ℝ) (hz : 1 ≤ z) :
    besselKhalf z ≤ (2 * sinh (1 / 2 : ℝ) + 2) * exp (-z) := by
  change besselK (1 / 2 : ℝ) z ≤ (2 * sinh (1 / 2 : ℝ) + 2) * exp (-z)
  convert
    besselK_asymptotic (ν := (1 / 2 : ℝ)) besselKhalf_order_pos besselKhalf_order_le_one z hz
      using 1
  ring

/-- The special-order near-origin product bound for `besselKhalf`. -/
lemma besselKhalf_mul_self_le (z : ℝ) (hz : 0 < z) (hz_le : z ≤ 1) :
    z * besselKhalf z ≤ cosh (1 / 2 : ℝ) + 2 := by
  unfold besselKhalf
  simpa using
    besselK_mul_self_le (ν := (1 / 2 : ℝ)) besselKhalf_order_pos besselKhalf_order_le_one z hz hz_le

/-- The special-order near-origin bound for `besselKhalf`. -/
lemma besselKhalf_near_origin_bound (z : ℝ) (hz : 0 < z) (hz_small : z ≤ 1) :
    besselKhalf z ≤ (cosh (1 / 2 : ℝ) + 2) / z := by
  unfold besselKhalf
  simpa using
    besselK_near_origin_bound (ν := (1 / 2 : ℝ)) besselKhalf_order_pos besselKhalf_order_le_one z hz hz_small

/-- The special-order radial integrability lemma for `besselKhalf`. -/
lemma radial_besselKhalf_integrable (m : ℝ) (hm : 0 < m) :
    IntegrableOn (fun r => r ^ 2 * besselKhalf (m * r)) (Set.Ioi 0) volume := by
  unfold besselKhalf
  simpa using
    radial_besselK_integrable (ν := (1 / 2 : ℝ)) besselKhalf_order_pos besselKhalf_order_le_one m hm

/-- The Schwinger identity specialized to `besselKhalf`. -/
lemma schwingerIntegral_eq_besselKhalf (m r : ℝ) (hm : 0 < m) (hr : 0 < r) :
    ∫ t in Ioi 0, (1 / t ^ (3 / 2 : ℝ)) * exp (-m^2 * t - r^2 / (4 * t)) =
    2 * (2 * m / r) ^ (1 / 2 : ℝ) * besselKhalf (m * r) := by
  convert schwingerIntegral_eq_besselK (ν := (1 / 2 : ℝ)) m r hm hr using 1
  norm_num

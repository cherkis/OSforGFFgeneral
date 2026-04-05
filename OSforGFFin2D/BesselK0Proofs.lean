/-
Copyright (c) 2025 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas

Proofs of K₀ properties adapted from auto1/lean/SpecialFunctions/Bessel.
These replace the 5 Bessel axioms formerly in BesselFunction.lean.
-/
import OSforGFFin2D.BesselFunction
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

open MeasureTheory Set Filter Real Topology Asymptotics intervalIntegral

/-! ## Helper lemmas: cosh bounds and integrability -/

/-- For any t, cosh(t) ≥ exp(t)/2 -/
private lemma cosh_ge_exp_div_two {t : ℝ} : cosh t ≥ exp t / 2 := by
  rw [Real.cosh_eq]; have : 0 < exp (-t) := exp_pos _; linarith

/-- For t ≥ 0, cosh(t) ≤ exp(t) -/
private lemma cosh_le_exp_of_nonneg {t : ℝ} (ht : 0 ≤ t) : cosh t ≤ exp t := by
  rw [Real.cosh_eq]; have : exp (-t) ≤ exp t := exp_le_exp.mpr (by linarith); linarith

/-- Helper: exp(-c * exp(t)) ≤ exp(-d*t) for large t -/
private lemma super_exp_bound {c d : ℝ} (hc : 0 < c) (_hd : 0 < d) :
    ∃ t₀ > 0, ∀ t ≥ t₀, exp (-c * exp t) ≤ exp (-d * t) := by
  have h_tendsto : Tendsto (fun t => exp t / t) atTop atTop := by
    have := Real.tendsto_exp_div_pow_atTop 1; simp only [pow_one] at this; exact this
  have h_event : ∀ᶠ t in atTop, d / c ≤ exp t / t := h_tendsto.eventually_ge_atTop (d / c)
  obtain ⟨t₀, ht₀⟩ := h_event.exists_forall_of_atTop
  use max t₀ 1
  constructor
  · exact lt_max_of_lt_right one_pos
  · intro t ht
    have ht₀' : t₀ ≤ t := le_of_max_le_left ht
    have ht1 : 1 ≤ t := le_of_max_le_right ht
    have ht_pos : 0 < t := lt_of_lt_of_le one_pos ht1
    have h_bound : d / c ≤ exp t / t := ht₀ t ht₀'
    have h_ineq : d * t ≤ c * exp t := by
      rw [div_le_div_iff₀ hc ht_pos] at h_bound; linarith
    exact exp_le_exp.mpr (by linarith)

/-- A function that decays like exp(-z * exp(t)) is integrable on (1, ∞) -/
private lemma integrable_of_super_exp_decay {f : ℝ → ℝ} {z : ℝ} (_hz : 0 < z)
    (hf_cont : ContinuousOn f (Ici 1))
    (hf_bound : ∃ c > 0, ∀ t ≥ 1, |f t| ≤ exp (-c * exp t)) :
    IntegrableOn f (Ioi 1) volume := by
  obtain ⟨c, hc, hf⟩ := hf_bound
  apply integrable_of_isBigO_exp_neg (b := 1) one_pos hf_cont
  rw [Asymptotics.isBigO_iff]
  use 1
  rw [Filter.eventually_atTop]
  obtain ⟨t₀, _, h_super⟩ := super_exp_bound hc one_pos
  use max t₀ 1
  intro t ht
  have ht₀' : t₀ ≤ t := le_of_max_le_left ht
  have ht1 : 1 ≤ t := le_of_max_le_right ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul]
  calc |f t| ≤ exp (-c * exp t) := hf t ht1
    _ ≤ exp (-1 * t) := h_super t ht₀'
    _ = |exp (-1 * t)| := (abs_of_pos (exp_pos _)).symm

/-- The K₀ integrand exp(-z*cosh(t)) is integrable on (1, ∞) for z > 0 -/
private lemma besselK0_integrand_Ioi_integrable {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun t => exp (-z * cosh t)) (Ioi 1) volume := by
  apply integrable_of_super_exp_decay hz
  · exact (continuous_exp.comp (continuous_const.mul continuous_cosh)).continuousOn
  · use z / 2, by positivity
    intro t _
    rw [abs_of_pos (exp_pos _)]
    apply exp_le_exp.mpr
    have hcosh : cosh t ≥ exp t / 2 := cosh_ge_exp_div_two
    nlinarith

/-- The K₁ integrand exp(-z*cosh(t))*cosh(t) is integrable on (1, ∞) for z > 0 -/
private lemma besselK1_integrand_Ioi_integrable {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun t => exp (-z * cosh t) * cosh t) (Ioi 1) volume := by
  apply integrable_of_isBigO_exp_neg (b := 1) one_pos
  · exact ((continuous_exp.comp (continuous_const.mul continuous_cosh)).mul
      continuous_cosh).continuousOn
  · rw [Asymptotics.isBigO_iff]
    use 1; rw [Filter.eventually_atTop]
    obtain ⟨t₀, _, h_super⟩ := super_exp_bound (c := z / 2) (d := 2) (by positivity) (by norm_num)
    use max t₀ 1
    intro t ht
    have ht1 : 1 ≤ t := le_of_max_le_right ht
    have ht0 : t₀ ≤ t := le_of_max_le_left ht
    rw [Real.norm_of_nonneg (mul_nonneg (exp_pos _).le (cosh_pos t).le)]
    rw [Real.norm_of_nonneg (exp_pos _).le, one_mul]
    have h_cosh_le : cosh t ≤ exp t := cosh_le_exp_of_nonneg (by linarith)
    have hexp_bound : exp (-z * cosh t) ≤ exp (-(z/2) * exp t) := by
      apply exp_le_exp.mpr; nlinarith [cosh_ge_exp_div_two (t := t)]
    calc exp (-z * cosh t) * cosh t
        ≤ exp (-(z/2) * exp t) * exp t :=
          mul_le_mul hexp_bound h_cosh_le (cosh_pos t).le (exp_pos _).le
      _ = exp (-(z/2) * exp t + t) := by rw [← exp_add]
      _ ≤ exp (-2 * t + t) := by
          apply exp_le_exp.mpr; linarith [exp_le_exp.mp (h_super t ht0)]
      _ = exp (-1 * t) := by ring_nf

/-- Icc and Ioi with same endpoint are disjoint -/
private lemma Icc_disjoint_Ioi {a b : ℝ} : Disjoint (Icc a b) (Ioi b) := by
  rw [Set.disjoint_iff]
  intro x ⟨hx_icc, hx_ioi⟩
  simp only [Set.mem_Icc, Set.mem_Ioi] at hx_icc hx_ioi; linarith

/-- Helper for splitting [0,∞) = [0,1] ∪ (1,∞) -/
private lemma Ici_split : Ici (0 : ℝ) = Icc 0 1 ∪ Ioi 1 := by
  ext x; simp only [mem_Ici, mem_union, mem_Icc, mem_Ioi]
  constructor
  · intro hx; by_cases h : x ≤ 1; left; exact ⟨hx, h⟩; right; linarith
  · intro h; cases h with | inl h => exact h.1 | inr h => linarith

/-- Integral of positive function over positive measure set is positive -/
private lemma integral_pos_of_pos_on_pos_measure {f : ℝ → ℝ} {s : Set ℝ}
    (hs_meas : MeasurableSet s)
    (hf : ∀ x ∈ s, 0 < f x)
    (hfi : IntegrableOn f s)
    (hs : 0 < volume s) :
    0 < ∫ x in s, f x := by
  have hf_nonneg : ∀ x ∈ s, 0 ≤ f x := fun x hx => le_of_lt (hf x hx)
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · have h_supp : s ⊆ Function.support f := fun x hx => ne_of_gt (hf x hx)
    rw [Set.inter_eq_right.mpr h_supp]; exact hs
  · exact ae_restrict_of_forall_mem hs_meas hf_nonneg
  · exact hfi

/-- Derivative of exp(-z * cosh t) with respect to z -/
private lemma exp_neg_mul_cosh_hasDerivAt (t z : ℝ) :
    HasDerivAt (fun w => exp (-w * cosh t)) ((-cosh t) * exp (-z * cosh t)) z := by
  have h1 : HasDerivAt (fun w => -w * cosh t) (-cosh t) z := by
    have := (hasDerivAt_id z).neg.mul_const (cosh t)
    simp only [neg_mul, one_mul] at this; exact this
  convert (hasDerivAt_exp (-z * cosh t)).comp z h1 using 1; ring

/-- Bound on K₀ derivative integrand for z' in a neighborhood of z -/
private lemma besselK0_deriv_bound (t z z' : ℝ) (hz'_lower : z / 2 < z') :
    ‖(-cosh t) * exp (-z' * cosh t)‖ ≤ cosh t * exp (-(z/2) * cosh t) := by
  rw [norm_eq_abs, abs_mul, abs_neg, abs_of_pos (cosh_pos t), abs_of_pos (exp_pos _)]
  apply mul_le_mul_of_nonneg_left _ (cosh_pos t).le
  apply exp_le_exp.mpr; nlinarith [(cosh_pos t).le]

/-- HasDerivAt for exp(-z * cosh s) with respect to s -/
private lemma exp_neg_z_cosh_hasDerivAt (z t : ℝ) :
    HasDerivAt (fun s => exp (-z * cosh s)) (-z * sinh t * exp (-z * cosh t)) t := by
  have h1 : HasDerivAt cosh (sinh t) t := Real.hasDerivAt_cosh t
  have h2 : HasDerivAt (fun s => -z * cosh s) (-z * sinh t) t := h1.const_mul (-z)
  convert (hasDerivAt_exp (-z * cosh t)).comp t h2 using 1; ring

/-- Integrability of cosh * exp(-z cosh) (the K₁ integrand) on Ioi 0 -/
private lemma cosh_exp_integrable {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun t => cosh t * exp (-z * cosh t)) (Ioi 0) volume := by
  have split : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := by
    ext x; simp only [mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro hx; by_cases h : x ≤ 1; left; exact ⟨hx, h⟩; right; linarith
    · intro h; cases h with | inl h => exact h.1 | inr h => linarith
  rw [split, integrableOn_union]
  constructor
  · exact (continuous_cosh.mul (continuous_exp.comp (continuous_const.mul continuous_cosh))).integrableOn_Ioc
  · exact (besselK1_integrand_Ioi_integrable hz).congr_fun (fun t _ => by ring) measurableSet_Ioi

/-! ## 1. K₀(z) > 0 for z > 0 -/

/-- K₀(z) is positive for z > 0 (proved via positivity of the integrand). -/
theorem besselK0_pos (z : ℝ) (hz : 0 < z) : 0 < besselK0 z := by
  unfold besselK0
  set f := fun t => exp (-z * cosh t)
  have hf_int : IntegrableOn f (Ici 0) volume := by
    rw [Ici_split, integrableOn_union]
    exact ⟨(continuous_exp.comp (continuous_const.mul continuous_cosh)).continuousOn.integrableOn_compact isCompact_Icc,
           besselK0_integrand_Ioi_integrable hz⟩
  apply integral_pos_of_pos_on_pos_measure measurableSet_Ici
    (fun t _ => exp_pos _) hf_int
  rw [Real.volume_Ici]; exact ENNReal.zero_lt_top

/-! ## 2. K₀'(z) = -K₁(z) -/

/-- Derivative relation: K₀'(z) = -K₁(z) (DLMF 10.29.3). -/
private theorem besselK0_deriv (z : ℝ) (hz : 0 < z) :
    HasDerivAt besselK0 (-besselK1 z) z := by
  set F : ℝ → ℝ → ℝ := fun z' t => exp (-z' * cosh t)
  set F' : ℝ → ℝ → ℝ := fun z' t => (-cosh t) * exp (-z' * cosh t)
  set bound : ℝ → ℝ := fun t => cosh t * exp (-(z/2) * cosh t)
  set s := Ioo (z/2) (z + 1)
  have hs : s ∈ 𝓝 z := Ioo_mem_nhds (by linarith) (by linarith)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (E := ℝ)
    (μ := volume.restrict (Ici 0)) (F := F) (x₀ := z) (bound := bound) (s := s) (F' := F')
    hs ?meas ?int_F ?meas_F' ?bound_cond ?int_bound ?deriv_cond
  · obtain ⟨_, hderiv⟩ := key
    unfold besselK0
    convert hderiv using 2
    unfold besselK1
    rw [← MeasureTheory.integral_neg]
    congr 1; ext t; ring
  case meas => filter_upwards with z'
               exact (continuous_exp.comp (continuous_const.mul continuous_cosh)).aestronglyMeasurable
  case int_F => rw [Ici_split, Measure.restrict_union Icc_disjoint_Ioi measurableSet_Ioi,
                    integrable_add_measure]
                constructor
                · exact (continuous_exp.comp (continuous_const.mul continuous_cosh)).continuousOn.integrableOn_compact isCompact_Icc
                · exact besselK0_integrand_Ioi_integrable hz
  case meas_F' => exact (continuous_cosh.neg.mul (continuous_exp.comp (continuous_const.mul continuous_cosh))).aestronglyMeasurable
  case bound_cond => filter_upwards with t
                     intro z' hz'
                     have hz'_lower : z / 2 < z' := hz'.1
                     exact besselK0_deriv_bound t z z' hz'_lower
  case int_bound =>
    have hz2 : 0 < z / 2 := by linarith
    have h_eq : bound = fun t => exp (-(z/2) * cosh t) * cosh t := by ext t; ring
    have h_Ioi : IntegrableOn bound (Ioi 1) := by rw [h_eq]; exact besselK1_integrand_Ioi_integrable hz2
    have h_Icc : IntegrableOn bound (Icc 0 1) := by
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      exact (continuous_cosh.mul (continuous_exp.comp (continuous_const.mul continuous_cosh))).continuousOn
    rw [Ici_split, Measure.restrict_union Icc_disjoint_Ioi measurableSet_Ioi, integrable_add_measure]
    exact ⟨h_Icc, h_Ioi⟩
  case deriv_cond =>
    filter_upwards with t
    intro z' _
    exact exp_neg_mul_cosh_hasDerivAt t z'

/-! ## 3. K₀(z) < K₁(z) -/

/-- K₀(z) < K₁(z) for z > 0, since cosh(t) > 1 for t > 0. -/
private theorem besselK0_lt_besselK1 (z : ℝ) (hz : 0 < z) : besselK0 z < besselK1 z := by
  unfold besselK0 besselK1; rw [← sub_pos]
  have hK1_int : IntegrableOn (fun t => exp (-z * cosh t) * cosh t) (Ici 0) volume := by
    rw [Ici_split, integrableOn_union]
    exact ⟨((continuous_exp.comp (continuous_const.mul continuous_cosh)).mul continuous_cosh).continuousOn.integrableOn_compact isCompact_Icc,
           besselK1_integrand_Ioi_integrable hz⟩
  have hK0_int : IntegrableOn (fun t => exp (-z * cosh t)) (Ici 0) volume := by
    rw [Ici_split, integrableOn_union]
    exact ⟨(continuous_exp.comp (continuous_const.mul continuous_cosh)).continuousOn.integrableOn_compact isCompact_Icc,
           besselK0_integrand_Ioi_integrable hz⟩
  have h_eq : (∫ t : ℝ in Ici 0, exp (-z * cosh t) * cosh t) -
              (∫ t : ℝ in Ici 0, exp (-z * cosh t)) =
              ∫ t : ℝ in Ici 0, exp (-z * cosh t) * (cosh t - 1) := by
    rw [← MeasureTheory.integral_sub hK1_int hK0_int]; congr 1; ext t; ring
  rw [h_eq]
  set f := fun t => exp (-z * cosh t) * (cosh t - 1)
  have hf_int : IntegrableOn f (Ici 0) volume := by
    rw [Ici_split, integrableOn_union]
    constructor
    · exact ((continuous_exp.comp (continuous_const.mul continuous_cosh)).mul
        (continuous_cosh.sub continuous_const)).continuousOn.integrableOn_compact isCompact_Icc
    · apply Integrable.mono' (besselK1_integrand_Ioi_integrable hz)
      · exact ((continuous_exp.comp (continuous_const.mul continuous_cosh)).mul
          (continuous_cosh.sub continuous_const)).aestronglyMeasurable.restrict
      · filter_upwards with t
        rw [Real.norm_of_nonneg (mul_nonneg (exp_pos _).le (sub_nonneg.mpr (Real.one_le_cosh t)))]
        apply mul_le_mul_of_nonneg_left _ (exp_pos _).le
        have := cosh_pos t; linarith
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · have h_subset : Ioi 0 ∩ Ici 0 ⊆ Function.support f ∩ Ici 0 :=
      fun t ⟨ht_pos, ht_ge⟩ => ⟨(mul_pos (exp_pos _) (sub_pos.mpr (Real.one_lt_cosh.mpr (ne_of_gt ht_pos)))).ne', ht_ge⟩
    calc volume (Function.support f ∩ Ici 0)
        ≥ volume (Ioi (0:ℝ) ∩ Ici 0) := measure_mono h_subset
      _ = volume (Ioi (0 : ℝ)) := by congr 1; ext x; simp [and_iff_left_of_imp le_of_lt]
      _ > 0 := by rw [Real.volume_Ioi]; exact ENNReal.zero_lt_top
  · exact ae_restrict_of_forall_mem measurableSet_Ici (fun t _ =>
      mul_nonneg (exp_pos _).le (sub_nonneg.mpr (Real.one_le_cosh t)))
  · exact hf_int

/-! ## 4. Continuity of K₀ on (0, ∞) -/

/-- K₀ is continuous on (0, ∞) via dominated convergence for parameter integrals. -/
theorem besselK0_continuousOn : ContinuousOn besselK0 (Ioi 0) := by
  rw [isOpen_Ioi.continuousOn_iff]
  intro z₀ hz₀
  have hz₀' : 0 < z₀ := mem_Ioi.mp hz₀
  unfold besselK0
  set bound := fun t : ℝ => exp (-(z₀/2) * cosh t)
  apply MeasureTheory.continuousAt_of_dominated (bound := bound)
  case hF_meas =>
    filter_upwards with x
    exact (continuous_exp.comp (continuous_const.mul continuous_cosh)).aestronglyMeasurable
  case h_bound =>
    have : ∀ᶠ x in 𝓝 z₀, z₀/2 < x := by
      apply Metric.eventually_nhds_iff_ball.mpr
      exact ⟨z₀/2, by positivity, fun x hx => by
        simp only [Metric.mem_ball, Real.dist_eq] at hx; linarith [(abs_lt.mp hx).1]⟩
    filter_upwards [this] with x hx
    filter_upwards with t
    simp only [Real.norm_eq_abs, abs_exp]
    apply exp_le_exp.mpr
    nlinarith [(cosh_pos t).le]
  case bound_integrable =>
    rw [Ici_split, Measure.restrict_union Icc_disjoint_Ioi measurableSet_Ioi, integrable_add_measure]
    exact ⟨(continuous_exp.comp (continuous_const.mul continuous_cosh)).continuousOn.integrableOn_compact isCompact_Icc,
           besselK0_integrand_Ioi_integrable (by positivity)⟩
  case h_cont =>
    filter_upwards with t
    exact (continuous_exp.comp (continuous_id.neg.mul continuous_const)).continuousAt

/-! ## 5. Asymptotic bound K₀(z) ≤ √(π/(2z)) · exp(-z) -/

/-- cosh(t) ≥ 1 + t²/2 for all t. -/
private lemma cosh_ge_one_add_sq_div_two (t : ℝ) : 1 + t ^ 2 / 2 ≤ cosh t := by
  rw [← Real.cosh_abs t]
  set s := |t|; have hs : 0 ≤ s := abs_nonneg t
  have key : cosh s = 1 + 2 * sinh (s/2) ^ 2 := by
    rw [show s = 2 * (s/2) from by ring, Real.cosh_two_mul, Real.cosh_sq']; ring_nf
  rw [key]
  have h_sinh : s/2 ≤ sinh (s/2) := Real.self_le_sinh_iff.mpr (by linarith)
  have h_sq : (s/2) ^ 2 ≤ sinh (s/2) ^ 2 :=
    sq_le_sq' (by linarith [Real.sinh_nonneg_iff.mpr (by linarith : 0 ≤ s/2)]) h_sinh
  nlinarith [sq_abs t]

/-- exp(-z*cosh(t)) ≤ exp(-z) * exp(-z*t²/2) -/
private lemma exp_neg_cosh_le_gaussian (z t : ℝ) (hz : 0 < z) :
    exp (-z * cosh t) ≤ exp (-z) * exp (-(z/2) * t^2) := by
  rw [← exp_add]; exact exp_le_exp.mpr (by nlinarith [cosh_ge_one_add_sq_div_two t])

/-- The Gaussian exp(-(z/2)*t²) is integrable on [0,∞) for z > 0 -/
private lemma integrableOn_gaussian_Ici {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun t => exp (-(z/2) * t^2)) (Ici 0) volume :=
  (integrable_exp_neg_mul_sq (by linarith : 0 < z/2)).integrableOn

/-- Asymptotic bound: K₀(z) ≤ √(π/(2z)) · exp(-z) for z > 0.
    Uses cosh(t) ≥ 1 + t²/2 and the Gaussian integral. -/
theorem besselK0_asymptotic (z : ℝ) (hz : 0 < z) :
    besselK0 z ≤ Real.sqrt (π / (2 * z)) * exp (-z) := by
  unfold besselK0
  have h_bound : ∀ t, exp (-z * cosh t) ≤ exp (-z) * exp (-(z/2) * t^2) :=
    fun t => exp_neg_cosh_le_gaussian z t hz
  have h_K0_int : IntegrableOn (fun t => exp (-z * cosh t)) (Ici 0) volume := by
    rw [Ici_split, integrableOn_union]
    exact ⟨(continuous_exp.comp (continuous_const.mul continuous_cosh)).continuousOn.integrableOn_compact isCompact_Icc,
           besselK0_integrand_Ioi_integrable hz⟩
  have h_gauss_int : IntegrableOn (fun t => exp (-z) * exp (-(z/2) * t^2)) (Ici 0) volume :=
    (integrableOn_gaussian_Ici hz).const_mul _
  calc ∫ t in Ici 0, exp (-z * cosh t)
      ≤ ∫ t in Ici 0, exp (-z) * exp (-(z/2) * t^2) :=
        setIntegral_mono h_K0_int h_gauss_int h_bound
    _ = exp (-z) * ∫ t in Ici 0, exp (-(z/2) * t^2) := MeasureTheory.integral_const_mul ..
    _ = exp (-z) * (Real.sqrt (π / (z/2)) / 2) := by
        rw [setIntegral_congr_set Ioi_ae_eq_Ici.symm, integral_gaussian_Ioi]
    _ = Real.sqrt (π / (2 * z)) * exp (-z) := by
        have h_eq : Real.sqrt (π / (z / 2)) / 2 = Real.sqrt (π / (2 * z)) := by
          have h4 : π / (z / 2) = 2 ^ 2 * (π / (2 * z)) := by field_simp
          rw [h4, Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 ^ 2),
              Real.sqrt_sq (by positivity : (0:ℝ) ≤ 2)]
          linarith
        rw [h_eq]; ring
/-! ## 6. z·K₁(z) ≤ 1 (helper for near-origin bound) -/

private lemma tendsto_cosh_atTop' : Tendsto cosh atTop atTop := by
  apply tendsto_atTop_atTop.mpr
  intro b; obtain ⟨t₀, ht₀⟩ := (tendsto_atTop_atTop.mp tendsto_exp_atTop) (2 * b)
  use t₀; intro t ht; rw [Real.cosh_eq]; linarith [exp_nonneg (-t), ht₀ t ht]

private lemma tendsto_neg_exp_neg_z_cosh (z : ℝ) (hz : 0 < z) :
    Tendsto (fun t => -exp (-z * cosh t)) atTop (𝓝 0) := by
  have h3 : Tendsto (fun t => exp (-(z * cosh t))) atTop (𝓝 0) :=
    tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp (tendsto_cosh_atTop'.const_mul_atTop hz))
  have h4 := h3.neg; rw [neg_zero] at h4; exact h4.congr (fun t => by ring_nf)

set_option maxHeartbeats 800000 in
/-- For z > 0, z·K₁(z) ≤ 1.
    Uses: split cosh = sinh + exp(-t), FTC for the sinh part, bound the exp(-t) part. -/
private lemma besselK1_mul_self_le_one (z : ℝ) (hz : 0 < z) : z * besselK1 z ≤ 1 := by
  unfold besselK1
  rw [show ∫ t in Ici (0:ℝ), exp (-z * cosh t) * cosh t =
      ∫ t in Ioi (0:ℝ), exp (-z * cosh t) * cosh t from
      setIntegral_congr_set Ioi_ae_eq_Ici.symm]
  rw [← MeasureTheory.integral_const_mul]
  -- Split cosh = sinh + exp(-t): cosh(t) - sinh(t) = exp(-t)
  have h_eq : ∀ t : ℝ, z * (exp (-z * cosh t) * cosh t) =
      z * sinh t * exp (-z * cosh t) + z * exp (-t) * exp (-z * cosh t) := by
    intro t
    have h : cosh t = sinh t + exp (-t) := by linarith [Real.cosh_sub_sinh t]
    rw [h]; ring
  have h_integrand_eq : (fun t => z * (exp (-z * cosh t) * cosh t)) =
      (fun t => z * sinh t * exp (-z * cosh t) + z * exp (-t) * exp (-z * cosh t)) :=
    funext h_eq
  rw [h_integrand_eq]
  -- Integrability of part 1: z*sinh*exp(-z*cosh) dominated by z*cosh*exp(-z*cosh)
  have h1 : IntegrableOn (fun t => z * sinh t * exp (-z * cosh t)) (Ioi 0) volume := by
    apply Integrable.mono ((cosh_exp_integrable hz).const_mul z)
    · exact (((continuous_const.mul continuous_sinh).mul
        (continuous_exp.comp (continuous_const.mul continuous_cosh))).aestronglyMeasurable).restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simp only [mem_Ioi] at ht
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by positivity : 0 ≤ z * sinh t * exp (-z * cosh t)),
          abs_of_nonneg (by positivity : 0 ≤ z * (cosh t * exp (-z * cosh t)))]
      calc z * sinh t * exp (-z * cosh t)
          ≤ z * cosh t * exp (-z * cosh t) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (sinh_lt_cosh t).le hz.le) (exp_pos _).le
        _ = z * (cosh t * exp (-z * cosh t)) := by ring
  -- Integrability of part 2: z*exp(-t)*exp(-z*cosh) ≤ z*exp(-z)*exp(-t)
  have h2 : IntegrableOn (fun t => z * exp (-t) * exp (-z * cosh t)) (Ioi 0) volume := by
    apply Integrable.mono ((integrableOn_exp_neg_Ioi 0).const_mul (z * exp (-z)))
    · exact (((continuous_const.mul (continuous_exp.comp continuous_neg)).mul
        (continuous_exp.comp (continuous_const.mul continuous_cosh))).aestronglyMeasurable).restrict
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
      calc z * exp (-t) * exp (-z * cosh t)
          ≤ z * exp (-t) * exp (-z) :=
            mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by nlinarith [Real.one_le_cosh t])) (by positivity)
        _ = z * exp (-z) * exp (-t) := by ring
  rw [MeasureTheory.integral_add h1 h2]
  -- Part 1: FTC gives ∫₀^∞ z*sinh(t)*exp(-z*cosh(t)) dt = exp(-z)
  have hPart1 : ∫ t in Ioi (0:ℝ), z * sinh t * exp (-z * cosh t) = exp (-z) := by
    rw [integral_Ioi_of_hasDerivAt_of_tendsto
      (((continuous_exp.comp (continuous_const.mul continuous_cosh)).neg).continuousAt.continuousWithinAt)
      (fun t _ => by convert (exp_neg_z_cosh_hasDerivAt z t).neg using 1; ring)
      h1
      (tendsto_neg_exp_neg_z_cosh z hz)]
    simp [Real.cosh_zero]
  -- Part 2: bound ∫₀^∞ z*exp(-t)*exp(-z*cosh(t)) dt ≤ z*exp(-z)
  have hPart2 : ∫ t in Ioi (0:ℝ), z * exp (-t) * exp (-z * cosh t) ≤ z * exp (-z) := by
    calc ∫ t in Ioi (0:ℝ), z * exp (-t) * exp (-z * cosh t)
        ≤ ∫ t in Ioi (0:ℝ), z * exp (-z) * exp (-t) := by
          apply setIntegral_mono h2 ((integrableOn_exp_neg_Ioi 0).const_mul _)
          intro t
          calc z * exp (-t) * exp (-z * cosh t)
              ≤ z * exp (-t) * exp (-z) :=
                mul_le_mul_of_nonneg_left (exp_le_exp.mpr (by nlinarith [Real.one_le_cosh t])) (by positivity)
            _ = z * exp (-z) * exp (-t) := by ring
      _ = z * exp (-z) * ∫ t in Ioi (0:ℝ), exp (-t) := MeasureTheory.integral_const_mul ..
      _ = z * exp (-z) := by rw [integral_exp_neg_Ioi]; simp
  -- Final: exp(-z) + z*exp(-z) = (z+1)*exp(-z) ≤ exp(z)*exp(-z) = 1
  linarith [calc
    (∫ t in Ioi (0:ℝ), z * sinh t * exp (-z * cosh t)) +
      ∫ t in Ioi (0:ℝ), z * exp (-t) * exp (-z * cosh t)
      = exp (-z) + ∫ t in Ioi (0:ℝ), z * exp (-t) * exp (-z * cosh t) := by rw [hPart1]
    _ ≤ exp (-z) + z * exp (-z) := by linarith [hPart2]
    _ = (z + 1) * exp (-z) := by ring
    _ ≤ exp z * exp (-z) := mul_le_mul_of_nonneg_right (add_one_le_exp z) (exp_pos _).le
    _ = 1 := by rw [← exp_add]; simp]

/-! ## 7. Near-origin bound: K₀(z) ≤ |log(z/2)| + 1 for z ∈ (0, 1] -/

set_option maxHeartbeats 800000 in
/-- Near-origin bound for K₀ using FTC and z·K₁(z) ≤ 1. -/
theorem besselK0_near_origin_bound (z : ℝ) (hz : 0 < z) (hz_small : z ≤ 1) :
    besselK0 z ≤ |Real.log (z / 2)| + 1 := by
  have h_deriv : ∀ t ∈ uIcc z 1, HasDerivAt besselK0 (-besselK1 t) t := by
    intro t ht; apply besselK0_deriv
    rw [Set.mem_uIcc] at ht; cases ht with | inl h => linarith [h.1] | inr h => linarith [h.1]
  have hK1_integrable : IntervalIntegrable besselK1 volume z 1 := by
    apply ContinuousOn.intervalIntegrable
    exact besselK1_continuousOn.mono (by
      intro t ht; rw [Set.mem_uIcc] at ht
      exact Set.mem_Ioi.mpr (by cases ht with | inl h => linarith [h.1] | inr h => linarith [h.1]))
  have hFTC : besselK0 z = besselK0 1 + ∫ t in z..1, besselK1 t := by
    have h_ftc := integral_eq_sub_of_hasDerivAt h_deriv hK1_integrable.neg
    rw [intervalIntegral.integral_neg] at h_ftc; linarith
  have hK1_bound : ∀ t ∈ Icc z 1, besselK1 t ≤ t⁻¹ := by
    intro t ⟨htz, _⟩
    have ht_pos : 0 < t := by linarith
    rw [inv_eq_one_div, le_div_iff₀ ht_pos]
    linarith [besselK1_mul_self_le_one t ht_pos]
  have hinv_integrable : IntervalIntegrable (fun t : ℝ => t⁻¹) volume z 1 := by
    apply intervalIntegrable_inv (f := id)
    · intro t ht; simp only [id]
      rw [Set.mem_uIcc] at ht
      cases ht with | inl h => linarith [h.1] | inr h => linarith [h.2]
    · exact continuousOn_id
  have h_int_bound : ∫ t in z..1, besselK1 t ≤ -Real.log z := by
    have h1 : ∫ t in z..1, besselK1 t ≤ ∫ t in z..1, t⁻¹ :=
      integral_mono_on hz_small hK1_integrable hinv_integrable (fun t ht => hK1_bound t ht)
    have h2 : ∫ t in z..1, t⁻¹ = Real.log (1 / z) := integral_inv_of_pos hz one_pos
    rw [one_div, Real.log_inv] at h2; linarith
  have hK0_one_le : besselK0 1 ≤ 1 := by
    have h1 := besselK0_lt_besselK1 1 one_pos
    have h2 := besselK1_mul_self_le_one 1 one_pos
    simp at h2; linarith
  calc besselK0 z = besselK0 1 + ∫ t in z..1, besselK1 t := hFTC
    _ ≤ 1 + (-Real.log z) := by linarith [hK0_one_le, h_int_bound]
    _ = 1 - Real.log z := by ring
    _ ≤ |Real.log (z / 2)| + 1 := by
        have hlog_neg : Real.log (z / 2) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
        rw [abs_of_nonpos hlog_neg, Real.log_div (by linarith) (by norm_num)]
        linarith [Real.log_pos (by norm_num : (1:ℝ) < 2)]

/-! ## 8. Integrability of K₀ on (0, ∞) -/

/-- K₀ is integrable on (0, ∞). -/
theorem besselK0_integrable_near_zero :
    IntegrableOn besselK0 (Ioi 0) volume := by
  rw [← Ioc_union_Ioi_eq_Ioi (show (0:ℝ) ≤ 1 from zero_le_one)]
  rw [integrableOn_union]
  have hK0_meas_Ioc : AEStronglyMeasurable besselK0 (volume.restrict (Ioc 0 1)) :=
    (besselK0_continuousOn.mono (fun x hx => Ioc_subset_Ioi_self hx)).aestronglyMeasurable
      measurableSet_Ioc
  have hK0_meas_Ioi : AEStronglyMeasurable besselK0 (volume.restrict (Ioi 1)) :=
    (besselK0_continuousOn.mono (fun x (hx : 1 < x) => show (0 : ℝ) < x by linarith)).aestronglyMeasurable
      measurableSet_Ioi
  refine ⟨?_, ?_⟩
  · -- Part 1: IntegrableOn besselK0 (Ioc 0 1)
    have h_log_int : IntegrableOn (fun z => -Real.log z + (Real.log 2 + 1)) (Ioc 0 1) volume :=
      ((intervalIntegrable_log' (a := 0) (b := 1)).1.neg).add
        (integrableOn_const (hs := measure_Ioc_lt_top.ne))
    apply Integrable.mono' h_log_int hK0_meas_Ioc
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
    simp only [mem_Ioc] at hz
    rw [Real.norm_eq_abs, abs_of_pos (besselK0_pos z hz.1)]
    calc besselK0 z ≤ |Real.log (z / 2)| + 1 := besselK0_near_origin_bound z hz.1 hz.2
      _ ≤ -Real.log z + (Real.log 2 + 1) := by
          have hlog_neg : Real.log (z / 2) ≤ 0 :=
            Real.log_nonpos (by linarith) (by linarith)
          rw [abs_of_nonpos hlog_neg, Real.log_div (by linarith) (by norm_num)]
          linarith [Real.log_pos (by norm_num : (1:ℝ) < 2)]
  · -- Part 2: IntegrableOn besselK0 (Ioi 1)
    apply Integrable.mono' ((integrableOn_exp_neg_Ioi 1).const_mul (Real.sqrt (π / 2)))
      hK0_meas_Ioi
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    simp only [mem_Ioi] at hz
    rw [Real.norm_eq_abs, abs_of_pos (besselK0_pos z (by linarith))]
    calc besselK0 z ≤ Real.sqrt (π / (2 * z)) * exp (-z) :=
          besselK0_asymptotic z (by linarith)
      _ ≤ Real.sqrt (π / 2) * exp (-z) := by
          have h1 : Real.sqrt (π / (2 * z)) ≤ Real.sqrt (π / 2) :=
            Real.sqrt_le_sqrt (div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith))
          nlinarith [exp_pos (-z), Real.sqrt_nonneg (π / 2)]

/-! ## 9. Schwinger integral = 2K₀(mr) -/

/-- Helper: exp substitution on Ioi.
    ∫₀^∞ g(exp(t)) · exp(t) dt = ∫₁^∞ g(s) ds. -/
private lemma integral_comp_exp_Ioi_helper {g : ℝ → ℝ}
    (hg_cont : ContinuousOn g (Ioi 0))
    (hg_int : IntegrableOn g (Ici 1) volume)
    (hcomp_int : IntegrableOn (fun t => g (exp t) * exp t) (Ici 0) volume) :
    ∫ t in Ioi (0:ℝ), g (exp t) * exp t = ∫ s in Ioi (1:ℝ), g s := by
  rw [show (1:ℝ) = exp 0 from (exp_zero).symm]
  have h4 : exp '' Ioi 0 = Ioi 1 := by
    ext y; simp only [mem_image, mem_Ioi]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact one_lt_exp_iff.mpr hx
    · intro hy; exact ⟨Real.log y, Real.log_pos hy, Real.exp_log (by linarith)⟩
  have h5 : exp '' Ici 0 = Ici 1 := by
    ext y; simp only [mem_image, mem_Ici]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact le_of_eq (by simp) |>.trans (exp_le_exp.mpr hx)
    · intro hy; exact ⟨Real.log y, Real.log_nonneg (by linarith), Real.exp_log (by linarith)⟩
  exact integral_comp_mul_deriv_Ioi continuous_exp.continuousOn tendsto_exp_atTop
    (fun x _ => (hasDerivAt_exp x).hasDerivWithinAt)
    (h4 ▸ hg_cont.mono (Ioi_subset_Ioi (by linarith : (0:ℝ) ≤ 1)))
    (h5 ▸ hg_int) hcomp_int

private lemma schwinger_integrand_integrableOn_Ioi (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun s => (1/s) * exp (-a * (s + s⁻¹))) (Ioi 1) volume := by
  apply integrable_of_isBigO_exp_neg (b := a) ha
  · apply ContinuousOn.mul
    · exact continuousOn_const.div continuousOn_id
        (fun x hx => ne_of_gt (by linarith [mem_Ici.mp hx] : 0 < x)
                                  )
    · exact continuous_exp.comp_continuousOn
        (continuousOn_const.mul (continuousOn_id.add
          (continuousOn_inv₀.mono (fun x hx =>
            ne_of_gt (by linarith [mem_Ici.mp hx] : 0 < x)))))
  · rw [Asymptotics.isBigO_iff]; use 1; rw [Filter.eventually_atTop]; use 1
    intro s hs
    simp only [Real.norm_eq_abs, one_mul]
    rw [abs_of_nonneg (mul_nonneg (div_nonneg (by norm_num) (by linarith)) (exp_pos _).le),
        abs_of_pos (exp_pos _)]
    calc 1 / s * exp (-a * (s + s⁻¹))
        ≤ 1 * exp (-a * s) := by
          apply mul_le_mul
          · exact div_le_one_of_le₀ (by linarith) (by linarith)
          · apply exp_le_exp.mpr; nlinarith [inv_pos.mpr (show 0 < s by linarith)]
          · exact (exp_pos _).le
          · linarith
      _ = exp (-a * s) := one_mul _

private lemma mul_exp_neg_le_one (t : ℝ) : t * exp (-t) ≤ 1 := by
  calc t * exp (-t) ≤ exp t * exp (-t) :=
        mul_le_mul_of_nonneg_right (add_one_le_exp t |>.trans' (by linarith)) (exp_pos _).le
    _ = 1 := by rw [← exp_add]; simp

private lemma schwinger_integrand_integrableOn_Ioc (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun s => (1/s) * exp (-a * (s + s⁻¹))) (Ioc 0 1) volume := by
  have hdom : IntegrableOn (fun (_ : ℝ) => (1/a : ℝ)) (Ioc 0 1) volume :=
    integrableOn_const (hs := measure_Ioc_lt_top.ne)
  apply Integrable.mono' hdom
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioc
    apply ContinuousOn.mul
    · exact continuousOn_const.div continuousOn_id
        (fun x hx => ne_of_gt (mem_Ioc.mp hx).1)
    · exact continuous_exp.comp_continuousOn
        (continuousOn_const.mul (continuousOn_id.add
          (continuousOn_inv₀.mono (fun x hx =>
            ne_of_gt (mem_Ioc.mp hx).1))))
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have ⟨hs_pos, hs_le⟩ := mem_Ioc.mp hs
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (div_nonneg (by norm_num) hs_pos.le) (exp_pos _).le)]
    calc 1 / s * exp (-a * (s + s⁻¹))
        ≤ 1 / s * exp (-a * s⁻¹) := by
          apply mul_le_mul_of_nonneg_left
          · apply exp_le_exp.mpr; nlinarith
          · exact div_nonneg (by norm_num) hs_pos.le
      _ = (1 / a) * ((a / s) * exp (-(a / s))) := by field_simp
      _ ≤ 1 / a := by
          have h1 := mul_exp_neg_le_one (a / s)
          have h2 : 0 < 1 / a := div_pos one_pos ha
          calc (1 / a) * ((a / s) * exp (-(a / s)))
              ≤ (1 / a) * 1 := mul_le_mul_of_nonneg_left h1 h2.le
            _ = 1 / a := mul_one _

private lemma self_reciprocal_integral (a : ℝ) (ha : 0 < a) :
    ∫ s in Ioi (0:ℝ), (1/s) * exp (-a * (s + s⁻¹)) =
    2 * ∫ s in Ioi (1:ℝ), (1/s) * exp (-a * (s + s⁻¹)) := by
  have h_split : ∫ s in Ioi (0:ℝ), (1/s) * exp (-a * (s + s⁻¹)) =
      (∫ s in Ioc 0 1, (1/s) * exp (-a * (s + s⁻¹))) +
      ∫ s in Ioi 1, (1/s) * exp (-a * (s + s⁻¹)) := by
    rw [← (Ioc_union_Ioi_eq_Ioi zero_le_one)]
    exact integral_union_ae (Ioc_disjoint_Ioi le_rfl |>.aedisjoint)
      measurableSet_Ioi.nullMeasurableSet
      (schwinger_integrand_integrableOn_Ioc a ha)
      (schwinger_integrand_integrableOn_Ioi a ha)
  have h_Ioc_Ioo : ∫ s in Ioc 0 1, (1/s) * exp (-a * (s + s⁻¹)) =
      ∫ s in Ioo 0 1, (1/s) * exp (-a * (s + s⁻¹)) := integral_Ioc_eq_integral_Ioo
  have h_image : (fun x : ℝ => x⁻¹) '' (Ioi 1) = Ioo 0 1 := by
    ext y; simp only [mem_image, mem_Ioi, mem_Ioo]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact ⟨by positivity, inv_lt_one_of_one_lt₀ hx⟩
    · intro ⟨hy0, hy1⟩; exact ⟨y⁻¹, one_lt_inv_iff₀.mpr ⟨hy0, hy1⟩, inv_inv y⟩
  set h := fun s : ℝ => (1/s) * exp (-a * (s + s⁻¹))
  have h_cov := integral_image_eq_integral_deriv_smul_of_antitone (F := ℝ)
    measurableSet_Ioi
    (fun x hx => (hasDerivAt_inv (ne_of_gt (by linarith [mem_Ioi.mp hx] : 0 < x))).hasDerivWithinAt)
    (inv_antitoneOn_Ioi.mono (Ioi_subset_Ioi zero_le_one))
    h
  rw [h_image] at h_cov
  simp only [neg_neg, smul_eq_mul] at h_cov
  have h_eq : ∀ x ∈ Ioi (1:ℝ), (x ^ 2)⁻¹ * h (x⁻¹) = h x := by
    intro x hx
    show (x ^ 2)⁻¹ * ((1/x⁻¹) * exp (-a * (x⁻¹ + (x⁻¹)⁻¹))) =
      (1/x) * exp (-a * (x + x⁻¹))
    simp only [inv_inv, one_div (x⁻¹), add_comm (x⁻¹)]
    rw [one_div, ← mul_assoc]; congr 1
    rw [sq, mul_inv, mul_assoc, inv_mul_cancel₀ (ne_of_gt (by linarith [mem_Ioi.mp hx])), mul_one]
  rw [setIntegral_congr_fun measurableSet_Ioi h_eq] at h_cov
  rw [h_split, h_Ioc_Ioo, h_cov, two_mul]

/-- Schwinger parameter integral equals 2K₀(mr).
    ∫₀^∞ (1/t) exp(-m²t - r²/(4t)) dt = 2 K₀(mr)   (G&R 3.471.9). -/
theorem schwingerIntegral_eq_besselK0 (m r : ℝ) (hm : 0 < m) (hr : 0 < r) :
    ∫ t in Ioi 0, (1 / t) * exp (-m^2 * t - r^2 / (4 * t)) =
    2 * besselK0 (m * r) := by
  set a := m * r / 2
  set c := r / (2 * m)
  have hc : 0 < c := by positivity
  have ha : 0 < a := by positivity
  have hmr : 0 < m * r := mul_pos hm hr
  set g := fun t : ℝ => (1 / t) * exp (-m ^ 2 * t - r ^ 2 / (4 * t))
  set h := fun s : ℝ => (1 / s) * exp (-a * (s + s⁻¹))
  -- STEP 1: Linear scaling ∫ g(t) dt = ∫ h(s) ds via t = c*s
  have halg : ∀ s ∈ Ioi (0:ℝ), g (c * s) = c⁻¹ * h s := by
    intro s hs; simp only [g, h, mem_Ioi] at *
    have h1 : (1 : ℝ) / (c * s) = c⁻¹ * (1 / s) := by field_simp
    have h2 : -m ^ 2 * (c * s) - r ^ 2 / (4 * (c * s)) = -a * (s + s⁻¹) := by
      simp only [a, c]; field_simp; ring
    rw [h1, h2, mul_assoc]
  have hscale := MeasureTheory.integral_comp_mul_left_Ioi g 0 hc
  simp only [mul_zero] at hscale
  rw [setIntegral_congr_fun measurableSet_Ioi halg, MeasureTheory.integral_const_mul,
      smul_eq_mul] at hscale
  have step1 : ∫ t in Ioi (0:ℝ), g t = ∫ s in Ioi (0:ℝ), h s :=
    (mul_left_cancel₀ (inv_ne_zero hc.ne') hscale).symm
  -- STEP 2: Exp substitution + K₀ definition
  have hh_cont : ContinuousOn h (Ioi 0) := by
    apply ContinuousOn.mul
    · exact continuousOn_const.div continuousOn_id (fun x hx => ne_of_gt (mem_Ioi.mp hx))
    · exact continuous_exp.comp_continuousOn
        ((continuous_const.continuousOn).mul
          (continuousOn_id.add (continuousOn_inv₀.mono (fun x hx => ne_of_gt (mem_Ioi.mp hx)))))
  have hh_Ici : IntegrableOn h (Ici 1) volume :=
    (schwinger_integrand_integrableOn_Ioi a ha).congr_set_ae Ioi_ae_eq_Ici.symm
  have h_comp : ∀ t : ℝ, h (exp t) * exp t = exp (-(m * r) * cosh t) := by
    intro t; simp only [h, one_div]
    rw [mul_right_comm, inv_mul_cancel₀ (exp_ne_zero t), one_mul,
        show (exp t : ℝ)⁻¹ = exp (-t) from (exp_neg t).symm]
    congr 1; rw [Real.cosh_eq]; ring
  have h_cosh_int : IntegrableOn (fun t => exp (-(m * r) * cosh t)) (Ici 0) volume := by
    apply Integrable.mono' ((integrableOn_gaussian_Ici hmr).smul (exp (-(m * r))))
    · exact (continuous_exp.comp (continuous_const.mul continuous_cosh)).continuousOn.aestronglyMeasurable measurableSet_Ici
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), Pi.smul_apply, smul_eq_mul]
      exact exp_neg_cosh_le_gaussian (m * r) t hmr
  have hcomp_int : IntegrableOn (fun t => h (exp t) * exp t) (Ici 0) volume := by
    rw [show (fun t => h (exp t) * exp t) = fun t => exp (-(m * r) * cosh t) from funext h_comp]
    exact h_cosh_int
  have step3 : ∫ s in Ioi (1:ℝ), h s = besselK0 (m * r) := by
    have h_exp := (integral_comp_exp_Ioi_helper hh_cont hh_Ici hcomp_int).symm
    rw [show (fun t => h (exp t) * exp t) = fun t => exp (-(m * r) * cosh t) from
      funext h_comp] at h_exp
    rw [h_exp, besselK0, integral_Ici_eq_integral_Ioi]
  calc ∫ t in Ioi (0:ℝ), g t
      = ∫ s in Ioi (0:ℝ), h s := step1
    _ = 2 * ∫ s in Ioi (1:ℝ), h s := self_reciprocal_integral a ha
    _ = 2 * besselK0 (m * r) := by rw [step3]

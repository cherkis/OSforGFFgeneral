/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Modified Bessel function `K₀` and the proper-time (Schwinger) evaluation

The radial profile of the free covariance in two dimensions is `(1/(2π)) · K₀(m r)`, where `K₀` is
the modified Bessel function of the second kind of order zero. This file defines `K₀` through its
cosh integral representation and evaluates the underlying proper-time integral in closed form:

`∫₀^∞ (1/t) · exp(-m² t - r²/(4t)) dt = 2 · K₀(m r)`   (Gradshteyn–Ryzhik 3.471.9).

The evaluation proceeds by the linear scaling `t = (r/(2m)) · s`, which turns the integrand into the
symmetric kernel `(1/s) · exp(-a (s + s⁻¹))` with `a = m r / 2`; the reciprocal involution `s ↦ s⁻¹`
folds `(0, ∞)` onto `(1, ∞)` (doubling the integral), and the substitution `s = eᵗ` matches the
cosh representation of `K₀`.
-/

open MeasureTheory Set Filter Real Topology Asymptotics intervalIntegral

/-- The modified Bessel function `K₀(z)` via its cosh integral representation,
    `K₀(z) = ∫₀^∞ exp(-z cosh t) dt`. Well-defined and positive for `z > 0`. -/
noncomputable def besselK0 (z : ℝ) : ℝ :=
  ∫ t : ℝ in Ici 0, exp (-z * cosh t)

/-- `cosh t ≥ 1 + t²/2` for all `t`. -/
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

/-- `exp(-z cosh t) ≤ exp(-z) · exp(-(z/2) t²)` for `z > 0`. -/
private lemma exp_neg_cosh_le_gaussian (z t : ℝ) (hz : 0 < z) :
    exp (-z * cosh t) ≤ exp (-z) * exp (-(z/2) * t^2) := by
  rw [← exp_add]; exact exp_le_exp.mpr (by nlinarith [cosh_ge_one_add_sq_div_two t])

/-- The Gaussian `exp(-(z/2) t²)` is integrable on `[0, ∞)` for `z > 0`. -/
private lemma integrableOn_gaussian_Ici {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun t => exp (-(z/2) * t^2)) (Ici 0) volume :=
  (integrable_exp_neg_mul_sq (by linarith : 0 < z/2)).integrableOn

/-- Exponential substitution on `Ioi`: `∫₀^∞ g(exp t) · exp t dt = ∫₁^∞ g(s) ds`. -/
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
    exact setIntegral_union₀ (Ioc_disjoint_Ioi le_rfl |>.aedisjoint)
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
  have h_cov := integral_image_eq_integral_deriv_smul_of_antitoneOn (F := ℝ)
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

/-- The Schwinger proper-time integral evaluates to `2 K₀(m r)`:
    `∫₀^∞ (1/t) exp(-m² t - r²/(4t)) dt = 2 K₀(m r)`   (Gradshteyn–Ryzhik 3.471.9). -/
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

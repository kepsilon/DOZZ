/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFFStructure.CirclePotential
public import DOZZ.GMC.CircleAverage
public import DOZZ.GMC.CirclePotential
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Circle-average covariance kernels

At circle cutoff `r` (radius `ρ = e^{-r}`) the covariance of two circle averages of the equator
field is `Λ_r(x - u) + h_r(x) + h_r(u)`, where `h_r` is the circle average of `log |·|₊` and
`Λ_r(w)` is the circle average over the circle of center `w` of `-log max(ρ, |·|)`. The kernel
`Λ_r` is even, equals `-log |w|` for `|w| ≥ 2ρ`, is `1/ρ`-Lipschitz, and is differentiable away
from `0` with derivative of norm at most `2/|w|`. These are the inputs for the symmetric
regularization of the screening Ward identity. -/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Real

namespace DOZZ.Proofs

/-- The truncated logarithmic potential `-log max(ρ, |v|)`. -/
noncomputable def bpzTruncLog (r : ℝ) (v : ℂ) : ℝ := -Real.log (max (Real.exp (-r)) ‖v‖)

/-- The logarithmic part `Λ_r` of the circle-average covariance. -/
noncomputable def bpzLam (r : ℝ) (w : ℂ) : ℝ := ∫ a, bpzTruncLog r a ∂circleMeasure w r

/-- The circle average `h_r` of `log |·|₊`. -/
noncomputable def bpzPin (r : ℝ) (x : ℂ) : ℝ := ∫ a, Real.log (normPlus a) ∂circleMeasure x r

theorem measurable_bpzTruncLog (r : ℝ) : Measurable (bpzTruncLog r) := by
  unfold bpzTruncLog
  exact (Real.measurable_log.comp (measurable_const.max measurable_norm)).neg

theorem continuous_bpzTruncLog (r : ℝ) : Continuous (bpzTruncLog r) := by
  unfold bpzTruncLog
  refine (Real.continuousOn_log.comp_continuous (continuous_const.max continuous_norm)
    fun v => ?_).neg
  exact (lt_of_lt_of_le (Real.exp_pos (-r)) (le_max_left _ _)).ne'

/-- The circle integral is the average over the parameter interval. -/
theorem bpz_integral_circleMeasure_eq (c : ℂ) (r : ℝ) (f : ℂ → ℝ) (hf : Measurable f) :
    (∫ a, f a ∂circleMeasure c r) =
      (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..2 * π, f (circleMap c (Real.exp (-r)) θ) := by
  rw [integral_circleMeasure_eq_circleAverage c r f hf, Real.circleAverage_def, smul_eq_mul]

/-- The kernel `Λ_r` as an average over the parameter interval. -/
theorem bpzLam_eq_interval (r : ℝ) (w : ℂ) :
    bpzLam r w = (2 * π)⁻¹ *
      ∫ θ in (0 : ℝ)..2 * π, bpzTruncLog r (w + Real.exp (-r) * Complex.exp (θ * Complex.I)) := by
  rw [bpzLam, bpz_integral_circleMeasure_eq w r _ (measurable_bpzTruncLog r)]
  rfl

/-- Translating the averaging circle translates the argument. -/
theorem bpz_integral_circleMeasure_sub (x u : ℂ) (r : ℝ) (f : ℂ → ℝ) (hf : Measurable f) :
    (∫ a, f (a - u) ∂circleMeasure x r) = ∫ a, f a ∂circleMeasure (x - u) r := by
  have hfu : Measurable fun a : ℂ => f (a - u) := hf.comp (measurable_id.sub_const u)
  rw [bpz_integral_circleMeasure_eq x r (fun a => f (a - u)) hfu,
    bpz_integral_circleMeasure_eq (x - u) r f hf]
  congr 2
  funext θ
  congr 1
  simp only [circleMap]
  ring

/-- The kernel `Λ_r` is even. -/
theorem bpzLam_neg (r : ℝ) (w : ℂ) : bpzLam r (-w) = bpzLam r w := by
  rw [bpzLam_eq_interval, bpzLam_eq_interval]
  congr 1
  set g : ℝ → ℝ := fun θ => bpzTruncLog r (w + Real.exp (-r) * Complex.exp (θ * Complex.I))
  have hper : Function.Periodic g (2 * π) := by
    intro θ
    simp only [g]
    congr 2
    rw [show ((θ + 2 * π : ℝ) : ℂ) * Complex.I = θ * Complex.I + 2 * π * Complex.I by
      push_cast; ring, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have hshift : ∀ θ : ℝ, bpzTruncLog r (-w + Real.exp (-r) * Complex.exp (θ * Complex.I)) =
      g (θ + π) := by
    intro θ
    simp only [g, bpzTruncLog]
    congr 3
    rw [← norm_neg]
    congr 1
    rw [show ((θ + π : ℝ) : ℂ) * Complex.I = θ * Complex.I + π * Complex.I by push_cast; ring,
      Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  simp_rw [hshift]
  rw [intervalIntegral.integral_comp_add_right g π]
  have h := hper.intervalIntegral_add_eq π 0
  simp only [zero_add] at h
  rw [show π + 2 * π = π + 2 * π by rfl] at h
  rw [show (0 : ℝ) + π = π by ring, show 2 * π + π = π + 2 * π by ring, h]

theorem bpzTruncLog_le (r : ℝ) (v : ℂ) : bpzTruncLog r v ≤ r := by
  unfold bpzTruncLog
  have h := Real.log_le_log (Real.exp_pos (-r)) (le_max_left (Real.exp (-r)) ‖v‖)
  rw [Real.log_exp] at h
  linarith

/-- The truncated potential is `e^r`-Lipschitz. -/
theorem abs_bpzTruncLog_sub_le (r : ℝ) (v v' : ℂ) :
    |bpzTruncLog r v - bpzTruncLog r v'| ≤ Real.exp r * ‖v - v'‖ := by
  unfold bpzTruncLog
  have hρ : 0 < Real.exp (-r) := Real.exp_pos _
  have h := CirclePotential.abs_log_sub_log_le hρ (le_max_left _ ‖v‖) (le_max_left _ ‖v'‖)
  have hmax : |max (Real.exp (-r)) ‖v‖ - max (Real.exp (-r)) ‖v'‖| ≤ ‖v - v'‖ :=
    by rw [max_comm _ ‖v‖, max_comm _ ‖v'‖]
       exact (abs_max_sub_max_le_abs _ _ _).trans (abs_norm_sub_norm_le v v')
  rw [show -Real.log (max (Real.exp (-r)) ‖v‖) - -Real.log (max (Real.exp (-r)) ‖v'‖) =
    -(Real.log (max (Real.exp (-r)) ‖v‖) - Real.log (max (Real.exp (-r)) ‖v'‖)) by ring,
    abs_neg]
  calc _ ≤ |max (Real.exp (-r)) ‖v‖ - max (Real.exp (-r)) ‖v'‖| / Real.exp (-r) := h
    _ ≤ ‖v - v'‖ / Real.exp (-r) := by gcongr
    _ = Real.exp r * ‖v - v'‖ := by
        rw [Real.exp_neg, div_inv_eq_mul, mul_comm]

/-- The truncated potential is integrable on every circle. -/
theorem integrable_bpzTruncLog_comp (x u : ℂ) (r : ℝ) :
    Integrable (fun a => bpzTruncLog r (a - u)) (circleMeasure x r) :=
  integrable_circleMeasure_of_circleIntegrable x r
    ((measurable_bpzTruncLog r).comp (measurable_id.sub_const u))
    ((continuous_bpzTruncLog r).comp (continuous_id.sub continuous_const)).continuousOn.circleIntegrable'

/-- The inner circle integral of the equator kernel. -/
theorem bpz_integral_gffKernel_circle (a u : ℂ) (r : ℝ) :
    (∫ b, gffKernel a b ∂circleMeasure u r) =
      bpzTruncLog r (a - u) + Real.log (normPlus a) + bpzPin r u := by
  let _ := circleMeasure_isProbability u r
  have h1 : Integrable (fun b : ℂ => -Real.log ‖a - b‖) (circleMeasure u r) := by
    have := integrable_log_norm_sub_circleMeasure u a r
    refine this.neg.congr (Filter.Eventually.of_forall fun b => ?_)
    simp only [Pi.neg_apply, norm_sub_rev b a]
  have h2 : Integrable (fun _ : ℂ => Real.log (normPlus a)) (circleMeasure u r) :=
    integrable_const _
  have h3 := integrable_log_normPlus_circleMeasure u r
  have h12 : Integrable (fun b : ℂ => -Real.log ‖a - b‖ + Real.log (normPlus a))
      (circleMeasure u r) := h1.add h2
  have hsplit : (fun b => gffKernel a b) =
      fun b => (-Real.log ‖a - b‖ + Real.log (normPlus a)) + Real.log (normPlus b) := rfl
  rw [hsplit, integral_add h12 h3, integral_add h1 h2, integral_neg,
    integral_log_norm_rev_sub_circleMeasure u a r, integral_const, probReal_univ, one_smul]
  unfold bpzTruncLog bpzPin
  rw [norm_sub_rev u a]

/-- The covariance of two circle averages at a common cutoff. -/
theorem bpz_circle_covariance {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (x u : ℂ) (r : ℝ) :
    gaussianCovariance P (fun ω => Xc ω x r) (fun ω => Xc ω u r) =
      bpzLam r (x - u) + bpzPin r x + bpzPin r u := by
  let _ := circleMeasure_isProbability x r
  rw [isCircleAverage_covariance P X hX Xc hXc x u r r]
  simp_rw [bpz_integral_gffKernel_circle _ u r]
  have h1 := integrable_bpzTruncLog_comp x u r
  have h2 := integrable_log_normPlus_circleMeasure x r
  have h3 : Integrable (fun _ : ℂ => bpzPin r u) (circleMeasure x r) := integrable_const _
  have h12 : Integrable (fun a : ℂ => bpzTruncLog r (a - u) + Real.log (normPlus a))
      (circleMeasure x r) := h1.add h2
  rw [integral_add h12 h3, integral_add h1 h2,
    bpz_integral_circleMeasure_sub x u r _ (measurable_bpzTruncLog r), integral_const,
    probReal_univ, one_smul]
  rfl

/-- Away from the diagonal the kernel is exactly `-log |w|`. -/
theorem bpzLam_eq_neg_log (r : ℝ) {w : ℂ} (hw : 2 * Real.exp (-r) ≤ ‖w‖) :
    bpzLam r w = -Real.log ‖w‖ := by
  have hρ : 0 < Real.exp (-r) := Real.exp_pos _
  have hae : (fun a => bpzTruncLog r a) =ᵐ[circleMeasure w r] fun a => -Real.log ‖a - 0‖ := by
    filter_upwards [ae_mem_sphere_circleMeasure w r] with a ha
    rw [Metric.mem_sphere, dist_eq_norm] at ha
    have hge : Real.exp (-r) ≤ ‖a‖ := by
      have := norm_sub_norm_le w a
      rw [norm_sub_rev] at this
      linarith
    simp only [bpzTruncLog, sub_zero, max_eq_right hge]
  rw [bpzLam, integral_congr_ae hae, integral_neg, integral_log_norm_sub_circleMeasure,
    sub_zero, max_eq_right (by linarith)]

/-- The kernel `Λ_r` is `e^r`-Lipschitz. -/
theorem abs_bpzLam_sub_le (r : ℝ) (w w' : ℂ) :
    |bpzLam r w - bpzLam r w'| ≤ Real.exp r * ‖w - w'‖ := by
  rw [bpzLam_eq_interval, bpzLam_eq_interval, ← mul_sub,
    ← intervalIntegral.integral_sub]
  rotate_left
  · exact ((continuous_bpzTruncLog r).comp (continuous_const.add
      (continuous_const.mul (Complex.continuous_exp.comp
        (Complex.continuous_ofReal.mul continuous_const))))).intervalIntegrable _ _
  · exact ((continuous_bpzTruncLog r).comp (continuous_const.add
      (continuous_const.mul (Complex.continuous_exp.comp
        (Complex.continuous_ofReal.mul continuous_const))))).intervalIntegrable _ _
  have hpi : 0 < 2 * π := by positivity
  rw [abs_mul, abs_of_pos (inv_pos.mpr hpi)]
  have hb : ∀ θ ∈ Set.uIoc 0 (2 * π),
      ‖bpzTruncLog r (w + Real.exp (-r) * Complex.exp (θ * Complex.I)) -
        bpzTruncLog r (w' + Real.exp (-r) * Complex.exp (θ * Complex.I))‖ ≤
        Real.exp r * ‖w - w'‖ := by
    intro θ _
    rw [Real.norm_eq_abs]
    refine (abs_bpzTruncLog_sub_le r _ _).trans (le_of_eq ?_)
    congr 2
    ring
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos hpi] at hint
  calc (2 * π)⁻¹ * |∫ θ in (0 : ℝ)..2 * π, _|
      ≤ (2 * π)⁻¹ * (Real.exp r * ‖w - w'‖ * (2 * π)) := by gcongr
    _ = Real.exp r * ‖w - w'‖ := by field_simp

/-- The derivative of the truncated potential off its truncation circle. -/
noncomputable def bpzTruncLogDeriv (r : ℝ) (v : ℂ) : ℂ →L[ℝ] ℝ :=
  if Real.exp (-r) < ‖v‖ then (-(‖v‖ ^ 2)⁻¹) • innerSL ℝ v else 0

theorem hasFDerivAt_neg_log_norm {v : ℂ} (hv : v ≠ 0) :
    HasFDerivAt (fun x : ℂ => -Real.log ‖x‖) ((-(‖v‖ ^ 2)⁻¹) • innerSL ℝ v) v := by
  have hsq : HasFDerivAt (fun x : ℂ => ‖x‖ ^ 2) (2 • innerSL ℝ v) v :=
    (hasStrictFDerivAt_norm_sq v).hasFDerivAt
  have hne : ‖v‖ ^ 2 ≠ 0 := by positivity
  have hlog := (hsq.log hne).const_mul (-(1 / 2 : ℝ))
  have hfun : (fun x : ℂ => -(1 / 2 : ℝ) * Real.log (‖x‖ ^ 2)) = fun x => -Real.log ‖x‖ := by
    funext x
    rw [Real.log_pow]
    push_cast
    ring
  rw [hfun] at hlog
  convert hlog using 1
  ext h
  simp only [smul_apply, smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

theorem hasFDerivAt_bpzTruncLog (r : ℝ) {v : ℂ} (hv : ‖v‖ ≠ Real.exp (-r)) :
    HasFDerivAt (bpzTruncLog r) (bpzTruncLogDeriv r v) v := by
  rcases lt_or_gt_of_ne hv with hlt | hgt
  · have hev : bpzTruncLog r =ᶠ[𝓝 v] fun _ => -Real.log (Real.exp (-r)) := by
      have : ∀ᶠ x in 𝓝 v, ‖x‖ < Real.exp (-r) :=
        (continuous_norm.tendsto v).eventually (gt_mem_nhds hlt)
      filter_upwards [this] with x hx
      simp only [bpzTruncLog, max_eq_left hx.le]
    have hd : bpzTruncLogDeriv r v = 0 := by
      simp only [bpzTruncLogDeriv, not_lt.mpr hlt.le, ↓reduceIte]
    rw [hd]
    exact (hasFDerivAt_const _ v).congr_of_eventuallyEq hev
  · have hv0 : v ≠ 0 := by
      intro h; rw [h, norm_zero] at hgt; exact absurd hgt (not_lt.mpr (Real.exp_pos _).le)
    have hev : bpzTruncLog r =ᶠ[𝓝 v] fun x => -Real.log ‖x‖ := by
      have : ∀ᶠ x in 𝓝 v, Real.exp (-r) < ‖x‖ :=
        (continuous_norm.tendsto v).eventually (lt_mem_nhds hgt)
      filter_upwards [this] with x hx
      simp only [bpzTruncLog, max_eq_right hx.le]
    have hd : bpzTruncLogDeriv r v = (-(‖v‖ ^ 2)⁻¹) • innerSL ℝ v := by
      simp only [bpzTruncLogDeriv, hgt, ↓reduceIte]
    rw [hd]
    exact (hasFDerivAt_neg_log_norm hv0).congr_of_eventuallyEq hev

theorem norm_bpzTruncLogDeriv_le (r : ℝ) (v : ℂ) :
    ‖bpzTruncLogDeriv r v‖ ≤ Real.exp r ∧
      (Real.exp (-r) < ‖v‖ → ‖bpzTruncLogDeriv r v‖ ≤ ‖v‖⁻¹) := by
  unfold bpzTruncLogDeriv
  split_ifs with h
  · have hv : 0 < ‖v‖ := lt_trans (Real.exp_pos _) h
    have hnorm : ‖(-(‖v‖ ^ 2)⁻¹) • innerSL ℝ v‖ = ‖v‖⁻¹ := by
      rw [norm_smul, innerSL_apply_norm, norm_neg, norm_inv, norm_pow, Real.norm_eq_abs,
        abs_of_pos hv]
      field_simp
    rw [hnorm]
    refine ⟨?_, fun _ => le_rfl⟩
    have := (inv_lt_inv₀ hv (Real.exp_pos _)).mpr h
    rw [Real.exp_neg, inv_inv] at this
    exact this.le
  · simp only [norm_zero]
    exact ⟨(Real.exp_pos r).le, fun _ => le_of_lt (inv_pos.mpr (lt_trans (Real.exp_pos _)
      (by assumption)))⟩

/-- The truncation circle is met at countably many parameter values. -/
theorem countable_bpz_truncation_hits (ρ : ℝ) {w : ℂ} (hw : w ≠ 0) :
    {θ : ℝ | ‖w + ρ * Complex.exp (θ * Complex.I)‖ = ρ}.Countable := by
  set S := {θ : ℝ | ‖w + ρ * Complex.exp (θ * Complex.I)‖ = ρ} with hS
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hkey : ∀ θ : ℝ, ‖w + ρ * Complex.exp (θ * Complex.I)‖ ^ 2 =
      ‖w‖ ^ 2 + ρ ^ 2 + 2 * ρ * ‖w‖ * Real.cos (θ - Complex.arg w) := by
    intro θ
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.normSq_apply, Real.cos_sub, Complex.cos_arg hw, Complex.sin_arg]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero, add_zero]
    have hn : ‖w‖ ^ 2 = w.re * w.re + w.im * w.im := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq θ, hn]
  rcases S.eq_empty_or_nonempty with h | ⟨θ₀, hθ₀⟩
  · rw [h]; exact Set.countable_empty
  · have hθ₀' : ‖w + ρ * Complex.exp (θ₀ * Complex.I)‖ = ρ := hθ₀
    have hρ : ρ ≠ 0 := by
      intro h0
      rw [h0, Complex.ofReal_zero, zero_mul, add_zero] at hθ₀'
      exact hwn.ne' hθ₀'
    have hsub : S ⊆ Set.range (fun k : ℤ => θ₀ + 2 * k * π) ∪
        Set.range (fun k : ℤ => 2 * Complex.arg w - θ₀ + 2 * k * π) := by
      intro θ hθ
      have hθ' : ‖w + ρ * Complex.exp (θ * Complex.I)‖ = ρ := hθ
      have h1 := hkey θ
      have h2 := hkey θ₀
      rw [hθ'] at h1
      rw [hθ₀'] at h2
      have hc : Real.cos (θ₀ - Complex.arg w) = Real.cos (θ - Complex.arg w) := by
        have hne : 2 * ρ * ‖w‖ ≠ 0 := by positivity
        apply mul_left_cancel₀ hne
        linarith
      obtain ⟨k, hk | hk⟩ := Real.cos_eq_cos_iff.mp hc
      · left; exact ⟨k, by linarith⟩
      · right; exact ⟨k, by linarith⟩
    exact ((Set.countable_range _).union (Set.countable_range _)).mono hsub

theorem measurable_bpzTruncLogDeriv (r : ℝ) : Measurable (bpzTruncLogDeriv r) := by
  unfold bpzTruncLogDeriv
  refine Measurable.ite (measurableSet_lt measurable_const measurable_norm) ?_ measurable_const
  exact ((measurable_norm.pow_const 2).inv.neg).smul (innerSL ℝ).continuous.measurable

/-- The derivative of `Λ_r` away from the origin. -/
noncomputable def bpzLamDeriv (r : ℝ) (w : ℂ) : ℂ →L[ℝ] ℝ :=
  (2 * π)⁻¹ • ∫ θ in (0 : ℝ)..2 * π,
    bpzTruncLogDeriv r (w + Real.exp (-r) * Complex.exp (θ * Complex.I))

private theorem continuous_bpz_circle_param (w : ℂ) (ρ : ℝ) :
    Continuous fun θ : ℝ => w + ρ * Complex.exp (θ * Complex.I) :=
  continuous_const.add (continuous_const.mul (Complex.continuous_exp.comp
    (Complex.continuous_ofReal.mul continuous_const)))

theorem hasFDerivAt_bpzLam (r : ℝ) {w : ℂ} (hw : w ≠ 0) :
    HasFDerivAt (bpzLam r) (bpzLamDeriv r w) w := by
  set ρ : ℝ := Real.exp (-r) with hρ
  have hfun : bpzLam r = fun x => (2 * π)⁻¹ *
      ∫ θ in (0 : ℝ)..2 * π, bpzTruncLog r (x + ρ * Complex.exp (θ * Complex.I)) := by
    funext x
    exact bpzLam_eq_interval r x
  have hnull : ∀ᵐ θ : ℝ ∂(volume : Measure ℝ),
      ‖w + ρ * Complex.exp ((θ : ℂ) * Complex.I)‖ ≠ ρ := by
    have h0 : (volume : Measure ℝ) {θ : ℝ | ‖w + ρ * Complex.exp ((θ : ℂ) * Complex.I)‖ = ρ}
        = 0 := (countable_bpz_truncation_hits ρ hw).measure_zero _
    refine ae_iff.mpr ?_
    simpa only [ne_eq, not_not] using h0
  have hmain := intervalIntegral.hasFDerivAt_integral_of_dominated_loc_of_lip
    (μ := volume) (a := 0) (b := 2 * π) (s := Set.univ) (x₀ := w)
    (F := fun x θ => bpzTruncLog r (x + ρ * Complex.exp (θ * Complex.I)))
    (F' := fun θ => bpzTruncLogDeriv r (w + ρ * Complex.exp (θ * Complex.I)))
    (bound := fun _ => Real.exp r) Filter.univ_mem
    (Filter.Eventually.of_forall fun x =>
      ((continuous_bpzTruncLog r).comp (continuous_bpz_circle_param x ρ)).aestronglyMeasurable)
    (((continuous_bpzTruncLog r).comp (continuous_bpz_circle_param w ρ)).intervalIntegrable _ _)
    ((measurable_bpzTruncLogDeriv r).comp
      (continuous_bpz_circle_param w ρ).measurable).aestronglyMeasurable
    (Filter.Eventually.of_forall fun θ _ => by
      refine LipschitzOnWith.of_dist_le_mul fun x _ y _ => ?_
      rw [Real.dist_eq, Real.coe_nnabs, abs_of_pos (Real.exp_pos r), dist_eq_norm]
      refine (abs_bpzTruncLog_sub_le r _ _).trans (le_of_eq ?_)
      congr 2
      ring)
    intervalIntegrable_const
    (by
      filter_upwards [hnull] with θ hθ _
      exact (hasFDerivAt_bpzTruncLog r hθ).comp w ((hasFDerivAt_id w).add_const _))
  rw [hfun]
  exact hmain.2.const_mul _

theorem norm_bpzLamDeriv_le (r : ℝ) {w : ℂ} (hw : w ≠ 0) : ‖bpzLamDeriv r w‖ ≤ 2 / ‖w‖ := by
  set ρ : ℝ := Real.exp (-r) with hρdef
  have hρ : 0 < ρ := Real.exp_pos _
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hpt : ∀ θ : ℝ, ‖bpzTruncLogDeriv r (w + ρ * Complex.exp (θ * Complex.I))‖ ≤ 2 / ‖w‖ := by
    intro θ
    set v := w + ρ * Complex.exp (θ * Complex.I)
    obtain ⟨hb1, hb2⟩ := norm_bpzTruncLogDeriv_le r v
    have hvw : ‖w‖ - ρ ≤ ‖v‖ := by
      have h1 := norm_sub_norm_le w (-(ρ * Complex.exp (θ * Complex.I)))
      rw [sub_neg_eq_add, norm_neg, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ] at h1
      linarith
    by_cases hv : ρ < ‖v‖
    · rcases le_or_gt (2 * ρ) ‖w‖ with h2 | h2
      · refine (hb2 hv).trans ?_
        have hv2 : ‖w‖ / 2 ≤ ‖v‖ := by linarith
        rw [div_eq_mul_inv, ← one_div]
        calc 1 / ‖v‖ ≤ 1 / (‖w‖ / 2) := one_div_le_one_div_of_le (by positivity) hv2
          _ = 2 / ‖w‖ := by field_simp
      · refine hb1.trans ?_
        have : Real.exp r = ρ⁻¹ := by rw [hρdef, Real.exp_neg, inv_inv]
        rw [this, le_div_iff₀ hwn]
        calc ρ⁻¹ * ‖w‖ ≤ ρ⁻¹ * (2 * ρ) := by gcongr
          _ = 2 := by field_simp
    · have hv' : ¬ Real.exp (-r) < ‖v‖ := hv
      have : bpzTruncLogDeriv r v = 0 := by
        simp only [bpzTruncLogDeriv, hv', ↓reduceIte]
      rw [this, norm_zero]
      positivity
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := 2 * π) (fun θ (_ : θ ∈ Set.uIoc 0 (2 * π)) => hpt θ)
  rw [sub_zero, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at hint
  unfold bpzLamDeriv
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (by positivity : (0 : ℝ) < 2 * π))]
  calc (2 * π)⁻¹ * ‖∫ θ in (0 : ℝ)..2 * π, _‖ ≤ (2 * π)⁻¹ * (2 / ‖w‖ * (2 * π)) := by gcongr
    _ = 2 / ‖w‖ := by field_simp

/-- Away from the diagonal the derivative is that of `-log |w|`. -/
theorem bpzLamDeriv_eq_of_far (r : ℝ) {w : ℂ} (hw : 2 * Real.exp (-r) < ‖w‖) :
    bpzLamDeriv r w = (-(‖w‖ ^ 2)⁻¹) • innerSL ℝ w := by
  have hw0 : w ≠ 0 := by
    intro h; rw [h, norm_zero] at hw; linarith [Real.exp_pos (-r)]
  have hev : bpzLam r =ᶠ[𝓝 w] fun x => -Real.log ‖x‖ := by
    have : ∀ᶠ x in 𝓝 w, 2 * Real.exp (-r) < ‖x‖ :=
      (continuous_norm.tendsto w).eventually (lt_mem_nhds hw)
    filter_upwards [this] with x hx
    exact bpzLam_eq_neg_log r hx.le
  exact (hasFDerivAt_bpzLam r hw0).unique
    ((hasFDerivAt_neg_log_norm hw0).congr_of_eventuallyEq hev)

theorem abs_log_normPlus_sub_le' (a b : ℂ) :
    |Real.log (normPlus a) - Real.log (normPlus b)| ≤ ‖a - b‖ := by
  have h := CirclePotential.abs_log_sub_log_le one_pos (le_max_left 1 ‖a‖) (le_max_left 1 ‖b‖)
  have hmax : |max 1 ‖a‖ - max 1 ‖b‖| ≤ ‖a - b‖ := by
    rw [max_comm 1 ‖a‖, max_comm 1 ‖b‖]
    exact (abs_max_sub_max_le_abs _ _ _).trans (abs_norm_sub_norm_le a b)
  unfold normPlus
  rw [div_one] at h
  exact h.trans hmax

/-- The pinning average is within `e^{-r}` of `log |x|₊`. -/
theorem abs_bpzPin_sub_le (r : ℝ) (x : ℂ) :
    |bpzPin r x - Real.log (normPlus x)| ≤ Real.exp (-r) := by
  let _ := circleMeasure_isProbability x r
  have hint := integrable_log_normPlus_circleMeasure x r
  have hconst : Integrable (fun _ : ℂ => Real.log (normPlus x)) (circleMeasure x r) :=
    integrable_const _
  have hdiff : bpzPin r x - Real.log (normPlus x) =
      ∫ a, (Real.log (normPlus a) - Real.log (normPlus x)) ∂circleMeasure x r := by
    rw [integral_sub hint hconst, integral_const, probReal_univ, one_smul]
    rfl
  rw [hdiff]
  calc |∫ a, (Real.log (normPlus a) - Real.log (normPlus x)) ∂circleMeasure x r|
      ≤ ∫ a, |Real.log (normPlus a) - Real.log (normPlus x)| ∂circleMeasure x r :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _a, Real.exp (-r) ∂circleMeasure x r := by
        apply integral_mono_ae (hint.sub hconst).abs (integrable_const _)
        filter_upwards [ae_mem_sphere_circleMeasure x r] with a ha
        rw [Metric.mem_sphere, dist_eq_norm] at ha
        exact (abs_log_normPlus_sub_le' a x).trans ha.le
    _ = Real.exp (-r) := by rw [integral_const, probReal_univ, one_smul]

/-- The circle-averaged equator kernel seen from a fixed point. -/
theorem bpz_integral_gffKernel_circle_left (x u : ℂ) (r : ℝ) :
    (∫ a, gffKernel a u ∂circleMeasure x r) =
      bpzTruncLog r (x - u) + bpzPin r x + Real.log (normPlus u) := by
  let _ := circleMeasure_isProbability x r
  have h1 : Integrable (fun a : ℂ => -Real.log ‖a - u‖) (circleMeasure x r) :=
    (integrable_log_norm_sub_circleMeasure x u r).neg
  have h2 := integrable_log_normPlus_circleMeasure x r
  have h3 : Integrable (fun _ : ℂ => Real.log (normPlus u)) (circleMeasure x r) :=
    integrable_const _
  have h12 : Integrable (fun a : ℂ => -Real.log ‖a - u‖ + Real.log (normPlus a))
      (circleMeasure x r) := h1.add h2
  have hsplit : (fun a => gffKernel a u) =
      fun a => (-Real.log ‖a - u‖ + Real.log (normPlus a)) + Real.log (normPlus u) := rfl
  rw [hsplit, integral_add h12 h3, integral_add h1 h2, integral_neg,
    integral_log_norm_sub_circleMeasure x u r, integral_const, probReal_univ, one_smul]
  rfl

end DOZZ.Proofs

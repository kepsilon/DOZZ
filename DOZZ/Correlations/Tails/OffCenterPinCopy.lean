/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.OffCenterCircleLaw
public import DOZZ.Correlations.Tails.GaussianPinCopy
public import DOZZ.Correlations.Tails.PinPotential

/-! The independent pin copy for the actual translated circle field.
The correction vanishes to first order at the insertion center. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace DOZZ.Proofs

/-- The local circle/pin covariance consists of the pin variance and its smooth correction. -/
theorem offCenter_circle_pin_covariance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (z : ℂ) (hz : 2 ≤ ‖z‖) (p : localCircle) :
    covariance (fun ω => Xc ω (z + p.val.1) p.val.2) (fun ω => Xc ω z 0) P =
      Real.log ‖z + p.val.1‖ + Real.log ‖z‖ := by
  have hp := circle_pin_exterior (z + p.val.1) p.val.2
    (localCircle_exterior z hz p)
  have hzpin := circle_pin_exterior z 0
    (by simpa only [neg_zero, Real.exp_zero, one_add_one_eq_two] using hz)
  have hp0 : circleLogPotential ‖p.val.1‖₊
      ⟨Real.exp (-p.val.2), Real.exp_pos _⟩ ⟨1, by norm_num⟩ = 0 := by
    simpa only [Real.log_one] using circleLogPotential_of_add_le (d := ‖p.val.1‖₊)
      ⟨Real.exp (-p.val.2), Real.exp_pos _⟩ ⟨1, by norm_num⟩ p.property
  rw [circleAverage_covariance P X Xc hX hc]
  simp only [add_sub_cancel_left, neg_zero, Real.exp_zero] at hzpin ⊢
  rw [hp0, hp, hzpin]
  ring

/-- The unshifted local circle variance retains the exact exterior normalization. -/
theorem offCenter_circle_self_covariance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (z : ℂ) (hz : 2 ≤ ‖z‖) (p : localCircle) :
    covariance (fun ω => Xc ω (z + p.val.1) p.val.2)
      (fun ω => Xc ω (z + p.val.1) p.val.2) P =
        p.val.2 + 2 * Real.log ‖z + p.val.1‖ := by
  rw [circleAverage_covariance P X Xc hX hc]
  have hp := circle_pin_exterior (z + p.val.1) p.val.2
    (localCircle_exterior z hz p)
  simp only [sub_self, nnnorm_zero, circleLogPotential_zero, max_self, Real.log_exp,
    neg_neg, hp]
  ring

/-- Pointwise regression coefficient of the residual local field on the equator pin. -/
noncomputable def localPinCoefficient (z x : ℂ) : ℝ :=
  (Real.log ‖z + x‖ - Real.log ‖z‖) / (2 * Real.log ‖z‖)

/-- Uniform first-order bound on the regression coefficient. -/
theorem local_pin_coefficient_bound (z x : ℂ)
    (hz : 2 ≤ ‖z‖) (hx : ‖x‖ ≤ 1) :
    |localPinCoefficient z x| ≤ ‖x‖ / (2 * Real.log ‖z‖) := by
  unfold localPinCoefficient
  rw [abs_div, abs_of_pos (offCenter_pin_variance_pos z hz)]
  exact div_le_div_of_nonneg_right (offCenter_pin_potential_bound z x hz hx)
    (offCenter_pin_variance_pos z hz).le

/-- Original translated circles and their pin have the same whole law after replacing
that pin by a copy and retaining the explicit small spatial correction. -/
theorem offCenter_circle_pin_copy_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun q : Ω × (ℂ × ℝ) => Xc q.1 q.2.1 q.2.2))
    (z : ℂ) (hz : 2 ≤ ‖z‖) :
    P.map (fun ω (j : Option localCircle) => j.elim (Xc ω z 0)
      (fun p => Xc ω (z + p.val.1) p.val.2)) =
    (P.prod P).map (fun q (j : Option localCircle) => j.elim (Xc q.2 z 0)
      (fun p => Xc q.2 z 0 + (Xc q.1 (z + p.val.1) p.val.2 - Xc q.1 z 0) +
        localPinCoefficient z p.val.1 * (Xc q.2 z 0 - Xc q.1 z 0))) := by
  let k : Option localCircle → ℂ × ℝ := fun j =>
    j.elim (z, 0) (fun p => (z + p.val.1, p.val.2))
  let Z : Option localCircle → Ω → ℝ := fun j ω => Xc ω (k j).1 (k j).2
  have hZ : IsGaussianProcess Z P := (circleAverage_isGaussianProcess P X Xc hX hc).1.comp_right k
  have hZm : Measurable (fun ω j => Z j ω) := by
    apply measurable_pi_iff.mpr
    intro j
    exact hm.comp (measurable_id.prodMk measurable_const)
  have hvar : covariance (Z none) (Z none) P = 2 * Real.log ‖z‖ :=
    offCenter_origin_variance X Xc hX hc z hz
  have he := gaussian_pin_copy_law P Z hZ hZm (2 * Real.log ‖z‖)
    (offCenter_pin_variance_pos z hz).ne' hvar
  have hsource : (fun ω j => Z j ω) =
      (fun ω (j : Option localCircle) => j.elim (Xc ω z 0)
        (fun p => Xc ω (z + p.val.1) p.val.2)) := by
    funext ω j
    cases j <;> rfl
  rw [← hsource, he]
  congr 1
  funext q j
  cases j with
  | none => rfl
  | some p =>
    change Xc q.1 (z + p.val.1) p.val.2 +
      covariance (fun ω => Xc ω (z + p.val.1) p.val.2) (fun ω => Xc ω z 0) P /
        (2 * Real.log ‖z‖) * (Xc q.2 z 0 - Xc q.1 z 0) = _
    rw [offCenter_circle_pin_covariance P X Xc hX hc z hz p]
    simp only [Option.elim_some]
    unfold localPinCoefficient
    field_simp [(offCenter_pin_variance_pos z hz).ne',
      (Real.log_pos (by linarith : 1 < ‖z‖)).ne']
    ring


end DOZZ.Proofs

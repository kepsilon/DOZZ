/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.OffCenterMultiplier

/-! A bounded continuous extension of the local pin coefficient. -/

@[expose] public section
open Set

namespace DOZZ.Proofs

/-- Clip the globally continuous reference potential outside the insertion disk. -/
noncomputable def boundedPinCoefficient (z : ℂ) : BoundedContinuousFunction ℂ ℝ :=
  let v := 2 * Real.log ‖z‖
  let b := 1 / |v|
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => max (-b) (min b ((Real.log (normPlus (z+x))-Real.log ‖z‖)/v)))
    (continuous_const.max (continuous_const.min
      (((continuous_const.max (continuous_const.add continuous_id).norm).log
        (fun _ => by positivity)).sub continuous_const |>.div_const v))) b (fun x => by
      rw [Real.norm_eq_abs]
      apply abs_le.mpr
      have hb : 0 ≤ b := by dsimp [b]; positivity
      exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩)

/-- On the full closed unit disk this is exactly the local regression coefficient. -/
theorem bounded_pin_coefficient_eq (z x : ℂ) (hz : 2 ≤ ‖z‖) (hx : ‖x‖ ≤ 1) :
    boundedPinCoefficient z x = localPinCoefficient z x := by
  have hv := offCenter_pin_variance_pos z hz
  have hnorm : 1 ≤ ‖z+x‖ := by
    have h := norm_sub_norm_le z (z+x)
    simp only [sub_add_cancel_left, norm_neg] at h
    linarith
  have hc := local_pin_coefficient_bound z x hz hx
  have hcb : |localPinCoefficient z x| ≤ 1 / (2 * Real.log ‖z‖) :=
    hc.trans (div_le_div_of_nonneg_right hx hv.le)
  have hleft := (abs_le.mp hcb).1
  have hright := (abs_le.mp hcb).2
  change max (-(1 / |2 * Real.log ‖z‖|))
    (min (1 / |2 * Real.log ‖z‖|)
      ((Real.log (normPlus (z+x))-Real.log ‖z‖)/(2 * Real.log ‖z‖))) = _
  rw [abs_of_pos hv, show normPlus (z+x) = ‖z+x‖ by
    unfold normPlus; exact max_eq_right hnorm]
  change max (-(1 / (2 * Real.log ‖z‖)))
    (min (1 / (2 * Real.log ‖z‖)) (localPinCoefficient z x)) = _
  rw [min_eq_right hright, max_eq_right hleft]


end DOZZ.Proofs

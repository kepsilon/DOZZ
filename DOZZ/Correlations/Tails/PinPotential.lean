/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.OffCenterRegression

/-! The first-order bound on the smooth off-center pin potential in the one-insertion tail
estimate. -/

@[expose] public section

namespace DOZZ.Proofs

/-- Logarithm has Lipschitz constant one when both arguments are at least one. -/
theorem abs_log_sub_le {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| := by
  have bound {u v : ℝ} (hu : 1 ≤ u) (hv : 1 ≤ v) :
      Real.log u - Real.log v ≤ |u - v| := by
    have hup : 0 < u := lt_of_lt_of_le zero_lt_one hu
    have hvp : 0 < v := lt_of_lt_of_le zero_lt_one hv
    calc
      Real.log u - Real.log v = Real.log (u / v) :=
        (Real.log_div hup.ne' hvp.ne').symm
      _ ≤ u / v - 1 := Real.log_le_sub_one_of_pos (div_pos hup hvp)
      _ = (u - v) / v := by field_simp
      _ ≤ |u - v| / v := div_le_div_of_nonneg_right (le_abs_self _) hvp.le
      _ ≤ |u - v| := div_le_self (abs_nonneg _) hv
  apply abs_le.mpr
  constructor
  · have h := bound hb ha
    rw [abs_sub_comm b a] at h
    linarith
  · exact bound ha hb

/-- Uniform first-order pin correction on the unit insertion disk, including centers
at norm two. This is the quantitative covariance correction in source `boundY`. -/
theorem offCenter_pin_potential_bound (z u : ℂ)
    (hz : 2 ≤ ‖z‖) (hu : ‖u‖ ≤ 1) :
    |Real.log ‖z + u‖ - Real.log ‖z‖| ≤ ‖u‖ := by
  have hz1 : 1 ≤ ‖z‖ := by linarith
  have hsum : 1 ≤ ‖z + u‖ := by
    have h := norm_sub_norm_le z (z + u)
    simp only [sub_add_cancel_left, norm_neg] at h
    linarith
  apply (abs_log_sub_le hsum hz1).trans
  simpa only [add_sub_cancel_left] using abs_norm_sub_norm_le (z + u) z

end DOZZ.Proofs

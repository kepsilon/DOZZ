/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Lateral.Field
import Mathlib.Tactic

/-! # Separated-region lateral covariance bounds

The plane-coordinate form of [KRV, (majkah)]. The estimate is
uniform in both angular variables and applies throughout the ξ window.
-/

public section

namespace DOZZ.Proofs

/-- A logarithm near one is controlled uniformly by the relative distance. -/
theorem reflected_log_near_one_bound (x q : ℝ) (hq : 0 ≤ q) (hq₂ : q ≤ 1 / 2)
    (hlo : 1 - q ≤ x) (hhi : x ≤ 1 + q) : |Real.log x| ≤ 2 * q := by
  have hx : 0 < x := by linarith only [hlo, hq₂]
  have hu := Real.log_le_sub_one_of_pos hx
  have hl := Real.one_sub_inv_le_log_of_pos hx
  have hinv : x⁻¹ ≤ 1 + 2 * q := by
    rw [inv_eq_one_div, div_le_iff₀ hx]
    have hm : (1 + 2 * q) * (1 - q) ≤ (1 + 2 * q) * x :=
      mul_le_mul_of_nonneg_left hlo (by linarith only [hq])
    nlinarith only [hm, hq, hq₂]
  rw [abs_le]
  constructor <;> linarith only [hu, hl, hinv, hhi, hq]

/-- Two concentric regions separated by a factor of two have small lateral cross covariance. -/
theorem reflected_lateral_cross_bound (w v : ℂ) (hw : w ≠ 0) (hv : v ≠ 0)
    (hsep : ‖v‖ ≤ ‖w‖ / 2) :
    |gffKernel w v - originRadialCovariance (-Real.log ‖w‖) v| ≤
      2 * (‖v‖ / ‖w‖) := by
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hnorm : ‖v‖ < ‖w‖ := by linarith only [hsep, hwpos]
  have hwv : w ≠ v := fun h => hnorm.ne (congrArg norm h.symm)
  have hdpos : 0 < ‖w - v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hwv)
  have hq : 0 ≤ ‖v‖ / ‖w‖ := div_nonneg (norm_nonneg _) hwpos.le
  have hq₂ : ‖v‖ / ‖w‖ ≤ 1 / 2 := (div_le_iff₀ hwpos).mpr (by linarith only [hsep])
  have hupper := norm_sub_le w v
  have hlower : ‖w‖ ≤ ‖w - v‖ + ‖v‖ := by
    simpa only [sub_add_cancel] using norm_add_le (w - v) v
  have hxlo : 1 - ‖v‖ / ‖w‖ ≤ ‖w - v‖ / ‖w‖ := by
    rw [← div_self hwpos.ne', ← sub_div, div_le_div_iff_of_pos_right hwpos]
    linarith only [hlower]
  have hxhi : ‖w - v‖ / ‖w‖ ≤ 1 + ‖v‖ / ‖w‖ := by
    rw [← div_self hwpos.ne', ← add_div, div_le_div_iff_of_pos_right hwpos]
    exact hupper
  have hlog := reflected_log_near_one_bound (‖w - v‖ / ‖w‖)
    (‖v‖ / ‖w‖) hq hq₂ hxlo hxhi
  rw [origin_lateralKernel_cancellation hw hv, max_eq_left hnorm.le]
  have he : -Real.log ‖w - v‖ + Real.log ‖w‖ =
      -Real.log (‖w - v‖ / ‖w‖) := by
    rw [Real.log_div hdpos.ne' hwpos.ne']
    ring
  rw [he, abs_neg]
  exact hlog

/-- Relative-radius separation gives the cross-covariance error used by Kahane. -/
theorem reflected_lateral_cross_bound_relative (w v : ℂ) (ρ : ℝ)
    (hw : w ≠ 0) (hv : v ≠ 0) (hρ : ρ ≤ 1 / 2) (hsep : ‖v‖ ≤ ρ * ‖w‖) :
    |gffKernel w v - originRadialCovariance (-Real.log ‖w‖) v| ≤ 2 * ρ := by
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hhalf : ‖v‖ ≤ ‖w‖ / 2 := by
    calc
      ‖v‖ ≤ ρ * ‖w‖ := hsep
      _ ≤ (1 / 2) * ‖w‖ := mul_le_mul_of_nonneg_right hρ hwpos.le
      _ = ‖w‖ / 2 := by ring
  have hratio : ‖v‖ / ‖w‖ ≤ ρ := (div_le_iff₀ hwpos).mpr hsep
  exact (reflected_lateral_cross_bound w v hw hv hhalf).trans
    (mul_le_mul_of_nonneg_left hratio (by norm_num))

end DOZZ.Proofs

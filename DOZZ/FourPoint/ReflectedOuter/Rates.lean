/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.IsComplexLittleOAtZero
import Mathlib.Tactic

/-! # Punctured cutoff geometry and the two reflected outer rates -/

@[expose] public section
open Filter Topology Set
namespace DOZZ.Proofs

/-- Every cutoff exponent in `(0,1)` eventually separates the moving root from its retained
region, while making that radius arbitrarily small. -/
theorem reflected_outer_cutoff_geometry (ξ ε : ℝ) (hξ : 0 < ξ) (hξ₁ : ξ < 1) (hε : 0 < ε) :
    ∀ᶠ z : ℂ in nhdsWithin (0 : ℂ) {z | z ≠ 0},
      0 < ‖z‖ ^ (1 - ξ) ∧ ‖z‖ ^ (1 - ξ) ≤ 1 ∧ ‖z‖ ≤ 1 ∧
        ‖z‖ ≤ ‖z‖ ^ (1 - ξ) / 2 ∧ ‖z‖ ^ (1 - ξ) < ε := by
  let l := nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}
  have hn : Tendsto (fun z : ℂ => ‖z‖) l (nhds 0) := by
    simpa only [norm_zero] using (continuous_norm.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
  have hr : Tendsto (fun z : ℂ => ‖z‖ ^ (1 - ξ)) l (nhds 0) := by
    have hh := ((Real.continuous_rpow_const (by linarith only [hξ₁] : 0 ≤ 1 - ξ)).tendsto 0).comp hn
    simpa only [Function.comp_def, Real.zero_rpow (by linarith only [hξ₁] : 1 - ξ ≠ 0)] using hh
  have hs : Tendsto (fun z : ℂ => ‖z‖ ^ ξ) l (nhds 0) := by
    have hh := ((Real.continuous_rpow_const hξ.le).tendsto 0).comp hn
    simpa only [Function.comp_def, Real.zero_rpow hξ.ne'] using hh
  filter_upwards [hr.eventually (gt_mem_nhds hε), hr.eventually (gt_mem_nhds zero_lt_one),
    hn.eventually (gt_mem_nhds zero_lt_one), hs.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    self_mem_nhdsWithin] with z hzε hzr hz₁ hzsep hz0
  have hz : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have he : ‖z‖ ^ (1 - ξ) * ‖z‖ ^ ξ = ‖z‖ := by
    rw [← Real.rpow_add hz, sub_add_cancel, Real.rpow_one]
  refine ⟨Real.rpow_pos_of_pos hz _, hzr.le, hz₁.le, ?_, hzε⟩
  have hh := mul_le_mul_of_nonneg_left hzsep.le (Real.rpow_nonneg hz.le (1 - ξ))
  rw [he] at hh
  linarith only [hh]

/-- Dividing the two explicit rates by the target power leaves two strictly positive powers. -/
theorem reflected_outer_rate_littleO (κ ξ e C₁ C₂ : ℝ) (f : ℂ → ℂ)
    (hslack : κ < ξ) (hfreeze : κ < (1 - ξ) * e)
    (hb : ∀ᶠ z : ℂ in nhdsWithin (0 : ℂ) {z | z ≠ 0},
      ‖f z‖ ≤ C₁ * ‖z‖ ^ ξ + C₂ * (‖z‖ ^ (1 - ξ)) ^ e) :
    IsComplexLittleOAtZero κ f := by
  let l := nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}
  have hn : Tendsto (fun z : ℂ => ‖z‖) l (nhds 0) := by
    simpa only [norm_zero] using (continuous_norm.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
  have ht (a : ℝ) (ha : 0 < a) : Tendsto (fun z : ℂ => ‖z‖ ^ a) l (nhds 0) := by
    have hh := ((Real.continuous_rpow_const ha.le).tendsto 0).comp hn
    simpa only [Function.comp_def, Real.zero_rpow ha.ne'] using hh
  have hlimit : Tendsto (fun z : ℂ => C₁ * ‖z‖ ^ (ξ - κ) +
      C₂ * ‖z‖ ^ ((1 - ξ) * e - κ)) l (nhds 0) := by
    simpa only [mul_zero, zero_add] using
      ((ht (ξ - κ) (sub_pos.mpr hslack)).const_mul C₁).add
        ((ht ((1 - ξ) * e - κ) (sub_pos.mpr hfreeze)).const_mul C₂)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlimit
    (Filter.Eventually.of_forall (fun z => div_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)))
  filter_upwards [hb, self_mem_nhdsWithin] with z hz hz0
  have hnz : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  calc
    _ ≤ (C₁ * ‖z‖ ^ ξ + C₂ * (‖z‖ ^ (1 - ξ)) ^ e) / ‖z‖ ^ κ :=
      div_le_div_of_nonneg_right hz (Real.rpow_nonneg hnz.le _)
    _ = _ := by
      rw [add_div, mul_div_assoc, mul_div_assoc, ← Real.rpow_sub hnz,
        ← Real.rpow_mul hnz.le, ← Real.rpow_sub hnz]

end DOZZ.Proofs

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.TaylorSourceMargins

/-! A single radius for all Taylor regions and their common strict power gain. -/

@[expose] public section
open MeasureTheory Filter Topology Set
namespace DOZZ.Proofs

/-- The source's three scales are simultaneously valid below one positive radius. -/
theorem taylor_small_scales (δ ε : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 / 4 ∧ ∀ r : ℝ, 0 < r → r ≤ r₀ →
      0 < r ^ (1 - δ) ∧ r ^ (1 - δ) ≤ 1 / 4 ∧
        r ≤ r ^ (1 - δ) / 2 ∧ 0 < r ^ (1 + ε) ∧ r ^ (1 + ε) ≤ r / 2 := by
  have hlim (a : ℝ) (ha : 0 < a) : Tendsto (fun r : ℝ => r ^ a) (nhds 0) (nhds 0) := by
    simpa only [Real.zero_rpow ha.ne'] using (Real.continuous_rpow_const ha.le).continuousAt.tendsto (x := (0 : ℝ))
  have hs : ∀ᶠ r : ℝ in nhds 0,
      r ^ δ < 1 / 2 ∧ r ^ ε < 1 / 2 ∧ r ^ (1 - δ) < 1 / 4 := by
    filter_upwards [(hlim δ hδ).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      (hlim ε hε).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      (hlim (1 - δ) (sub_pos.mpr hδ1)).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))]
      with r h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨R, hR, hsmall⟩ := Metric.eventually_nhds_iff.mp hs
  let r₀ : ℝ := min (R / 2) (1 / 4)
  refine ⟨r₀, lt_min (by positivity) (by norm_num), min_le_right _ _, ?_⟩
  intro r hr hrr
  have hrR : dist r 0 < R := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hr]
    have hh : r ≤ R / 2 := hrr.trans (min_le_left _ _)
    linarith only [hh, hR]
  obtain ⟨h1, h2, h3⟩ := hsmall hrR
  have hρ : 0 < r ^ (1 - δ) := Real.rpow_pos_of_pos hr _
  have heq : r = r ^ (1 - δ) * r ^ δ := by
    rw [← Real.rpow_add hr, sub_add_cancel, Real.rpow_one]
  have heq₂ : r ^ (1 + ε) = r * r ^ ε := by rw [Real.rpow_add hr, Real.rpow_one]
  refine ⟨hρ, h3.le, ?_, Real.rpow_pos_of_pos hr _, ?_⟩
  · have hh := mul_le_mul_of_nonneg_left h1.le hρ.le
    rw [← heq] at hh
    linarith only [hh]
  · rw [heq₂]
    have hh := mul_le_mul_of_nonneg_left h2.le hr.le
    linarith only [hh]

/-- Reducing an available strict gain also leaves room for the one-root near-disk gain. -/
theorem taylor_common_gain (γ κ δ ε η d W q : ℝ)
    (hγ : 0 < γ) (hε : 0 < ε) (hη : 0 < η) (hηκ : η < 2 - κ)
    (hηd : η ≤ δ * d) (hmid : κ - 2 + η ≤ -2 - 2 * ε + (1 - δ) * W / (2 * q)) :
    ∃ η' : ℝ, 0 < η' ∧ η' < 2 - κ ∧ η' ≤ δ * d ∧
      η' ≤ ε * γ ^ 2 / 2 ∧ κ - 2 + η' ≤ -2 - 2 * ε + (1 - δ) * W / (2 * q) := by
  let η' : ℝ := min η (ε * γ ^ 2 / 4)
  have hpos : 0 < ε * γ ^ 2 / 4 := by positivity
  have hl : η' ≤ η := min_le_left _ _
  have hr : η' ≤ ε * γ ^ 2 / 4 := min_le_right _ _
  exact ⟨η', lt_min hη hpos, hl.trans_lt hηκ, hl.trans hηd,
    by nlinarith only [hr, hpos], by linarith only [hl, hmid]⟩

end DOZZ.Proofs

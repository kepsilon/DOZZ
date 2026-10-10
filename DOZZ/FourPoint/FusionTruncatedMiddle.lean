/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.FusionUniformPowers
public import DOZZ.FourPoint.FusionKernelBounds

/-! Bounded transport of the signed middle fusion exponent. -/

@[expose] public section

namespace DOZZ.Proofs

/-- Truncating the middle and outer distances changes the middle ratio by a factor in `[1,k]`. -/
theorem fusion_middle_truncated_ratio (x t u k : ℝ)
    (hx : 0 < x) (ht : 0 < t) (hxu : x ≤ u) (htu : t ≤ u) (huk : u ≤ k * t) :
    x / u ≤ min x t / t ∧ min x t / t ≤ k * (x / u) := by
  have hu : 0 < u := hx.trans_le hxu
  constructor
  · rcases le_total x t with hxt | htx
    · rw [min_eq_left hxt]
      exact div_le_div_of_nonneg_left hx.le ht htu
    · rw [min_eq_right htx, div_self ht.ne']
      exact (div_le_one₀ hu).mpr hxu
  · have hvx : min x t ≤ x := min_le_left _ _
    have hcomp : x / t ≤ k * (x / u) := by
      apply (div_le_iff₀ ht).mpr
      have hh := mul_le_mul_of_nonneg_left huk (div_pos hx hu).le
      convert hh using 1 <;> field_simp
    exact (div_le_div_of_nonneg_right hvx ht.le).trans hcomp

/-- The signed middle power transports uniformly, without assuming it is nonnegative. -/
theorem fusion_middle_truncated_power (x t u k e E : ℝ)
    (hx : 0 < x) (ht : 0 < t) (hxu : x ≤ u) (htu : t ≤ u) (huk : u ≤ k * t)
    (hk : 1 ≤ k) (hel : -E ≤ e) (heu : e ≤ E) :
    (min x t / t) ^ e ≤ k ^ E * (x / u) ^ e := by
  have hu : 0 < u := hx.trans_le hxu
  obtain ⟨hl, hh⟩ := fusion_middle_truncated_ratio x t u k hx ht hxu htu huk
  have hlow : (x / u) / k ≤ min x t / t := (div_le_self (div_pos hx hu).le hk).trans hl
  exact rpow_distance_comparison _ _ k e E (div_pos hx hu) hk hlow hh hel heu

end DOZZ.Proofs

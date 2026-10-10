/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.DualFusionRadialIntegral
public import DOZZ.Hypergeom.Planar.AngularMean

/-! The annular primitive (erratum K23, see docs/ERRATA-AND-DEVIATIONS.md) and its three distinct
asymptotic regimes. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- The literal closed-annulus integral agrees with the power primitive. -/
theorem radial_integral_eq_power (β r ξ : ℝ) (hβ : β ≠ 3)
    (hr : 0 < r) (hcut : r ^ (1 - ξ) < 1 / 2) :
    dualFusionRadialIntegral β r ξ =
      ((1 / 2 : ℝ) ^ (3 - β) - (r ^ (1 - ξ)) ^ (3 - β)) / (3 - β) := by
  have ha : 0 < r ^ (1 - ξ) := Real.rpow_pos_of_pos hr _
  unfold dualFusionRadialIntegral
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hcut.le]
  have hp : 2 - β ≠ -1 := by intro h; apply hβ; linarith only [h]
  have hnot : (0 : ℝ) ∉ Set.uIcc (r ^ (1 - ξ)) (1 / 2) :=
    notMem_uIcc_of_lt ha (by norm_num)
  have he : (2 : ℝ) - β + 1 = 3 - β := by ring
  simpa only [he] using integral_rpow (Or.inr ⟨hp, hnot⟩)

/-- At the transition exponent the primitive is logarithmic. -/
theorem radial_integral_eq_log (r ξ : ℝ)
    (hr : 0 < r) (hcut : r ^ (1 - ξ) < 1 / 2) :
    dualFusionRadialIntegral 3 r ξ = Real.log (1 / 2) - (1 - ξ) * Real.log r := by
  have ha : 0 < r ^ (1 - ξ) := Real.rpow_pos_of_pos hr _
  unfold dualFusionRadialIntegral
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hcut.le]
  simp only [show (2 : ℝ) - 3 = -1 by norm_num, Real.rpow_neg_one]
  rw [integral_inv_of_pos ha (by norm_num),
    Real.log_div (by norm_num) ha.ne', Real.log_rpow hr]

/-- The exact constant, logarithmic, and power cases for the dual annular primitive (erratum K23,
see docs/ERRATA-AND-DEVIATIONS.md). -/
theorem dual_fusion_radial_three_case (β ξ : ℝ)
    (hξ : 0 < ξ) (hξ₂ : ξ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → r < 1 / 2 → r ^ (1 - ξ) < 1 / 2 →
      (β < 3 →
        dualFusionRadialIntegral β r ξ ≤ C) ∧
      (β = 3 →
        dualFusionRadialIntegral β r ξ ≤ C * (1 + |Real.log r|)) ∧
      (3 < β →
        dualFusionRadialIntegral β r ξ ≤
          C * r ^ ((1 - ξ) * (3 - β))) := by
  by_cases hβ : β < 3
  · let C : ℝ := (1 / 2 : ℝ) ^ (3 - β) / (3 - β) + 1
    have he : 0 < 3 - β := sub_pos.mpr hβ
    have hC : 0 < C := by dsimp [C]; positivity
    refine ⟨C, hC, ?_⟩
    intro r hr _ hcut
    refine ⟨?_, ?_, ?_⟩
    · intro _
      rw [radial_integral_eq_power β r ξ hβ.ne hr hcut]
      have ha : 0 ≤ (r ^ (1 - ξ)) ^ (3 - β) :=
        (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hr _) _).le
      have hb : ((1 / 2 : ℝ) ^ (3 - β) - (r ^ (1 - ξ)) ^ (3 - β)) / (3 - β) ≤
          (1 / 2 : ℝ) ^ (3 - β) / (3 - β) :=
        div_le_div_of_nonneg_right (sub_le_self _ ha) he.le
      exact hb.trans (by dsimp [C]; linarith)
    · intro h; exact False.elim (hβ.ne h)
    · intro h; exact False.elim (not_lt_of_ge hβ.le h)
  · by_cases hβeq : β = 3
    · subst β
      refine ⟨1, by norm_num, ?_⟩
      intro r hr hrhalf hcut
      refine ⟨fun h => False.elim (lt_irrefl _ h), ?_,
        fun h => False.elim (lt_irrefl _ h)⟩
      intro _
      rw [radial_integral_eq_log r ξ hr hcut, one_mul]
      have hlogr : Real.log r < 0 := Real.log_neg hr (lt_trans hrhalf (by norm_num))
      have hloghalf : Real.log (1 / 2 : ℝ) ≤ 0 :=
        (Real.log_neg (by norm_num) (by norm_num)).le
      rw [abs_of_neg hlogr]
      nlinarith only [hlogr, hloghalf, hξ, hξ₂]
    · have hβgt : 3 < β := lt_of_le_of_ne (le_of_not_gt hβ) (Ne.symm hβeq)
      let C : ℝ := 1 / (β - 3)
      have hd : 0 < β - 3 := sub_pos.mpr hβgt
      refine ⟨C, by dsimp [C]; positivity, ?_⟩
      intro r hr _ hcut
      refine ⟨fun h => False.elim (not_lt_of_ge hβgt.le h),
        fun h => False.elim (hβeq h), ?_⟩
      intro _
      rw [radial_integral_eq_power β r ξ hβeq hr hcut]
      have hform :
          ((1 / 2 : ℝ) ^ (3 - β) - (r ^ (1 - ξ)) ^ (3 - β)) / (3 - β) =
            ((r ^ (1 - ξ)) ^ (3 - β) - (1 / 2 : ℝ) ^ (3 - β)) / (β - 3) := by
        field_simp
        ring
      rw [hform]
      have hb : 0 ≤ (1 / 2 : ℝ) ^ (3 - β) := (Real.rpow_pos_of_pos (by norm_num) _).le
      calc
        ((r ^ (1 - ξ)) ^ (3 - β) - (1 / 2 : ℝ) ^ (3 - β)) / (β - 3)
            ≤ (r ^ (1 - ξ)) ^ (3 - β) / (β - 3) :=
          div_le_div_of_nonneg_right (sub_le_self _ hb) hd.le
        _ = C * r ^ ((1 - ξ) * (3 - β)) := by
          rw [← Real.rpow_mul hr.le]
          dsimp [C]
          ring

end DOZZ.Proofs

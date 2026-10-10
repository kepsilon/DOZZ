/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.DeletedDisk
public import DOZZ.FourPoint.Dual.RootedIdentity
public import DOZZ.FourPoint.Reflected.Remainder
import Mathlib.Tactic
/-! # The actual rooted deleted-disk expectation -/
public section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- Rooting and spatial integration give the deleted-disk power for the actual
retained inverse mass, uniformly in the insertion and retained radius. -/
theorem dual_deleted_disk_rooted_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ q : ℝ) (hq : 0 ≤ q) (hβ : γ * α₁ < 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ) (ξ r : ℝ), ‖z‖ ≤ 1 → ‖z‖ ^ (1 - ξ) ≤ 1 →
      0 < r → r ≤ 1 / 2 →
      (∫⁻ ω, (∫⁻ x in Metric.ball (0 : ℂ) r,
        ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ 0 x) ∂M ω) *
          dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^ (-q) ∂P) ≤
            ENNReal.ofReal (C * r ^ (4 - γ * α₁)) := by
  obtain ⟨C₁, hC₁, hb⟩ := dual_outerMass_rooted_weight_bound
    P X hX γ hγ hγ₂ M hM α₁ α₂ α₃ q hq
  obtain ⟨C₂, hC₂, hs⟩ := dual_deleted_disk_spatial_bound γ α₁ α₂ α₃ hβ
  refine ⟨C₁ * C₂, mul_pos hC₁ hC₂, ?_⟩
  intro z ξ r hz hcut hr hr₁
  let D := Metric.ball (0 : ℂ) r
  let f := D.indicator (dualFusionKernel γ α₁ α₂ α₃ 0)
  have hf : Measurable f := (dual_kernel_measurable γ α₁ α₂ α₃ 0).indicator measurableSet_ball
  have he : (fun x => ENNReal.ofReal (f x)) =
      D.indicator (fun x => ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ 0 x)) := by
    funext x
    by_cases hx : x ∈ D <;> simp [f, hx]
  have ht := hb z ξ hz hcut f hf
  simp_rw [show ∀ x, ENNReal.ofReal (f x) = D.indicator
    (fun x => ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ 0 x)) x from fun x => congrFun he x] at ht
  rw [lintegral_indicator measurableSet_ball] at ht
  have heω (ω : Ω) : (∫⁻ u, D.indicator
      (fun x => ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ 0 x)) u *
        dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^ (-q) ∂M ω) =
      (∫⁻ x in D, ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ 0 x) ∂M ω) *
        dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^ (-q) := by
    have hfi : Measurable (D.indicator
        (fun x => ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ 0 x))) :=
      (ENNReal.measurable_ofReal.comp (dual_kernel_measurable γ α₁ α₂ α₃ 0)).indicator measurableSet_ball
    rw [lintegral_mul_const _ hfi, lintegral_indicator measurableSet_ball]
  simp_rw [heω] at ht
  exact ht.trans ((mul_le_mul' le_rfl (hs r hr hr₁)).trans_eq (by
    rw [← ENNReal.ofReal_mul hC₁.le]
    congr 1
    ring))

/-- The actual rooted deleted-disk term is negligible at the dual fusion power. -/
theorem dual_deleted_disk_rooted_littleO {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ q ξ κ : ℝ) (hq : 0 ≤ q) (hβ : γ * α₁ < 4) (hξ₁ : ξ < 1)
    (hslack : κ < (1 - ξ) * (4 - γ * α₁)) :
    Tendsto (fun z : ℂ =>
      (∫⁻ ω, (∫⁻ x in Metric.ball (0 : ℂ) (‖z‖ ^ (1 - ξ)),
        ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ 0 x) ∂M ω) *
          dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^ (-q) ∂P).toReal / ‖z‖ ^ κ)
      (nhdsWithin 0 {z : ℂ | z ≠ 0}) (nhds 0) := by
  let F : ℂ → ℝ := fun z =>
    (∫⁻ ω, (∫⁻ x in Metric.ball (0 : ℂ) (‖z‖ ^ (1 - ξ)),
      ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ 0 x) ∂M ω) *
        dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^ (-q) ∂P).toReal
  obtain ⟨C, hC, hb⟩ := dual_deleted_disk_rooted_bound P X hX γ hγ hγ₂ M hM
    α₁ α₂ α₃ q hq hβ
  have hn : Tendsto (fun z : ℂ => ‖z‖)
      (nhdsWithin 0 {z : ℂ | z ≠ 0}) (nhds 0) := by
    simpa only [norm_zero] using (continuous_norm.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
  have hc : Tendsto (fun z : ℂ => ‖z‖ ^ (1 - ξ))
      (nhdsWithin 0 {z : ℂ | z ≠ 0}) (nhds 0) := by
    have he := sub_pos.mpr hξ₁
    simpa only [Function.comp_def, Real.zero_rpow he.ne'] using
      ((Real.continuous_rpow_const he.le).tendsto (0 : ℝ)).comp hn
  have hh : ∀ᶠ z : ℂ in nhdsWithin 0 {z : ℂ | z ≠ 0},
      ‖(F z : ℂ)‖ ≤ C * ‖z‖ ^ ((1 - ξ) * (4 - γ * α₁)) := by
    filter_upwards [hn.eventually (gt_mem_nhds zero_lt_one),
      hc.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      self_mem_nhdsWithin] with z hz hzcut hz0
    have hbz := hb z ξ (‖z‖ ^ (1 - ξ)) hz.le (by linarith only [hzcut])
      (Real.rpow_pos_of_pos (norm_pos_iff.mpr hz0) _) hzcut.le
    rw [← Real.rpow_mul (norm_nonneg z)] at hbz
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbz).trans_eq
      (ENNReal.toReal_ofReal (mul_nonneg hC.le (Real.rpow_nonneg (norm_nonneg z) _)))
  exact (isComplexLittleOAtZero_ofReal_iff κ F).mp
    (isComplexLittleOAtZero_of_norm_le_power hslack hh)

end DOZZ.Proofs

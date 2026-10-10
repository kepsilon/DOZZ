/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.MovingMoment
public import DOZZ.FourPoint.Dual.DeletedMoment
public import DOZZ.FourPoint.Reflected.Remainder
import Mathlib.Tactic
/-! # The actual dual outer inverse-moment correction is negligible -/
public section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- The actual retained inverse expectation differs from the full zero inverse expectation
by o(|z|^κ) under the two strict dual outer margins. -/
theorem dual_outer_inverse_moment_littleO {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ p ξ κ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hp : 0 < p)
    (hα₁ : α₁ - 2 / γ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hβ : γ * α₁ < 4) (hξ : 0 < ξ) (hξ₁ : ξ < 1) (hκξ : κ < ξ)
    (hslack : κ < (1 - ξ) * (4 - γ * α₁))
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    Tendsto (fun z : ℂ =>
      (dualOuterMoment P M γ α₁ α₂ α₃ p z ξ -
        (∫⁻ ω, coulombMass γ (M ω) ![-2 / γ, α₁, α₂] ![0, 0, 1] α₃ ^ (-p) ∂P).toReal) /
          ‖z‖ ^ κ) (nhdsWithin 0 {z : ℂ | z ≠ 0}) (nhds 0) := by
  obtain ⟨C₁, _, hmove⟩ := dual_outer_moving_moment_bound
    P X M γ α₁ α₂ α₃ p hγ hγ₂ hp hα₁ hα₂ hα₃ hX hM
  obtain ⟨C₂, _, hdel⟩ := dual_retainedZero_deleted_moment_bound
    P X M γ α₁ α₂ α₃ p hγ hγ₂ hp hα₁ hα₂ hα₃ hβ hX hM
  let l := nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}
  have hn : Tendsto (fun z : ℂ => ‖z‖) l (nhds 0) := by
    simpa only [norm_zero] using (continuous_norm.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
  have hpow (s : ℝ) (hs : 0 < s) : Tendsto (fun z : ℂ => ‖z‖ ^ s) l (nhds 0) := by
    simpa only [Function.comp_def, Real.zero_rpow hs.ne'] using
      ((Real.continuous_rpow_const hs.le).tendsto (0 : ℝ)).comp hn
  have hbound : ∀ᶠ z : ℂ in l,
      |dualOuterMoment P M γ α₁ α₂ α₃ p z ξ -
        (∫⁻ ω, coulombMass γ (M ω) ![-2 / γ, α₁, α₂] ![0, 0, 1] α₃ ^ (-p) ∂P).toReal| ≤
          C₁ * ‖z‖ ^ ξ + C₂ * ‖z‖ ^ ((1 - ξ) * (4 - γ * α₁)) := by
    filter_upwards [hn.eventually (gt_mem_nhds zero_lt_one),
      (hpow (1 - ξ) (sub_pos.mpr hξ₁)).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      (hpow ξ hξ).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      self_mem_nhdsWithin] with z hz hcut hsmall hz0
    have hpz : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hr : 0 < ‖z‖ ^ (1 - ξ) := Real.rpow_pos_of_pos hpz _
    have he : ‖z‖ = ‖z‖ ^ (1 - ξ) * ‖z‖ ^ ξ := by
      rw [← Real.rpow_add hpz, sub_add_cancel, Real.rpow_one]
    have hsep : ‖z‖ ≤ ‖z‖ ^ (1 - ξ) / 2 := by
      calc
        _ = _ := he
        _ ≤ ‖z‖ ^ (1 - ξ) * (1 / 2) := mul_le_mul_of_nonneg_left hsmall.le hr.le
        _ = _ := by ring
    have h₁ := hmove z ξ hr (by linarith only [hcut]) hz.le hsep
    have h₂ := hdel (‖z‖ ^ (1 - ξ)) hr hcut.le
    have hratio : ‖z‖ / ‖z‖ ^ (1 - ξ) = ‖z‖ ^ ξ := by
      calc
        _ = (‖z‖ ^ (1 - ξ) * ‖z‖ ^ ξ) / ‖z‖ ^ (1 - ξ) :=
          congrArg (fun y => y / ‖z‖ ^ (1 - ξ)) he
        _ = _ := mul_div_cancel_left₀ _ hr.ne'
    rw [hratio] at h₁
    rw [← Real.rpow_mul hpz.le] at h₂
    exact (abs_sub_le _ _ _).trans (add_le_add h₁ h₂)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hu := ((reflected_radius_power_ratio_tendsto κ ξ hκξ).const_mul C₁).add
    ((reflected_radius_power_ratio_tendsto κ ((1 - ξ) * (4 - γ * α₁)) hslack).const_mul C₂)
  apply squeeze_zero' (Eventually.of_forall fun z => norm_nonneg _) ?_
    (show Tendsto (fun z : ℂ => C₁ * (‖z‖ ^ ξ / ‖z‖ ^ κ) +
      C₂ * (‖z‖ ^ ((1 - ξ) * (4 - γ * α₁)) / ‖z‖ ^ κ)) l (nhds 0) by
      simpa only [mul_zero, add_zero] using hu)
  filter_upwards [hbound] with z hz
  rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]
  exact (div_le_div_of_nonneg_right hz (Real.rpow_nonneg (norm_nonneg z) _)).trans_eq (by ring)

end DOZZ.Proofs

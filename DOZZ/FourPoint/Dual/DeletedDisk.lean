/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.Kernel
public import DOZZ.FourPoint.TaylorRadialBall
import DOZZ.GMC.SharpMoments.SeibergWeight
import Mathlib.Tactic
/-! # The deterministic deleted-disk estimate for the dual outer correction -/
public section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- The zero dual kernel near its first root is bounded by the integrable local radial power. -/
theorem dual_zero_kernel_local_bound (γ α₁ α₂ α₃ : ℝ) (x : ℂ) (hx : ‖x‖ < 1 / 2) :
    dualFusionKernel γ α₁ α₂ α₃ 0 x ≤ (2 : ℝ) ^ |γ * α₂| * ‖x‖ ^ (2 - γ * α₁) := by
  by_cases hx0 : x = 0
  · subst x
    simp [dualFusionKernel]
    positivity
  have hp : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hdlo : (1 / 2 : ℝ) ≤ ‖x - 1‖ := by
    have h := norm_sub_norm_le (1 : ℂ) x
    rw [norm_one, norm_sub_rev] at h
    linarith
  have hdhi : ‖x - 1‖ ≤ 2 := by
    have h := norm_sub_le x (1 : ℂ)
    rw [norm_one] at h
    linarith
  have hu := coulombWeight_rpow_le (by norm_num : (1 : ℝ) ≤ 2)
    (by simpa only [one_div] using hdlo) hdhi (-(γ * α₂))
  simp only [abs_neg] at hu
  have he : dualFusionKernel γ α₁ α₂ α₃ 0 x =
      ‖x‖ ^ (2 - γ * α₁) * ‖x - 1‖ ^ (-(γ * α₂)) := by
    unfold dualFusionKernel normPlus
    rw [sub_zero, max_eq_left (by linarith : ‖x‖ ≤ 1), Real.one_rpow, mul_one,
      Real.rpow_sub hp, Real.rpow_two, Real.rpow_neg (norm_nonneg (x - 1))]
    ring
  rw [he]
  exact (mul_le_mul_of_nonneg_left hu (Real.rpow_nonneg hp.le _)).trans_eq (mul_comm _ _)

/-- Deleting a small disk has order r^(4−γα₁), with no missing logarithmic endpoint. -/
theorem dual_deleted_disk_spatial_bound (γ α₁ α₂ α₃ : ℝ) (hβ : γ * α₁ < 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 / 2 →
      (∫⁻ x in Metric.ball (0 : ℂ) r,
        ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ 0 x) ∂gmcReferenceMeasure) ≤
          ENNReal.ofReal (C * r ^ (4 - γ * α₁)) := by
  obtain ⟨C₀, hC₀, hb⟩ := planar_radial_ball_bound (2 - γ * α₁)
    (by linarith only [hβ])
  refine ⟨(2 : ℝ) ^ |γ * α₂| * C₀, mul_pos (by positivity) hC₀, ?_⟩
  intro r hr hr₁
  have hd : Measurable (fun x : ℂ => ENNReal.ofReal (normPlus x ^ (-4 : ℝ))) := by
    unfold normPlus
    fun_prop
  have hk : Measurable (fun x => ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ 0 x)) :=
    ENNReal.measurable_ofReal.comp (dual_kernel_measurable γ α₁ α₂ α₃ 0)
  rw [gmcReferenceMeasure, restrict_withDensity measurableSet_ball,
    lintegral_withDensity_eq_lintegral_mul _ hd hk]
  calc
    _ ≤ ∫⁻ x in Metric.ball (0 : ℂ) r,
        ENNReal.ofReal ((2 : ℝ) ^ |γ * α₂|) * ENNReal.ofReal (‖x‖ ^ (2 - γ * α₁)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      have hn : ‖x‖ < 1 / 2 := (by simpa only [Metric.mem_ball, dist_zero_right] using hx : ‖x‖ < r).trans_le hr₁
      have hplus : normPlus x = 1 := max_eq_left (by linarith : ‖x‖ ≤ 1)
      simp only [Pi.mul_apply, hplus, Real.one_rpow, ENNReal.ofReal_one, one_mul]
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (dual_zero_kernel_local_bound γ α₁ α₂ α₃ x hn)
    _ = ENNReal.ofReal ((2 : ℝ) ^ |γ * α₂|) *
        ∫⁻ x in Metric.ball (0 : ℂ) r, ENNReal.ofReal (‖x‖ ^ (2 - γ * α₁)) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ |γ * α₂|) * ENNReal.ofReal (C₀ * r ^ ((2 - γ * α₁) + 2)) :=
      mul_le_mul' le_rfl (by simpa only [sub_zero] using hb 0 r hr)
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [show (2 - γ * α₁) + 2 = 4 - γ * α₁ by ring]
      ring

end DOZZ.Proofs

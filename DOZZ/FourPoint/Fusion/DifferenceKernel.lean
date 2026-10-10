/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.ScaledLocalKernel
public import DOZZ.FourPoint.Fusion.RootedKernelBound
public import DOZZ.Hypergeom.Planar.DifferenceIntegral
/-! # The literal signed KRV mass difference kernel -/
@[expose] public section
open MeasureTheory Set
namespace DOZZ.Proofs
noncomputable def fusionDifferenceKernel (γ α₁ α₂ α₃ : ℝ) (z x : ℂ) : ℝ :=
  gammaHalfKernel γ α₁ α₂ α₃ z x - gammaHalfKernel γ α₁ α₂ α₃ 0 x
/-- The difference kernel is jointly measurable. -/
theorem fusionDifferenceKernel_measurable (γ α₁ α₂ α₃ : ℝ) :
    Measurable (fun q : ℂ × ℂ => fusionDifferenceKernel γ α₁ α₂ α₃ q.1 q.2) :=
  (fusion_measurable_gammaHalfKernel γ α₁ α₂ α₃).sub
    ((fusion_measurable_gammaHalfKernel γ α₁ α₂ α₃).comp (measurable_const.prodMk measurable_snd))
/-- In the local chart the difference has exactly the first-subtracted planar kernel. -/
theorem fusion_difference_kernel_local (γ α₁ α₂ α₃ : ℝ) (z x : ℂ)
    (hx : ‖x‖ < 1 / 2) :
    fusionDifferenceKernel γ α₁ α₂ α₃ z x =
      planarDifferenceKernel (γ ^ 2 / 2) (γ * α₁) z x * ‖x - 1‖ ^ (-γ * α₂) := by
  have hn : normPlus x = 1 := max_eq_left (by linarith)
  have h1 : 0 < ‖x - 1‖ := by
    have h := norm_sub_norm_le (1 : ℂ) x
    rw [norm_one, norm_sub_rev] at h
    linarith
  unfold fusionDifferenceKernel gammaHalfKernel planarDifferenceKernel
  rw [hn, Real.one_rpow, mul_one, mul_one, sub_zero, neg_mul γ α₂, Real.rpow_neg h1.le]
  ring
/-- Local scaling of the signed difference preserves its sign. -/
theorem fusion_difference_kernel_scaled (γ α₁ α₂ α₃ : ℝ) (y z : ℂ)
    (hz : z ≠ 0) (hlocal : ‖y * z‖ < 1 / 2) :
    fusionDifferenceKernel γ α₁ α₂ α₃ z (y * z) =
      ‖z‖ ^ (γ ^ 2 / 2 - γ * α₁) *
        planarDifferenceKernel (γ ^ 2 / 2) (γ * α₁) 1 y * ‖y * z - 1‖ ^ (-γ * α₂) := by
  rw [fusion_difference_kernel_local γ α₁ α₂ α₃ z (y * z) hlocal]
  have he : planarDifferenceKernel (γ ^ 2 / 2) (γ * α₁) z (y * z) =
      ‖z‖ ^ (γ ^ 2 / 2 - γ * α₁) * planarDifferenceKernel (γ ^ 2 / 2) (γ * α₁) 1 y := by
    unfold planarDifferenceKernel
    rw [show y * z - z = (y - 1) * z by ring, norm_mul, norm_mul,
      Real.mul_rpow (norm_nonneg _) (norm_nonneg _),
      Real.mul_rpow (norm_nonneg _) (norm_nonneg _),
      Real.mul_rpow (norm_nonneg _) (norm_nonneg _), Real.rpow_sub (norm_pos_iff.mpr hz)]
    ring
  rw [he, mul_assoc]
/-- The local signed difference is absolutely integrable against the reference measure. -/
theorem fusion_difference_local_integrable (γ α₁ α₂ α₃ : ℝ)
    (hk : 0 < γ ^ 2 / 2) (hβ : γ ^ 2 / 2 + 1 < γ * α₁) (hβ2 : γ * α₁ < 2)
    (z : ℂ) (_hz : z ≠ 0) :
    Integrable ((Metric.ball (0 : ℂ) (1 / 2)).indicator
      (fusionDifferenceKernel γ α₁ α₂ α₃ z)) gmcReferenceMeasure := by
  let B := Metric.ball (0 : ℂ) (1 / 2)
  have hf : Measurable (fusionDifferenceKernel γ α₁ α₂ α₃ z) := by
    have hp : Measurable (fun x : ℂ => (z, x)) := measurable_const.prodMk measurable_id
    simpa only [Function.comp_def] using (fusionDifferenceKernel_measurable γ α₁ α₂ α₃).comp hp
  have hK := (planar_difference_integral (γ ^ 2 / 2) (γ * α₁) hk hβ hβ2 z).1
  have hdom := hK.norm.const_mul ((2 : ℝ) ^ |γ * α₂|)
  have hv : Integrable (B.indicator (fusionDifferenceKernel γ α₁ α₂ α₃ z)) volume := by
    apply hdom.mono' (hf.indicator Metric.isOpen_ball.measurableSet).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      by_cases hx : x ∈ B
      · rw [Set.indicator_of_mem hx, fusion_difference_kernel_local γ α₁ α₂ α₃ z x
          (by simpa only [B, Metric.mem_ball, dist_zero_right] using hx), norm_mul,
          Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
        have h := fusion_oneRoot_factor_bound x (by
          have hx' : ‖x‖ < 1 / 2 := by simpa only [B, Metric.mem_ball, dist_zero_right] using hx
          exact hx'.le) (γ * α₂)
        rw [← Real.rpow_neg (norm_nonneg _), ← neg_mul] at h
        exact (mul_le_mul_of_nonneg_left h (norm_nonneg _)).trans_eq (mul_comm _ _)
      · rw [Set.indicator_of_notMem hx, norm_zero]
        positivity
  apply (integrable_indicator_iff Metric.isOpen_ball.measurableSet).mpr
  change Integrable _ (gmcReferenceMeasure.restrict B)
  rw [gmcReferenceMeasure_restrict_unit_chart B Metric.isOpen_ball.measurableSet
    (fun x hx => by
      have hx' : ‖x‖ < 1 / 2 := by simpa only [B, Metric.mem_ball, dist_zero_right] using hx
      linarith)]
  exact (integrable_indicator_iff Metric.isOpen_ball.measurableSet).mp hv
end DOZZ.Proofs

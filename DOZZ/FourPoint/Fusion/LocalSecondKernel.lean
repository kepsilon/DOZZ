/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.Kernel
public import DOZZ.Hypergeom.Planar.WirtingerIntegral
public import DOZZ.GMC.Annulus.ReferenceIntensity

/-! # Absolute integrability of the local second derivative kernel -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The absolute pure derivative kernel is the mixed kernel. -/
theorem fusion_secondKernel_norm (γ α₁ α₂ α₃ : ℝ) (z x : ℂ) :
    ‖(gammaHalfKernel γ α₁ α₂ α₃ z x : ℂ) / (x - z) ^ 2‖ =
      gammaHalfKernel γ α₁ α₂ α₃ z x / ‖x - z‖ ^ 2 := by
  have hk : 0 ≤ gammaHalfKernel γ α₁ α₂ α₃ z x := by
    unfold gammaHalfKernel
    exact div_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      (Real.rpow_nonneg (by unfold normPlus; positivity) _))
      (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _))
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hk, norm_pow]

/-- On the half-unit chart the insertion at one is a bounded factor. -/
theorem fusion_localSecondKernel_bound (γ α₁ α₂ α₃ : ℝ) (z x : ℂ)
    (hx : ‖x‖ < 1 / 2) (hx0 : x ≠ 0) (hxz : x ≠ z) :
    gammaHalfKernel γ α₁ α₂ α₃ z x / ‖x - z‖ ^ 2 ≤
      (2 : ℝ) ^ |γ * α₂| * planarMixedKernel (γ ^ 2 / 2) (γ * α₁) z x := by
  have hn : normPlus x = 1 := max_eq_left (by linarith)
  have h0 : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hd : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxz)
  have hlo : (1 / 2 : ℝ) ≤ ‖x - 1‖ := by
    have h := norm_sub_norm_le (1 : ℂ) x
    rw [norm_one, norm_sub_rev] at h
    linarith
  have hhi : ‖x - 1‖ ≤ (2 : ℝ) := by
    have h := norm_sub_le x (1 : ℂ)
    rw [norm_one] at h
    linarith
  have h1 : 0 < ‖x - 1‖ := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hlo
  have ht : ‖x - 1‖ ^ (-γ * α₂) ≤ (2 : ℝ) ^ |γ * α₂| := by
    simpa only [neg_mul, abs_neg] using coulombWeight_rpow_le (L := 2) (y := ‖x - 1‖)
      (by norm_num) (by norm_num; exact hlo) hhi (-γ * α₂)
  have he : gammaHalfKernel γ α₁ α₂ α₃ z x / ‖x - z‖ ^ 2 =
      planarMixedKernel (γ ^ 2 / 2) (γ * α₁) z x * ‖x - 1‖ ^ (-γ * α₂) := by
    unfold gammaHalfKernel planarMixedKernel
    rw [hn, Real.one_rpow, mul_one, Real.rpow_sub hd, Real.rpow_two,
      neg_mul γ α₂, Real.rpow_neg h1.le]
    ring
  rw [he, mul_comm ((2 : ℝ) ^ |γ * α₂|)]
  exact mul_le_mul_of_nonneg_left ht (by unfold planarMixedKernel; positivity)

/-- The cutoff pure derivative kernel is absolutely integrable against the reference measure. -/
theorem fusion_localSecondKernel_integrable (γ α₁ α₂ α₃ : ℝ)
    (hk : 0 < γ ^ 2 / 2) (hβ : γ ^ 2 / 2 < γ * α₁) (hβ2 : γ * α₁ < 2)
    (z : ℂ) (hz : z ≠ 0) :
    Integrable ((Metric.ball (0 : ℂ) (1 / 2)).indicator
      (fun x : ℂ => (gammaHalfKernel γ α₁ α₂ α₃ z x : ℂ) / (x - z) ^ 2)) gmcReferenceMeasure := by
  let B := Metric.ball (0 : ℂ) (1 / 2)
  let f := fun x : ℂ => (gammaHalfKernel γ α₁ α₂ α₃ z x : ℂ) / (x - z) ^ 2
  have hf : Measurable f := (Complex.measurable_ofReal.comp
    ((fusion_measurable_gammaHalfKernel γ α₁ α₂ α₃).comp
      (measurable_const.prodMk measurable_id))).div ((measurable_id.sub_const z).pow_const 2)
  have hmix := (planar_mixed_integral (γ ^ 2 / 2) (γ * α₁) hk hβ hβ2 z hz).1
  have hdom : Integrable (fun x => (2 : ℝ) ^ |γ * α₂| *
      planarMixedKernel (γ ^ 2 / 2) (γ * α₁) z x) volume := hmix.const_mul _
  have hfvol : Integrable (B.indicator f) volume := by
    apply hdom.mono' (hf.indicator Metric.isOpen_ball.measurableSet).aestronglyMeasurable
    filter_upwards [Measure.ae_ne volume (0 : ℂ), Measure.ae_ne volume z] with x hx0 hxz
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, fusion_secondKernel_norm]
      exact fusion_localSecondKernel_bound γ α₁ α₂ α₃ z x
        (by simpa only [B, Metric.mem_ball, dist_zero_right] using hx) hx0 hxz
    · rw [Set.indicator_of_notMem hx, norm_zero]
      unfold planarMixedKernel
      positivity
  apply (integrable_indicator_iff Metric.isOpen_ball.measurableSet).mpr
  change Integrable f (gmcReferenceMeasure.restrict B)
  rw [gmcReferenceMeasure_restrict_unit_chart B Metric.isOpen_ball.measurableSet
    (fun x hx => by
      have h : ‖x‖ < 1 / 2 := by simpa only [B, Metric.mem_ball, dist_zero_right] using hx
      linarith)]
  exact (integrable_indicator_iff Metric.isOpen_ball.measurableSet).mp hfvol

end DOZZ.Proofs

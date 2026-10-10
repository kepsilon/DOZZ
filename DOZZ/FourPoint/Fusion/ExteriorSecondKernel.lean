/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.LocalSecondKernel

/-! # The exterior second derivative kernel has a bounded denominator -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Outside the half-unit disk, the denominator costs at most sixteen. -/
theorem fusion_exteriorSecondKernel_bound (γ α₁ α₂ α₃ : ℝ) (z x : ℂ)
    (hz : ‖z‖ ≤ 1 / 4) (hx : 1 / 2 ≤ ‖x‖) :
    ‖(gammaHalfKernel γ α₁ α₂ α₃ z x : ℂ) / (x - z) ^ 2‖ ≤
      16 * gammaHalfKernel γ α₁ α₂ α₃ z x := by
  have hl : (1 / 4 : ℝ) ≤ ‖x - z‖ := by
    have h := norm_sub_norm_le x z
    linarith
  have hd : 0 < ‖x - z‖ ^ 2 := pow_pos (by linarith : 0 < ‖x - z‖) 2
  have hk : 0 ≤ gammaHalfKernel γ α₁ α₂ α₃ z x := by
    unfold gammaHalfKernel
    exact div_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      (Real.rpow_nonneg (by unfold normPlus; positivity) _))
      (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _))
  rw [fusion_secondKernel_norm, div_le_iff₀ hd]
  have hs : 1 ≤ 16 * ‖x - z‖ ^ 2 := by nlinarith [sq_nonneg (‖x - z‖ - 1 / 4)]
  calc
    _ ≤ gammaHalfKernel γ α₁ α₂ α₃ z x * (16 * ‖x - z‖ ^ 2) :=
      le_mul_of_one_le_right hk hs
    _ = _ := by ring

/-- Finiteness of the mass makes the exterior absolute integral finite, sample by sample. -/
theorem fusion_exteriorSecondKernel_integrable (γ α₁ α₂ α₃ : ℝ) (z : ℂ)
    (hz : ‖z‖ ≤ 1 / 4) (μ : Measure ℂ)
    (hkernel : (∫⁻ x, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂μ) < ⊤) :
    IntegrableOn (fun x : ℂ => (gammaHalfKernel γ α₁ α₂ α₃ z x : ℂ) / (x - z) ^ 2)
      (Metric.ball (0 : ℂ) (1 / 2))ᶜ μ := by
  have hf : Measurable (fun x : ℂ => (gammaHalfKernel γ α₁ α₂ α₃ z x : ℂ) / (x - z) ^ 2) :=
    (Complex.measurable_ofReal.comp ((fusion_measurable_gammaHalfKernel γ α₁ α₂ α₃).comp
      (measurable_const.prodMk measurable_id))).div ((measurable_id.sub_const z).pow_const 2)
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  calc
    _ ≤ ∫⁻ x in (Metric.ball (0 : ℂ) (1 / 2))ᶜ,
        ENNReal.ofReal (16 * gammaHalfKernel γ α₁ α₂ α₃ z x) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet.compl] with x hx
      have hx' : 1 / 2 ≤ ‖x‖ := by
        simpa only [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hx
      exact ENNReal.ofReal_le_ofReal (fusion_exteriorSecondKernel_bound γ α₁ α₂ α₃ z x hz hx')
    _ = ENNReal.ofReal 16 * ∫⁻ x in (Metric.ball (0 : ℂ) (1 / 2))ᶜ,
        ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂μ := by
      simp only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal 16 * ∫⁻ x, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂μ :=
      mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hkernel

end DOZZ.Proofs

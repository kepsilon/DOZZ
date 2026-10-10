/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.ExteriorMixedKernel

/-! # The exterior spatial integral is bounded by the unrooted Coulomb mass -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The exterior error has a samplewise bound by sixteen times the full mass. -/
theorem fusion_exteriorMixedKernel_integral_bound (γ α₁ α₂ α₃ : ℝ) (z : ℂ)
    (hz : ‖z‖ ≤ 1 / 4) (μ : Measure ℂ) (hm : coulombMass γ μ ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ < ⊤)
    (hzμ : μ {z} = 0) (h0μ : μ {0} = 0) (h1μ : μ {1} = 0) :
    ‖∫ x in (Metric.ball (0 : ℂ) (1 / 2))ᶜ,
      (gammaHalfKernel γ α₁ α₂ α₃ z x : ℂ) / (‖x - z‖ ^ 2 : ℝ) ∂μ‖ ≤
      16 * (coulombMass γ μ ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃).toReal := by
  let f := fun x : ℂ => (gammaHalfKernel γ α₁ α₂ α₃ z x : ℂ) / (‖x - z‖ ^ 2 : ℝ)
  have hbound : (∫⁻ x in (Metric.ball (0 : ℂ) (1 / 2))ᶜ, ENNReal.ofReal ‖f x‖ ∂μ) ≤
      ENNReal.ofReal 16 * coulombMass γ μ ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ := by
    calc
      _ ≤ ∫⁻ x in (Metric.ball (0 : ℂ) (1 / 2))ᶜ,
          ENNReal.ofReal (16 * gammaHalfKernel γ α₁ α₂ α₃ z x) ∂μ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet.compl] with x hx
        have hx' : 1 / 2 ≤ ‖x‖ := by
          simpa only [Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_lt] using hx
        apply ENNReal.ofReal_le_ofReal
        have h := fusion_exteriorSecondKernel_bound γ α₁ α₂ α₃ z x hz hx'
        rw [fusion_secondKernel_norm] at h
        dsimp only [f]
        rw [norm_div, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg (by unfold gammaHalfKernel normPlus; positivity),
          Real.norm_of_nonneg (sq_nonneg _)]
        exact h
      _ = ENNReal.ofReal 16 * ∫⁻ x in (Metric.ball (0 : ℂ) (1 / 2))ᶜ,
          ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂μ := by
        simp only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal 16 * ∫⁻ x, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂μ :=
        mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)
      _ = _ := by rw [← fusion_gammaHalfMass_kernel γ α₁ α₂ α₃ z μ hzμ h0μ h1μ]
  calc
    _ ≤ (∫⁻ x in (Metric.ball (0 : ℂ) (1 / 2))ᶜ, ENNReal.ofReal ‖f x‖ ∂μ).toReal :=
      norm_integral_le_lintegral_norm _
    _ ≤ (ENNReal.ofReal 16 * coulombMass γ μ ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃).toReal :=
      ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hm.ne) hbound
    _ = _ := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 16)]

/-- Multiplying by an inverse power improves the exterior bound to the preceding inverse order. -/
theorem fusion_exterior_mixed_inverse_integral_bound (γ α₁ α₂ α₃ s : ℝ) (z : ℂ)
    (hz : ‖z‖ ≤ 1 / 4) (μ : Measure ℂ)
    (hm0 : coulombMass γ μ ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ ≠ 0)
    (hm : coulombMass γ μ ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ < ⊤)
    (hzμ : μ {z} = 0) (h0μ : μ {0} = 0) (h1μ : μ {1} = 0) :
    ‖((coulombMass γ μ ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ ^ s).toReal : ℂ) *
      (∫ x in (Metric.ball (0 : ℂ) (1 / 2))ᶜ,
        (gammaHalfKernel γ α₁ α₂ α₃ z x : ℂ) / (‖x - z‖ ^ 2 : ℝ) ∂μ)‖ ≤
      16 * (coulombMass γ μ ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ ^ (s + 1)).toReal := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
  calc
    _ ≤ (coulombMass γ μ ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ ^ s).toReal *
        (16 * (coulombMass γ μ ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃).toReal) :=
      mul_le_mul_of_nonneg_left (fusion_exteriorMixedKernel_integral_bound γ α₁ α₂ α₃ z hz μ hm hzμ h0μ h1μ)
        ENNReal.toReal_nonneg
    _ = _ := by
      rw [ENNReal.rpow_add s 1 hm0 hm.ne, ENNReal.rpow_one, ENNReal.toReal_mul]
      ring

end DOZZ.Proofs

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.ScaledFactor
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod

/-! # Dominated convergence for the signed rescaled spatial integral -/

@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- An arbitrary integrable planar kernel can be multiplied by the uniformly bounded rooted
factor. This includes its signed real and complex components. -/
theorem fusionScaledIntegral_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hα : γ / 2 ≤ α₁) (hα₁ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (s : ℝ) (hs : s < 0)
    (K : ℂ → ℂ) (hK : Integrable K volume) :
    Tendsto (fun z : ℂ => ∫ y : ℂ, K y *
      (fusionScaledFactor P M γ α₁ α₂ α₃ s y z : ℂ)) (nhds 0)
      (nhds ((∫ y : ℂ, K y) *
        ((∫⁻ ω, fusionMovingMass γ α₁ α₂ α₃ 1 0 (M ω) ^ s ∂P).toReal : ℂ))) := by
  obtain ⟨B, hB, hbound⟩ := fusionScaledFactor_uniform_bound P X hX γ hγ hγ2 M hM α₁ α₂ α₃ s hs.le
  have hmeas := fusionScaledFactor_measurable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ s
  have hF : ∀ᶠ z : ℂ in nhds 0, AEStronglyMeasurable
      (fun y => K y * (fusionScaledFactor P M γ α₁ α₂ α₃ s y z : ℂ)) volume := by
    apply Eventually.of_forall
    intro z
    exact hK.aestronglyMeasurable.mul
      ((Complex.measurable_ofReal.comp (hmeas.comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable)
  have hdom : ∀ᶠ z : ℂ in nhds 0, ∀ᵐ y : ℂ ∂volume,
      ‖K y * (fusionScaledFactor P M γ α₁ α₂ α₃ s y z : ℂ)‖ ≤ ‖K y‖ * B := by
    have hz : ∀ᶠ z : ℂ in nhds 0, ‖z‖ ≤ 1 := by
      exact ((continuous_norm.tendsto (0 : ℂ)).eventually_lt_const (by simp)).mono fun z h => h.le
    filter_upwards [hz] with z hz
    exact ae_of_all _ fun y => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hbound y z hz) (norm_nonneg _)
  have hlim : ∀ᵐ y : ℂ ∂volume, Tendsto
      (fun z : ℂ => K y * (fusionScaledFactor P M γ α₁ α₂ α₃ s y z : ℂ)) (nhds 0)
      (nhds (K y * ((∫⁻ ω, fusionMovingMass γ α₁ α₂ α₃ 1 0 (M ω) ^ s ∂P).toReal : ℂ))) := by
    filter_upwards [Measure.ae_ne volume (0 : ℂ)] with y hy
    have hf := fusionScaledFactor_tendsto P X hX γ hγ hγ2 M hM α₁ α₂ α₃
      hα hα₁ hα₂ hα₃ y hy s hs
    have he : (∫⁻ ω, fusionMovingMass γ α₁ α₂ α₃ y 0 (M ω) ^ s ∂P) =
        ∫⁻ ω, fusionMovingMass γ α₁ α₂ α₃ 1 0 (M ω) ^ s ∂P := by
      simp only [fusionMovingMass, fusionMovingKernel, mul_zero]
    rw [he] at hf
    exact tendsto_const_nhds.mul (Complex.continuous_ofReal.continuousAt.tendsto.comp hf)
  have h := tendsto_integral_filter_of_dominated_convergence (fun y => ‖K y‖ * B)
    hF hdom (hK.norm.mul_const B) hlim
  simpa only [integral_mul_const] using h

/-- Joint measurability makes the spatial integral a measurable function of the moving point. -/
theorem fusionScaledIntegral_measurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ s : ℝ) (K : ℂ → ℂ) (hK : Measurable K) :
    Measurable (fun z : ℂ => ∫ y : ℂ, K y *
      (fusionScaledFactor P M γ α₁ α₂ α₃ s y z : ℂ)) := by
  have hmeas := fusionScaledFactor_measurable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ s
  have h : Measurable (fun q : ℂ × ℂ => K q.1 *
      (fusionScaledFactor P M γ α₁ α₂ α₃ s q.1 q.2 : ℂ)) :=
    (hK.comp measurable_fst).mul (Complex.measurable_ofReal.comp hmeas)
  exact h.stronglyMeasurable.integral_prod_left'.measurable

end DOZZ.Proofs

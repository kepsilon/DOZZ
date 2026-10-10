/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.DifferenceSpatialSplit
/-! # Signed time integrability and the full KRV split -/
@[expose] public section
open MeasureTheory Set
namespace DOZZ.Proofs
/-- The local signed expectation has an integrable time majorant after scaling. -/
theorem fusion_localDifference_time_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hlo : γ / 2 + 1 / γ < α₁) (hα₁ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (p : ℝ) (hp : 0 ≤ p)
    (z : ℂ) (hz : z ≠ 0) (hz4 : ‖z‖ ≤ 1 / 4) :
    IntegrableOn (fun t : ℝ => ∫ ω,
      (fusionUnrootedSegment γ α₁ α₂ α₃ t z (M ω) ^ (-p - 1)).toReal *
        (∫ x in Metric.ball (0 : ℂ) (1 / 2), fusionDifferenceKernel γ α₁ α₂ α₃ z x ∂M ω) ∂P) (Icc 0 1) volume := by
  let K := planarDifferenceKernel (γ ^ 2 / 2) (γ * α₁) 1
  obtain ⟨hk, hβ, hβ2, _, _⟩ := fusion_difference_parameters γ α₁ hγ hlo hα₁
  have hK : Integrable K volume := (planar_difference_integral _ _ hk hβ hβ2 1).1
  obtain ⟨B, _, hb⟩ := fusionInterpolatedFactor_uniform_bound P X hX γ hγ hγ2 M hM α₁ α₂ α₃ (-p - 1) (by linarith)
  have hf : Measurable (fusionDifferenceKernel γ α₁ α₂ α₃ z) := by
    have hm : Measurable (fun x : ℂ => (z, x)) := measurable_const.prodMk measurable_id
    simpa only [Function.comp_def] using (fusionDifferenceKernel_measurable γ α₁ α₂ α₃).comp hm
  have hm := fusion_segment_time_expectation_measurable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ (-p - 1) z
    ((Metric.ball (0 : ℂ) (1 / 2)).indicator (fusionDifferenceKernel γ α₁ α₂ α₃ z))
    (hf.indicator Metric.isOpen_ball.measurableSet)
  simp only [integral_indicator Metric.isOpen_ball.measurableSet] at hm
  apply (integrable_const (‖z‖ ^ (γ * (Q γ - α₁)) * (∫ y : ℂ, ‖K y‖ * B))).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  rw [fusion_localDifference_rooting_scaled P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hlo hα₁ hα₂ hα₃ p hp t ht z hz hz4,
    norm_mul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (norm_nonneg z) _)
  apply norm_integral_le_of_norm_le (hK.norm.mul_const B)
  exact ae_of_all _ fun y => by
    rw [norm_mul, Real.norm_eq_abs]
    simpa only [Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_left (hb t ht y z (by linarith)) (norm_nonneg (K y))
/-- The full signed time integral splits into its local and exterior parts. -/
theorem fusion_difference_time_split {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hlo : γ / 2 + 1 / γ < α₁) (hα₁ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (p : ℝ) (hp : 0 ≤ p)
    (z : ℂ) (hz : z ≠ 0) (hz4 : ‖z‖ ≤ 1 / 4) :
    let I := fun t ω => (fusionUnrootedSegment γ α₁ α₂ α₃ t z (M ω) ^ (-p - 1)).toReal
    let f := fusionDifferenceKernel γ α₁ α₂ α₃ z
    (∫ t in Icc (0 : ℝ) 1, ∫ ω, I t ω * (∫ x, f x ∂M ω) ∂P) =
      (∫ t in Icc (0 : ℝ) 1, ∫ ω, I t ω * (∫ x in Metric.ball (0 : ℂ) (1 / 2), f x ∂M ω) ∂P) +
      (∫ t in Icc (0 : ℝ) 1, ∫ ω, I t ω * (∫ x in (Metric.ball (0 : ℂ) (1 / 2))ᶜ, f x ∂M ω) ∂P) := by
  intro I f
  have hf : Measurable f := by
    have hm : Measurable (fun x : ℂ => (z, x)) := measurable_const.prodMk measurable_id
    simpa only [Function.comp_def] using (fusionDifferenceKernel_measurable γ α₁ α₂ α₃).comp hm
  have hm := fusion_segment_time_expectation_measurable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ (-p - 1) z
    ((Metric.ball (0 : ℂ) (1 / 2))ᶜ.indicator f) (hf.indicator Metric.isOpen_ball.measurableSet.compl)
  simp only [integral_indicator Metric.isOpen_ball.measurableSet.compl] at hm
  obtain ⟨C, _, hb⟩ := fusion_difference_exterior_expectation_bound P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hα₁ hα₂ hα₃ p hp
  have hiR : IntegrableOn (fun t => ∫ ω, I t ω * (∫ x in (Metric.ball (0 : ℂ) (1 / 2))ᶜ, f x ∂M ω) ∂P) (Icc 0 1) volume := by
    apply (integrable_const (C * ‖z‖)).mono' hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (hb t ht z hz hz4).2
  have hiL := fusion_localDifference_time_integrable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hlo hα₁ hα₂ hα₃ p hp z hz hz4
  calc
    _ = ∫ t in Icc (0 : ℝ) 1, ((∫ ω, I t ω * (∫ x in Metric.ball (0 : ℂ) (1 / 2), f x ∂M ω) ∂P) +
      (∫ ω, I t ω * (∫ x in (Metric.ball (0 : ℂ) (1 / 2))ᶜ, f x ∂M ω) ∂P)) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        exact fusion_difference_spatial_expectation_split P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hlo hα₁ hα₂ hα₃ p hp t ht z hz hz4
    _ = _ := integral_add hiL hiR
end DOZZ.Proofs

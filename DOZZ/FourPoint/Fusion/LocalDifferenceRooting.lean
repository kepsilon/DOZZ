/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.DifferenceScaling
public import DOZZ.FourPoint.Fusion.Parameters
/-! # Rooting and scaling the literal local mass difference -/
@[expose] public section
open MeasureTheory Set
namespace DOZZ.Proofs
/-- The local signed mass difference has exactly the rescaled rooted segment integral. -/
theorem fusion_localDifference_rooting_scaled {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hlo : γ / 2 + 1 / γ < α₁) (hα₁ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (p : ℝ) (hp : 0 ≤ p)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (z : ℂ) (hz : z ≠ 0) (hz4 : ‖z‖ ≤ 1 / 4) :
    (∫ ω, (fusionUnrootedSegment γ α₁ α₂ α₃ t z (M ω) ^ (-p - 1)).toReal *
      (∫ x in Metric.ball (0 : ℂ) (1 / 2), fusionDifferenceKernel γ α₁ α₂ α₃ z x ∂M ω) ∂P) =
      ‖z‖ ^ (γ * (Q γ - α₁)) *
        ∫ y : ℂ, planarDifferenceKernel (γ ^ 2 / 2) (γ * α₁) 1 y *
          fusionInterpolatedFactor P M γ α₁ α₂ α₃ (-p - 1) t y z := by
  let B := Metric.ball (0 : ℂ) (1 / 2)
  have hf : Measurable (fusionDifferenceKernel γ α₁ α₂ α₃ z) := by
    have hm : Measurable (fun x : ℂ => (z, x)) := measurable_const.prodMk measurable_id
    simpa only [Function.comp_def] using (fusionDifferenceKernel_measurable γ α₁ α₂ α₃).comp hm
  obtain ⟨hk, hβ, hβ2, _, _⟩ := fusion_difference_parameters γ α₁ hγ hlo hα₁
  have hfi := fusion_difference_local_integrable γ α₁ α₂ α₃ hk hβ hβ2 z hz
  have h := (fusion_segment_rooting P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hα₁ hα₂ hα₃
    t ht (-p - 1) (by linarith) z hz hz4 (B.indicator (fusionDifferenceKernel γ α₁ α₂ α₃ z))
    (hf.indicator Metric.isOpen_ball.measurableSet) hfi).2.2
  have he : (fun u => B.indicator (fusionDifferenceKernel γ α₁ α₂ α₃ z) u *
      (∫⁻ ω, fusionUnrootedSegment γ α₁ α₂ α₃ t z (gmcRootedMeasure γ u (M ω)) ^ (-p - 1) ∂P).toReal) =
      B.indicator (fun u => fusionDifferenceKernel γ α₁ α₂ α₃ z u *
        (∫⁻ ω, fusionUnrootedSegment γ α₁ α₂ α₃ t z (gmcRootedMeasure γ u (M ω)) ^ (-p - 1) ∂P).toReal) := by
    funext u
    by_cases hu : u ∈ B
    · simp only [Set.indicator_of_mem hu]
    · simp only [Set.indicator_of_notMem hu, zero_mul]
  rw [he, integral_indicator (show MeasurableSet B from Metric.isOpen_ball.measurableSet)] at h
  rw [gmcReferenceMeasure_restrict_unit_chart B Metric.isOpen_ball.measurableSet
    (fun x hx => by
      have hx' : ‖x‖ < 1 / 2 := by simpa only [B, Metric.mem_ball, dist_zero_right] using hx
      linarith)] at h
  simp only [integral_indicator (show MeasurableSet B from Metric.isOpen_ball.measurableSet)] at h
  rw [h, fusion_difference_reference_scaled P X hX γ hγ hγ2 M hM α₁ α₂ α₃ t (-p - 1) z hz,
    ← fusion_exponent_eq γ α₁ hγ.ne']
end DOZZ.Proofs

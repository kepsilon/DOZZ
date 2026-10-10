/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.LocalDifferenceRooting
public import DOZZ.FourPoint.Fusion.DifferenceExteriorExpectation
public import DOZZ.FourPoint.Fusion.DifferenceMassIntegral
/-! # The signed local and exterior split -/
@[expose] public section
open MeasureTheory Set
namespace DOZZ.Proofs
/-- Local rooting and the exterior mass majorant justify splitting the signed expectation. -/
theorem fusion_difference_spatial_expectation_split {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hlo : γ / 2 + 1 / γ < α₁) (hα₁ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (p : ℝ) (hp : 0 ≤ p)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (z : ℂ) (hz : z ≠ 0) (hz4 : ‖z‖ ≤ 1 / 4) :
    let I := fun ω => (fusionUnrootedSegment γ α₁ α₂ α₃ t z (M ω) ^ (-p - 1)).toReal
    let f := fusionDifferenceKernel γ α₁ α₂ α₃ z
    (∫ ω, I ω * (∫ x, f x ∂M ω) ∂P) =
      (∫ ω, I ω * (∫ x in Metric.ball (0 : ℂ) (1 / 2), f x ∂M ω) ∂P) +
      (∫ ω, I ω * (∫ x in (Metric.ball (0 : ℂ) (1 / 2))ᶜ, f x ∂M ω) ∂P) := by
  intro I f
  let B := Metric.ball (0 : ℂ) (1 / 2)
  have hf : Measurable f := by
    have hm : Measurable (fun x : ℂ => (z, x)) := measurable_const.prodMk measurable_id
    simpa only [Function.comp_def] using (fusionDifferenceKernel_measurable γ α₁ α₂ α₃).comp hm
  obtain ⟨hk, hβ, hβ2, _, _⟩ := fusion_difference_parameters γ α₁ hγ hlo hα₁
  have hfi := fusion_difference_local_integrable γ α₁ α₂ α₃ hk hβ hβ2 z hz
  have hl := (fusion_segment_rooting P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hα₁ hα₂ hα₃ t ht
    (-p - 1) (by linarith) z hz hz4 (B.indicator f) (hf.indicator Metric.isOpen_ball.measurableSet) hfi).1
  simp only [integral_indicator (show MeasurableSet B from Metric.isOpen_ball.measurableSet)] at hl
  obtain ⟨C, _, hb⟩ := fusion_difference_exterior_expectation_bound P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hα₁ hα₂ hα₃ p hp
  have hr := (hb t ht z hz hz4).1
  have he : (fun ω => I ω * (∫ x, f x ∂M ω)) =ᵐ[P]
      (fun ω => I ω * (∫ x in B, f x ∂M ω) + I ω * (∫ x in Bᶜ, f x ∂M ω)) := by
    filter_upwards [fusion_gammaHalfMass_pos_finite_ae P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hα₁ hα₂ hα₃ z hz hz4,
      fusion_zeroMass_pos_finite_ae P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hα₁ hα₂ hα₃,
      gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM z,
      gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 0,
      gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 1] with ω hbω haω hωz hω0 hω1
    have hfull := (fusion_difference_mass_integral γ α₁ α₂ α₃ z (M ω) hωz hω0 hω1 hbω.2 haω.2).1
    rw [← integral_add_compl (show MeasurableSet B from Metric.isOpen_ball.measurableSet) hfull, mul_add]
  rw [integral_congr_ae he, integral_add hl hr]
end DOZZ.Proofs

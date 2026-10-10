/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.DifferenceExteriorMass
public import DOZZ.FourPoint.Fusion.SegmentSpatialMeasurable
public import DOZZ.FourPoint.Fusion.MassPositiveFinite
/-! # A uniform first-order exterior error for KRV -/
@[expose] public section
open MeasureTheory Set
namespace DOZZ.Proofs
/-- The signed exterior expectation is integrable and uniformly of order the root displacement. -/
theorem fusion_difference_exterior_expectation_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hα₁ : α₁ < 2 / γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (p : ℝ) (hp : 0 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ z : ℂ, z ≠ 0 → ‖z‖ ≤ 1 / 4 →
      Integrable (fun ω => (fusionUnrootedSegment γ α₁ α₂ α₃ t z (M ω) ^ (-p - 1)).toReal *
        (∫ x in (Metric.ball (0 : ℂ) (1 / 2))ᶜ, fusionDifferenceKernel γ α₁ α₂ α₃ z x ∂M ω)) P ∧
      ‖∫ ω, (fusionUnrootedSegment γ α₁ α₂ α₃ t z (M ω) ^ (-p - 1)).toReal *
        (∫ x in (Metric.ball (0 : ℂ) (1 / 2))ᶜ, fusionDifferenceKernel γ α₁ α₂ α₃ z x ∂M ω) ∂P‖ ≤ C * ‖z‖ := by
  obtain ⟨C, hC, hb⟩ := fusionUnrootedSegment_inverse_uniform P X hX γ hγ hγ2 M hM α₁ α₂ α₃ p hp
  let D := fusionExteriorDifferenceConstant γ
  have hD : 0 ≤ D := by dsimp [D, fusionExteriorDifferenceConstant]; positivity
  refine ⟨D * C, mul_nonneg hD hC.le, ?_⟩
  intro t ht z hz hz4
  let I := fun ω => fusionUnrootedSegment γ α₁ α₂ α₃ t z (M ω)
  let B := (Metric.ball (0 : ℂ) (1 / 2))ᶜ
  let f := fusionDifferenceKernel γ α₁ α₂ α₃ z
  have hfm : Measurable f := by
    have hm : Measurable (fun x : ℂ => (z, x)) := measurable_const.prodMk measurable_id
    simpa only [Function.comp_def] using (fusionDifferenceKernel_measurable γ α₁ α₂ α₃).comp hm
  have hIm : AEMeasurable (fun ω => I ω ^ (-p)) P :=
    ((gmc_coulombMass_aemeasurable P X hX γ hγ hγ2 M hM _ _ _).const_mul _ |>.add
      ((gmc_coulombMass_aemeasurable P X hX γ hγ hγ2 M hM _ _ _).const_mul _)).pow_const _
  have hib : (∫⁻ ω, I ω ^ (-p) ∂P) ≤ ENNReal.ofReal C := hb t ht z (by linarith)
  have hit := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hib
  have hmaj : Integrable (fun ω => (D * ‖z‖) * (I ω ^ (-p)).toReal) P :=
    (integrable_toReal_of_lintegral_ne_top hIm hit).const_mul _
  have hm := fusion_segment_spatial_aestronglyMeasurable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ t (-p - 1) z
    (B.indicator f) (hfm.indicator Metric.isOpen_ball.measurableSet.compl)
  simp only [integral_indicator (show MeasurableSet B from Metric.isOpen_ball.measurableSet.compl)] at hm
  have hd : ∀ᵐ ω ∂P, ‖(I ω ^ (-p - 1)).toReal * (∫ x in B, f x ∂M ω)‖ ≤
      (D * ‖z‖) * (I ω ^ (-p)).toReal := by
    filter_upwards [fusion_gammaHalfMass_pos_finite_ae P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hα₁ hα₂ hα₃ z hz hz4,
      fusion_zeroMass_pos_finite_ae P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hα₁ hα₂ hα₃,
      gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM z,
      gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 0,
      gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM 1] with ω hzI h0I hωz hω0 hω1
    have hIf := fusion_convexMass_pos_finite _ _ t ht hzI.1 hzI.2 h0I.1 h0I.2
    have hIt : I ω ^ (-p) ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero hIf.1 hIf.2
    have hab := fusion_difference_exterior_absolute_bound γ α₁ α₂ α₃ t p ht hp z hz4 (M ω) hωz hω0 hω1
    have hbound := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIt) hab
    change ((∫⁻ x in B, ENNReal.ofReal |f x| ∂M ω) * I ω ^ (-p - 1)).toReal ≤
      (ENNReal.ofReal (D * ‖z‖) * I ω ^ (-p)).toReal at hbound
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (mul_nonneg hD (norm_nonneg z))] at hbound
    calc
      _ = (I ω ^ (-p - 1)).toReal * ‖∫ x in B, f x ∂M ω‖ := by
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      _ ≤ (I ω ^ (-p - 1)).toReal * (∫⁻ x in B, ENNReal.ofReal |f x| ∂M ω).toReal := by
        exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using norm_integral_le_lintegral_norm (μ := (M ω).restrict B) f) ENNReal.toReal_nonneg
      _ ≤ _ := by simpa only [mul_comm] using hbound
  refine ⟨hmaj.mono' hm hd, ?_⟩
  calc
    _ ≤ ∫ ω, (D * ‖z‖) * (I ω ^ (-p)).toReal ∂P := norm_integral_le_of_norm_le hmaj hd
    _ = (D * ‖z‖) * (∫⁻ ω, I ω ^ (-p) ∂P).toReal := by
      rw [integral_const_mul, integral_toReal hIm (ae_lt_top' hIm hit)]
    _ ≤ (D * ‖z‖) * C := mul_le_mul_of_nonneg_left
      ((ENNReal.toReal_mono ENNReal.ofReal_ne_top hib).trans_eq (ENNReal.toReal_ofReal hC.le))
      (mul_nonneg hD (norm_nonneg _))
    _ = _ := by ring
end DOZZ.Proofs

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.MassSegment
public import DOZZ.FourPoint.Fusion.InterpolatedInverseMoments
public import DOZZ.FourPoint.Fusion.RootedIntegrability
/-! # Signed rooting for the positive KRV mass segment -/
@[expose] public section
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace DOZZ.Proofs
/-- Rooting the unrooted segment gives exactly the two moving rooted endpoints. -/
theorem fusionUnrootedSegment_rooted_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ t : ℝ) (y z : ℂ) :
    ∀ᵐ ω ∂P, fusionUnrootedSegment γ α₁ α₂ α₃ t z (gmcRootedMeasure γ (y * z) (M ω)) =
      fusionInterpolatedMass γ α₁ α₂ α₃ t y z (M ω) := by
  filter_upwards [fusionMovingMass_eq_rooted_ae P X hX γ hγ hγ2 M hM α₁ α₂ α₃ y z,
    fusionRootOnlyMass_eq_rooted_ae P X hX γ hγ hγ2 M hM α₁ α₂ α₃ y z] with ω h1 h0
  simp only [fusionUnrootedSegment, fusionInterpolatedMass, h1, h0]
/-- The rooted inverse expectation is bounded uniformly at every spatial root. -/
theorem fusionUnrootedSegment_rooted_inverse_uniform {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ s : ℝ) (hs : s ≤ 0) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ t ∈ Icc (0 : ℝ) 1, ∀ z : ℂ, z ≠ 0 → ‖z‖ ≤ 1 → ∀ u : ℂ,
      (∫⁻ ω, fusionUnrootedSegment γ α₁ α₂ α₃ t z (gmcRootedMeasure γ u (M ω)) ^ s ∂P) ≤ C := by
  obtain ⟨C, hC, hb⟩ := fusionInterpolatedMass_inverse_uniform P X hX γ hγ hγ2 M hM α₁ α₂ α₃ s hs
  refine ⟨C, hC, ?_⟩
  intro t ht z hz hz1 u
  have he : (∫⁻ ω, fusionUnrootedSegment γ α₁ α₂ α₃ t z (gmcRootedMeasure γ u (M ω)) ^ s ∂P) =
      ∫⁻ ω, fusionInterpolatedMass γ α₁ α₂ α₃ t (u / z) z (M ω) ^ s ∂P := by
    apply lintegral_congr_ae
    filter_upwards [fusionUnrootedSegment_rooted_ae P X hX γ hγ hγ2 M hM α₁ α₂ α₃ t (u / z) z] with ω hω
    simpa only [div_mul_cancel₀ _ hz] using congrArg (fun q : ℝ≥0∞ => q ^ s) hω
  rw [he]
  exact hb t ht (u / z) z hz1
/-- Finite endpoint masses make a negative segment power nonzero almost surely. -/
theorem fusionUnrootedSegment_inverse_ne_zero_ae {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hα₁ : α₁ < 2 / γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (t s : ℝ) (hs : s < 0) (z : ℂ) (hz : z ≠ 0) (hz4 : ‖z‖ ≤ 1 / 4) :
    ∀ᵐ ω ∂P, fusionUnrootedSegment γ α₁ α₂ α₃ t z (M ω) ^ s ≠ 0 := by
  filter_upwards [fusion_gammaHalfMass_pos_finite_ae P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hα₁ hα₂ hα₃ z hz hz4,
    fusion_zeroMass_pos_finite_ae P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hα₁ hα₂ hα₃] with ω hωz hω0
  have hf : fusionUnrootedSegment γ α₁ α₂ α₃ t z (M ω) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hωz.2,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hω0.2⟩
  intro he
  rcases ENNReal.rpow_eq_zero_iff.mp he with ⟨_, hp⟩ | ⟨ht, _⟩
  · linarith
  · exact hf ht
/-- An integrable signed reference observable can be rooted against the segment inverse power. -/
theorem fusion_segment_rooting {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hα₁ : α₁ < 2 / γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (s : ℝ) (hs : s < 0)
    (z : ℂ) (hz : z ≠ 0) (hz4 : ‖z‖ ≤ 1 / 4)
    (f : ℂ → ℝ) (hfm : Measurable f) (hfi : Integrable f gmcReferenceMeasure) :
    Integrable (fun ω => (fusionUnrootedSegment γ α₁ α₂ α₃ t z (M ω) ^ s).toReal * (∫ x, f x ∂M ω)) P ∧
    Integrable (fun u => f u * (∫⁻ ω,
      fusionUnrootedSegment γ α₁ α₂ α₃ t z (gmcRootedMeasure γ u (M ω)) ^ s ∂P).toReal) gmcReferenceMeasure ∧
    (∫ ω, (fusionUnrootedSegment γ α₁ α₂ α₃ t z (M ω) ^ s).toReal * (∫ x, f x ∂M ω) ∂P) =
      ∫ u, f u * (∫⁻ ω,
        fusionUnrootedSegment γ α₁ α₂ α₃ t z (gmcRootedMeasure γ u (M ω)) ^ s ∂P).toReal ∂gmcReferenceMeasure := by
  let G := fun μ : Measure ℂ => fusionUnrootedSegment γ α₁ α₂ α₃ t z μ ^ s
  have hG := fusionUnrootedSegment_measurable γ α₁ α₂ α₃ t s z
  obtain ⟨C, hC, hb⟩ := fusionUnrootedSegment_rooted_inverse_uniform P X hX γ hγ hγ2 M hM α₁ α₂ α₃ s hs.le
  have habs : (∫⁻ u, ENNReal.ofReal |f u| * (∫⁻ ω, G (gmcRootedMeasure γ u (M ω)) ∂P) ∂gmcReferenceMeasure) < ⊤ := by
    calc
      _ ≤ ∫⁻ u, ENNReal.ofReal |f u| * C ∂gmcReferenceMeasure :=
        lintegral_mono fun u => mul_le_mul' le_rfl (hb t ht z hz (by linarith) u)
      _ = (∫⁻ u, ENNReal.ofReal |f u| ∂gmcReferenceMeasure) * C :=
        lintegral_mul_const _ (ENNReal.measurable_ofReal.comp (by simpa only [Real.norm_eq_abs] using hfm.norm))
      _ < ⊤ := ENNReal.mul_lt_top (by
        have h := hfi.hasFiniteIntegral
        rw [hasFiniteIntegral_iff_norm] at h
        simpa only [Real.norm_eq_abs] using h) hC
  have hsample := fusion_rooted_spatial_integrable P X hX γ hγ hγ2 M hM (fun u => (f u : ℂ))
    (Complex.measurable_ofReal.comp hfm) G hG
    (fusionUnrootedSegment_inverse_ne_zero_ae P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hα₁ hα₂ hα₃ t s hs z hz hz4)
    (by simpa only [Complex.norm_real, Real.norm_eq_abs] using habs)
  have hreal : ∀ᵐ ω ∂P, Integrable f (M ω) := hsample.mono fun ω h => by
    convert h.re using 1
  exact fusion_rooted_real_integral P X hX γ hγ hγ2 M hM f hfm hreal G hG habs
end DOZZ.Proofs

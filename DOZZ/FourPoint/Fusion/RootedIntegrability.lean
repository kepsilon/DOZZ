/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.ComplexRooting

/-! # Recovering samplewise spatial integrability from the absolute rooted bound -/

@[expose] public section
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- If the weighting functional is nonzero almost surely, the absolute rooted bound implies
samplewise integrability of the spatial observable. -/
theorem fusion_rooted_spatial_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (f : ℂ → ℂ) (hf : Measurable f)
    (G : Measure ℂ → ℝ≥0∞) (hG : Measurable G)
    (hG0 : ∀ᵐ ω ∂P, G (M ω) ≠ 0)
    (hb : (∫⁻ u, ENNReal.ofReal ‖f u‖ *
      (∫⁻ ω, G (gmcRootedMeasure γ u (M ω)) ∂P) ∂gmcReferenceMeasure) < ⊤) :
    ∀ᵐ ω ∂P, Integrable f (M ω) := by
  let L := fun ω => (∫⁻ u, ENNReal.ofReal ‖f u‖ ∂M ω) * G (M ω)
  have hM' := gmc_measure_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM
  have hL : AEMeasurable L P :=
    ((Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp hf.norm)).comp_aemeasurable hM').mul
      (hG.comp_aemeasurable hM')
  have hid : (∫⁻ ω, L ω ∂P) = ∫⁻ u, ENNReal.ofReal ‖f u‖ *
      (∫⁻ ω, G (gmcRootedMeasure γ u (M ω)) ∂P) ∂gmcReferenceMeasure := by
    calc
      _ = ∫⁻ ω, ∫⁻ u, ENNReal.ofReal ‖f u‖ * G (M ω) ∂M ω ∂P := by
        apply lintegral_congr
        intro ω
        exact (lintegral_mul_const _ (ENNReal.measurable_ofReal.comp hf.norm)).symm
      _ = ∫⁻ u, ∫⁻ ω, ENNReal.ofReal ‖f u‖ * G (gmcRootedMeasure γ u (M ω)) ∂P
          ∂gmcReferenceMeasure :=
        DOZZ.equatorGFF_rooted_GMC_identity P X hX γ hγ hγ2 M hM
          (fun u _ μ => ENNReal.ofReal ‖f u‖ * G μ)
          ((ENNReal.measurable_ofReal.comp (hf.norm.comp measurable_fst)).mul
            (hG.comp (measurable_snd.comp measurable_snd)))
      _ = _ := by
        apply lintegral_congr
        intro u
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hLb : (∫⁻ ω, L ω ∂P) < ⊤ := hid ▸ hb
  filter_upwards [ae_lt_top' hL hLb.ne, hG0] with ω hω h0
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  by_contra ht
  have ht' : (∫⁻ u, ENNReal.ofReal ‖f u‖ ∂M ω) = ⊤ := not_lt_top_iff.mp ht
  dsimp only [L] at hω
  rw [ht', ENNReal.top_mul h0] at hω
  exact lt_irrefl _ hω

end DOZZ.Proofs

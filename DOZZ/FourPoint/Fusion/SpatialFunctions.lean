/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.SpatialExpectationMeasurable
/-! # Restricted signed spatial expectations -/
@[expose] public section
open MeasureTheory Set
namespace DOZZ.Proofs
noncomputable def fusionPureSpatial {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ p : ℝ) (B : Set ℂ) (z : ℂ) : ℂ :=
  ∫ ω, ((coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ ^ (-p - 1)).toReal : ℂ) *
    (∫ x in B, (gammaHalfKernel γ α₁ α₂ α₃ z x : ℂ) / (x - z) ^ 2 ∂M ω) ∂P
noncomputable def fusionMixedSpatial {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ p : ℝ) (B : Set ℂ) (z : ℂ) : ℂ :=
  ∫ ω, ((coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ ^ (-p - 1)).toReal : ℂ) *
    (∫ x in B, (gammaHalfKernel γ α₁ α₂ α₃ z x : ℂ) / (‖x - z‖ ^ 2 : ℝ) ∂M ω) ∂P
/-- Restricting the spatial kernel to a fixed measurable region preserves parameter measurability. -/
theorem fusionPureSpatial_measurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ p : ℝ) (B : Set ℂ) (hB : MeasurableSet B) :
    Measurable (fusionPureSpatial P M γ α₁ α₂ α₃ p B) := by
  let H := fun q : ℂ × ℂ => B.indicator
    (fun x : ℂ => (gammaHalfKernel γ α₁ α₂ α₃ q.1 x : ℂ) / (x - q.1) ^ 2) q.2
  have hH : Measurable H := by
    change Measurable ((Prod.snd ⁻¹' B).indicator
      (fun q : ℂ × ℂ => (gammaHalfKernel γ α₁ α₂ α₃ q.1 q.2 : ℂ) /
        (q.2 - q.1) ^ 2))
    exact ((Complex.measurable_ofReal.comp (fusion_measurable_gammaHalfKernel γ α₁ α₂ α₃)).div
      ((measurable_snd.sub measurable_fst).pow_const 2)).indicator (hB.preimage measurable_snd)
  have h := fusion_gammaHalf_spatial_expectation_measurable P X hX γ hγ hγ2 M hM
    α₁ α₂ α₃ (-p - 1) H hH
  unfold fusionPureSpatial
  simpa only [H, integral_indicator hB] using h
/-- Restricting the spatial kernel to a fixed measurable region preserves parameter measurability. -/
theorem fusionMixedSpatial_measurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ p : ℝ) (B : Set ℂ) (hB : MeasurableSet B) :
    Measurable (fusionMixedSpatial P M γ α₁ α₂ α₃ p B) := by
  let H := fun q : ℂ × ℂ => B.indicator
    (fun x : ℂ => (gammaHalfKernel γ α₁ α₂ α₃ q.1 x : ℂ) / (‖x - q.1‖ ^ 2 : ℝ)) q.2
  have hH : Measurable H := by
    change Measurable ((Prod.snd ⁻¹' B).indicator
      (fun q : ℂ × ℂ => (gammaHalfKernel γ α₁ α₂ α₃ q.1 q.2 : ℂ) /
        (‖q.2 - q.1‖ ^ 2 : ℝ)))
    exact ((Complex.measurable_ofReal.comp (fusion_measurable_gammaHalfKernel γ α₁ α₂ α₃)).div
      (Complex.measurable_ofReal.comp ((measurable_snd.sub measurable_fst).norm.pow_const 2))).indicator (hB.preimage measurable_snd)
  have h := fusion_gammaHalf_spatial_expectation_measurable P X hX γ hγ hγ2 M hM
    α₁ α₂ α₃ (-p - 1) H hH
  unfold fusionMixedSpatial
  simpa only [H, integral_indicator hB] using h
end DOZZ.Proofs

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.TranslatedRadialProjection
public import DOZZ.Brownian.Lateral.ReflectionJointLaw

/-! The complete lateral GMC carrier for the actual translated source projection. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DOZZ.Proofs

/-- The translated projection has stationarity, reflection, intensity and a genuine source
witness, with the literal off-center radial circle process. -/
theorem translated_lateral_isLateralGMCOf
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (z : ℂ) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (N : Ω → Measure ℂ) (hN : IsGMCOf P (translatedField X Xc z) γ N) :
    IsLateralGMCOf P γ (fun ω => lateralProjectedGMC γ
      (originRadialPath (fun ω x r => Xc ω (z+x) r - Xc ω z 0) ω) (N ω)) := by
  let Uc := fun ω x r => Xc ω (z+x) r - Xc ω z 0
  let A := originRadialPath Uc
  have hU := translated_field_isEquatorGFF P X Xc hX hc z
  have hcU := translated_field_circleAverage P X Xc hX hc z
  have hmU := translated_circle_jointMeasurable Xc hm z
  have hcontU := translated_circle_continuous P Xc hcont z
  have hA := originRadialPath_aemeasurable P _ Uc hcU hcontU
  have hZm := lateralProjectedGMC_aemeasurable P γ A hA N
    (equatorGFF_GMC_aemeasurable P _ hU γ hγ hγ2 N hN) hN.1
  have hsource := (translated_radial_sourceProjection P X Xc hX hc hm hcont
    z γ hγ hγ2 N hN).1
  refine ⟨hγ, hγ2, hX.1, hZm, ae_lateralProjectedGMC_interval_ne_top P γ A N hN.1,
    ?_, ?_, ?_, ⟨translatedField X Xc z, N, hsource⟩⟩
  · exact fun t => lateralProjectedGMC_translation_law P _ Uc hU hcU hmU hcontU
      γ hγ hγ2 N hN t
  · exact lateralProjectedGMC_reflection_law P _ Uc hU hcU hcontU γ hγ hγ2 N hN
  · exact fun a b _hab => lateralProjectedGMC_interval_intensity P _ Uc hU hcU hmU hcontU
      γ hγ hγ2 N hN a b


end DOZZ.Proofs

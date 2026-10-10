/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.TranslatedCanonicalWilliamsLaw
public import DOZZ.Correlations.Tails.WilliamsSourceInputLaw

/-! The translated canonical mass expressed using the original reflection witness. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

theorem translated_canonical_source_williams_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (z : ℂ) (γ α : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Q γ)
    (N : Ω → Measure ℂ) (hN : IsGMCOf P (translatedField X Xc z) γ N)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α B Z) :
    P.map (localSingularMass N (fun _ => 1) 0 γ α) =
      ((brownianMaximumReferenceLaw (Q γ-α)).prod P).map
        (fun q => ENNReal.ofReal (Real.exp (γ*q.1))*
          twoSidedReflectionCutMass γ q.1 B Z q.2) := by
  let Qν := P.map (fun ω => (B ω).1)
  have hQν : IsNegativeConditionedBrownianLaw (Q γ-α) Qν := hData.1.1.2
  have hl := translated_canonical_williams_mass_law P X Xc hX hc hm hcont
    z γ α hγ hγ2 hα N hN Qν hQν
  dsimp only at hl
  have hZt := translated_lateral_isLateralGMCOf P X Xc hX hc hm hcont
    z γ hγ hγ2 N hN
  rw [isLateralGMCOf_map_eq P P γ _ Z hZt hData.2.1] at hl
  exact hl.trans (williams_source_input_law P γ α hα B Z hData Qν hQν)

theorem actual_cut_mass_joint_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (γ : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hB : AEMeasurable B P) (hZ : AEMeasurable Z P)
    (hfin : ∀ᵐ ω ∂P, ∀ a b : ℝ, Z ω (Set.Icc a b) < ⊤) :
    AEMeasurable (fun q : ℝ × Ω => twoSidedReflectionCutMass γ q.1 B Z q.2) (μ.prod P) := by
  have hpair := hB.prodMk hZ
  have hInp : AEMeasurable (fun q : ℝ × Ω => (q.1,(B q.2,Z q.2))) (μ.prod P) :=
    measurable_fst.aemeasurable.prodMk
      (hpair.comp_quasiMeasurePreserving measurePreserving_snd.quasiMeasurePreserving)
  have hm := (measurable_williamsCutMassCode γ).comp_aemeasurable hInp
  apply hm.congr
  have hf := (measurePreserving_snd (μ := μ) (ν := P)).quasiMeasurePreserving.ae hfin
  filter_upwards [hf] with q hq
  exact williamsCutMassCode_eq γ q.1 (B q.2) (Z q.2) hq


end DOZZ.Proofs

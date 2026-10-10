/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.CanonicalSourceWilliamsLaw
public import DOZZ.Correlations.Tails.IndependentProductLaw
public import DOZZ.Correlations.Tails.SingularMassMeasurability

/-! The canonical leading mass has the prefactored Williams law on the source witness. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

theorem prefactored_source_williams_mass_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (γ : ℝ)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hB : AEMeasurable B P) (hZ : AEMeasurable Z P)
    (hfin : ∀ᵐ ω ∂P, ∀ a b : ℝ, Z ω (Set.Icc a b) < ⊤)
    (S : Ω → ℝ≥0∞) (hS : AEMeasurable S P) :
    AEMeasurable (fun q : ℝ × (Ω × Ω) =>
      (S q.2.2*twoSidedReflectionCutMass γ q.1 B Z q.2.1)*
        ENNReal.ofReal (Real.exp (γ*q.1))) (μ.prod (P.prod P)) := by
  have hProj := (measurePreserving_fst (μ := P) (ν := P)).comp
    (measurePreserving_snd (μ := μ) (ν := P.prod P))
  have hInp : AEMeasurable (fun q : ℝ × (Ω × Ω) => (q.1,(B q.2.1,Z q.2.1)))
      (μ.prod (P.prod P)) := measurable_fst.aemeasurable.prodMk
    ((hB.prodMk hZ).comp_quasiMeasurePreserving hProj.quasiMeasurePreserving)
  have hCut : AEMeasurable (fun q : ℝ × (Ω × Ω) =>
      twoSidedReflectionCutMass γ q.1 B Z q.2.1) (μ.prod (P.prod P)) := by
    have h := (measurable_williamsCutMassCode γ).comp_aemeasurable hInp
    apply h.congr
    filter_upwards [hProj.quasiMeasurePreserving.ae hfin] with q hq
    exact williamsCutMassCode_eq γ q.1 (B q.2.1) (Z q.2.1) hq
  have hPin := hS.comp_quasiMeasurePreserving
    ((measurePreserving_snd (μ := P) (ν := P)).comp
      (measurePreserving_snd (μ := μ) (ν := P.prod P))).quasiMeasurePreserving
  exact (hPin.mul hCut).mul ((measurable_fst.const_mul γ).exp.ennreal_ofReal).aemeasurable

theorem prefactored_canonical_source_williams_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (z : ℂ) (γ α : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Q γ)
    (N : Ω → Measure ℂ) (hN : IsGMCOf P (translatedField X Xc z) γ N)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α B Z)
    (S : Ω → ℝ≥0∞) (hS : AEMeasurable S P) :
    (P.prod P).map (fun q => S q.2*localSingularMass N (fun _ => 1) 0 γ α q.1) =
      ((brownianMaximumReferenceLaw (Q γ-α)).prod (P.prod P)).map
        (fun q => (S q.2.2*twoSidedReflectionCutMass γ q.1 B Z q.2.1)*
          ENNReal.ofReal (Real.exp (γ*q.1))) := by
  let : IsProbabilityMeasure P := hX.1
  let μ := brownianMaximumReferenceLaw (Q γ-α)
  let : IsProbabilityMeasure μ := isProbabilityMeasure_brownianMaximumReferenceLaw (sub_pos.mpr hα)
  let mass := localSingularMass N (fun _ => 1) 0 γ α
  let g := fun q : ℝ × Ω => ENNReal.ofReal (Real.exp (γ*q.1))*
    twoSidedReflectionCutMass γ q.1 B Z q.2
  have hB := aemeasurable_of_twoSidedConditioned hData.1
  have hZ := hData.2.1.2.2.2.1
  have hfin := hData.2.1.2.2.2.2.1
  have hg : AEMeasurable g (μ.prod P) :=
    ((measurable_fst.const_mul γ).exp.ennreal_ofReal).aemeasurable.mul
      (actual_cut_mass_joint_aemeasurable P μ γ B Z hB hZ hfin)
  have hmass : AEMeasurable mass P := localSingularMass_aemeasurable P
    (translatedField X Xc z) (translated_field_isEquatorGFF P X Xc hX hc z)
    γ hγ hγ2 N hN (fun _ => 1) measurable_const 0 α
  have hl := translated_canonical_source_williams_law P X Xc hX hc hm hcont
    z γ α hγ hγ2 hα N hN B Z hData
  have hprod := independent_product_law P (μ.prod P) mass g S hmass hg hS hl
  let F := fun q : ℝ × (Ω × Ω) => (S q.2.2*twoSidedReflectionCutMass γ q.1 B Z q.2.1)*
    ENNReal.ofReal (Real.exp (γ*q.1))
  have hProj := (measurePreserving_fst (μ := P) (ν := P)).comp
    (measurePreserving_snd (μ := μ) (ν := P.prod P))
  have hInp : AEMeasurable (fun q : ℝ × (Ω × Ω) => (q.1,(B q.2.1,Z q.2.1)))
      (μ.prod (P.prod P)) := measurable_fst.aemeasurable.prodMk
    ((hB.prodMk hZ).comp_quasiMeasurePreserving hProj.quasiMeasurePreserving)
  have hCut : AEMeasurable (fun q : ℝ × (Ω × Ω) =>
      twoSidedReflectionCutMass γ q.1 B Z q.2.1) (μ.prod (P.prod P)) := by
    have h := (measurable_williamsCutMassCode γ).comp_aemeasurable hInp
    apply h.congr
    filter_upwards [hProj.quasiMeasurePreserving.ae hfin] with q hq
    exact williamsCutMassCode_eq γ q.1 (B q.2.1) (Z q.2.1) hq
  have hPin := hS.comp_quasiMeasurePreserving
    ((measurePreserving_snd (μ := P) (ν := P)).comp
      (measurePreserving_snd (μ := μ) (ν := P.prod P))).quasiMeasurePreserving
  have hF : AEMeasurable F (μ.prod (P.prod P)) :=
    (hPin.mul hCut).mul ((measurable_fst.const_mul γ).exp.ennreal_ofReal).aemeasurable
  have hT := measurePreserving_prodAssoc μ P P
  have hF' : AEMeasurable F (((μ.prod P).prod P).map MeasurableEquiv.prodAssoc) := by
    rw [hT.map_eq]
    exact hF
  change (P.prod P).map (fun q => S q.2*mass q.1) = (μ.prod (P.prod P)).map F
  rw [← hT.map_eq,AEMeasurable.map_map_of_aemeasurable hF' hT.aemeasurable]
  convert hprod using 1
  congr 1
  funext q
  change (S q.2*twoSidedReflectionCutMass γ q.1.1 B Z q.1.2)*
    ENNReal.ofReal (Real.exp (γ*q.1.1)) = S q.2*
      (ENNReal.ofReal (Real.exp (γ*q.1.1))*twoSidedReflectionCutMass γ q.1.1 B Z q.1.2)
  ac_rfl


end DOZZ.Proofs

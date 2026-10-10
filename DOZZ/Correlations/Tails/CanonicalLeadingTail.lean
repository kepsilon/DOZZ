/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.SourceWilliamsUniformTail

/-! The uniform Williams estimate for the actual independently prefactored canonical mass. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

theorem canonical_leading_tail_uniform
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (Kz : Set ℂ) (hKz : IsCompact Kz) (hz : ∀ z ∈ Kz, 2 ≤ ‖z‖)
    (Kα : Set ℝ) (hKα : IsCompact Kα) (hα : ∀ α ∈ Kα, γ/2 < α ∧ α < Q γ)
    (B : ℝ → Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hZ : IsLateralGMCOf P γ Z) (hData : ∀ α ∈ Kα, IsReflectionData P γ α (B α) Z)
    (b R η a : ℝ) (hb : 0 ≤ b) (hR : 0 < R) (hRbulk : R < 4/γ^2)
    (hη : 0 < η) (ha : η < a) (r : ℝ → ℝ)
    (hr : ∀ α ∈ Kα, 0 < r α ∧ r α ≤ R)
    (hpr : ∀ α ∈ Kα, reflectionExponent γ α+η < (1-a)*r α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Kz, ∀ α ∈ Kα, ∀ f : ℝ, 0 < f → f ≤ b →
      ∀ N : Ω → Measure ℂ, IsGMCOf P (translatedField X Xc z) γ N →
      ∀ x : ℝ, 1 ≤ x →
      |((P.prod P) {q | ENNReal.ofReal x <
          ENNReal.ofReal (f*‖z‖^(-4 : ℝ)*Real.exp (γ*Xc q.2 z 0-γ^2*Real.log ‖z‖))*
            localSingularMass N (fun _ => 1) 0 γ α q.1}).toReal -
          oneInsertionTailCoefficient γ α z f (reflectionBarR P γ α (B α) Z)*
            x^(-reflectionExponent γ α)| ≤ C*x^(-reflectionExponent γ α-η) := by
  let : IsProbabilityMeasure P := hX.1
  obtain ⟨C,hC,hbound⟩ := source_williams_tail_uniform P X Xc hX hc γ hγ hγ2
    Kz hKz hz Kα hKα hα B Z hZ hData b R η a hb hR hRbulk hη ha r hr hpr
  refine ⟨C,hC,?_⟩
  intro z hzk α hαk f hf hfb N hN x hx
  let S : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal (f*‖z‖^(-4 : ℝ)*Real.exp (γ*Xc ω z 0-γ^2*Real.log ‖z‖))
  have hS : Measurable S := by
    have hpin := (hc.1 0).comp (measurable_id.prodMk (measurable_const : Measurable (fun _ : Ω => z)))
    exact ((((hpin.const_mul γ).sub_const _).exp).const_mul _).ennreal_ofReal
  let μ := brownianMaximumReferenceLaw (Q γ-α)
  let : IsProbabilityMeasure μ := isProbabilityMeasure_brownianMaximumReferenceLaw
    (sub_pos.mpr (hα α hαk).2)
  have hLaw := prefactored_canonical_source_williams_law P X Xc hX hc hm hcont
    z γ α hγ hγ2 (hα α hαk).2 N hN (B α) Z (hData α hαk) S hS.aemeasurable
  have hMass := localSingularMass_aemeasurable P (translatedField X Xc z)
    (translated_field_isEquatorGFF P X Xc hX hc z) γ hγ hγ2 N hN
    (fun _ => 1) measurable_const 0 α
  have hLead := (hS.comp measurable_snd).aemeasurable.mul
    (hMass.comp_quasiMeasurePreserving (measurePreserving_fst (μ := P) (ν := P)).quasiMeasurePreserving)
  change AEMeasurable (fun q : Ω × Ω => S q.2*localSingularMass N (fun _ => 1) 0 γ α q.1) (P.prod P) at hLead
  have hModel := prefactored_source_williams_mass_aemeasurable P μ γ (B α) Z
    (aemeasurable_of_twoSidedConditioned (hData α hαk).1)
    (hData α hαk).2.1.2.2.2.1 (hData α hαk).2.1.2.2.2.2.1 S hS.aemeasurable
  have hTail := congrArg (fun ν : Measure ℝ≥0∞ => ν (Ioi (ENNReal.ofReal x))) hLaw
  rw [Measure.map_apply_of_aemeasurable hLead measurableSet_Ioi,
    Measure.map_apply_of_aemeasurable hModel measurableSet_Ioi] at hTail
  change (P.prod P) {q | ENNReal.ofReal x < S q.2*localSingularMass N (fun _ => 1) 0 γ α q.1} =
    (μ.prod (P.prod P)) {q | ENNReal.ofReal x <
      (S q.2.2*twoSidedReflectionCutMass γ q.1 (B α) Z q.2.1)*
        ENNReal.ofReal (Real.exp (γ*q.1))} at hTail
  change |((P.prod P) {q | ENNReal.ofReal x < S q.2*localSingularMass N (fun _ => 1) 0 γ α q.1}).toReal -
    oneInsertionTailCoefficient γ α z f (reflectionBarR P γ α (B α) Z)*
      x^(-reflectionExponent γ α)| ≤ C*x^(-reflectionExponent γ α-η)
  rw [hTail]
  exact hbound z hzk α hαk f hf hfb x hx


end DOZZ.Proofs

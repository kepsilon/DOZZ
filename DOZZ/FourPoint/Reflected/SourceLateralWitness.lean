/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Statements.Brownian.EquatorGFFLateralGMCDecomposition
public import DOZZ.Brownian.Lateral.ReflectionJointLaw
public import DOZZ.ShiftEquations.Reflection.Witness
/-! A regular circle witness usable by both conditional spatial comparison and Williams' law. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The supplied field and chaos have one regular circle witness whose literal origin path
and literal projection provide the full lateral GMC interface. -/
theorem reflected_source_lateral_witness
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) :
    ∃ Xc : Ω → ℂ → ℝ → ℝ,
      IsCircleAverage P X Xc ∧
      Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2) ∧
      (∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2)) ∧
      IsSourceLateralProjection P X γ M
        (fun ω => lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)) ∧
      IsLateralGMCOf P γ (fun ω => lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)) := by
  obtain ⟨Xc, hc, hm, hcont, hSource, hfin⟩ :=
    equatorGFF_exists_sourceLateralProjection P X hX γ hγ hγ₂ M hM
  have hA := originRadialPath_aemeasurable P X Xc hc hcont
  have hZ := lateralProjectedGMC_aemeasurable P γ (originRadialPath Xc) hA M
    (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ₂ M hM) hM.1
  refine ⟨Xc, hc, hm, hcont, hSource, hγ, hγ₂, hX.1, hZ, hfin, ?_, ?_, ?_, ⟨X,M,hSource⟩⟩
  · exact fun t => lateralProjectedGMC_translation_law P X Xc hX hc hm hcont γ hγ hγ₂ M hM t
  · exact lateralProjectedGMC_reflection_law P X Xc hX hc hcont γ hγ hγ₂ M hM
  · exact fun a b _ => lateralProjectedGMC_interval_intensity P X Xc hX hc hm hcont γ hγ hγ₂ M hM a b

/-- One regular source circle witness and its literal lateral measure support the entire
reflection family on the supplied probability space, before choosing the fusion parameter. -/
theorem reflected_regular_source_reflection_family
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) :
    ∃ Xc : Ω → ℂ → ℝ → ℝ, ∃ B : ℝ → Ω → BrownianPath × BrownianPath,
      IsCircleAverage P X Xc ∧
      Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2) ∧
      (∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2)) ∧
      IsSourceLateralProjection P X γ M
        (fun ω => lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)) ∧
      IsLateralGMCOf P γ (fun ω => lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)) ∧
      ∀ α : ℝ, α < Q γ → IsReflectionData P γ α (B α)
        (fun ω => lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)) := by
  obtain ⟨Xc, hc, hm, hcont, hSource, hL⟩ :=
    reflected_source_lateral_witness P X hX γ hγ hγ₂ M hM
  obtain ⟨B,hB⟩ := exists_reflectionData_family P X γ M _ hSource hL
  exact ⟨Xc,B,hc,hm,hcont,hSource,hL,hB⟩

end DOZZ.Proofs

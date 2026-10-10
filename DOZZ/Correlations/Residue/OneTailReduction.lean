/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Residue.FullSourceTailReduction
public import DOZZ.Correlations.SumTail.Reduction

/-! The joint-tail inequality `DOZZ.separatedSingularMass_joint_tail` and the two-insertion tail
`DOZZ.twoInsertion_tail_sum_uniform` supply the two-insertion hypothesis in both complete
residue-bridge reductions. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology
namespace DOZZ.Proofs

/-- The unit-volume residue bridge on its full domain (erratum K30, see
docs/ERRATA-AND-DEVIATIONS.md), with its literal one-insertion input as the only remaining tail
premise. -/
theorem residue_unitVolume_bridge_of_oneInsertion_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ α2 α3 : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : 0 < α2 ∧ α2 ≤ α3 ∧ γ / 2 < α3 ∧ α3 < Q γ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hone : ∀
    (Kz : Set ℂ) (_hKz : IsCompact Kz) (_hz : ∀ z ∈ Kz, 2 ≤ ‖z‖)
    (Kα : Set ℝ) (_hKα : IsCompact Kα)
    (_hα : ∀ α ∈ Kα, γ / 2 < α ∧ α < Q γ)
    (Family : ℂ → Set (ℂ → ℝ)) (radius supBound derivBound lowerBound : ℝ)
    (_hFamily : UniformPositiveC1Family Kz Family radius supBound derivBound lowerBound),
    ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
      IsSourceLateralProjection P X γ M Z ∧
        (∀ α ∈ Kα, IsReflectionData P γ α (B α) Z) ∧
        ∀ η : ℝ, 0 < η → (∀ α ∈ Kα, η < oneInsertionErrorCeiling γ α) →
          ∃ C : ℝ, 0 ≤ C ∧
            ∀ z ∈ Kz, ∀ α ∈ Kα, ∀ F ∈ Family z, ∀ x : ℝ, 1 ≤ x →
              |(P {ω | ENNReal.ofReal x < localSingularMass M F z γ α ω}).toReal -
                oneInsertionTailCoefficient γ α z (F z) (reflectionBarR P γ α (B α) Z) *
                  Real.rpow x (-reflectionExponent γ α)| ≤
                C * Real.rpow x (-reflectionExponent γ α - η) ) :
    ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
      IsSourceLateralProjection P X γ M Z ∧ IsReflectionData P γ α3 (B α3) Z ∧
      Tendsto (fun ε : ℝ => ε * unitVolumeStructureConstant P M γ
          (α3 - α2 + ε) α2 α3) (𝓝[>] 0)
        (𝓝 (bridgeMultiplicity α2 α3 * reflectionExponent γ α3 *
          reflectionBarR P γ α3 (B α3) Z)) := by
  apply residue_unitVolume_bridge_of_insertion_tails P X M γ α2 α3 hγ hγ2 hα hX hM
  · exact hone
  · intro K2 K3 hK2 hK3 hpos2 hpos3 hsep A2 A3 hA2 hA3 hα2 hα3
      F2s F3s radius supBound derivBound lowerBound hF2 hF3
    exact sumtail_twoInsertion_tail_sum_uniform_of_oneInsertion_tail P X M γ hγ hγ2 hX hM
      K2 K3 hK2 hK3 hpos2 hpos3 hsep A2 A3 hA2 hA3 hα2 hα3
      F2s F3s radius supBound derivBound lowerBound hF2 hF3 hone

/-- The residue bridge for the full structure constant on its full domain (erratum K30, see
docs/ERRATA-AND-DEVIATIONS.md), with its literal one-insertion input as the only remaining tail
premise. -/
theorem residue_structureConstant_bridge_of_oneInsertion_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ α2 α3 : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hα : 0 < α2 ∧ α2 ≤ α3 ∧ γ / 2 < α3 ∧ α3 < Q γ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hPole : ReflectionPoleFree γ α3)
    (hone : ∀
    (Kz : Set ℂ) (_hKz : IsCompact Kz) (_hz : ∀ z ∈ Kz, 2 ≤ ‖z‖)
    (Kα : Set ℝ) (_hKα : IsCompact Kα)
    (_hα : ∀ α ∈ Kα, γ / 2 < α ∧ α < Q γ)
    (Family : ℂ → Set (ℂ → ℝ)) (radius supBound derivBound lowerBound : ℝ)
    (_hFamily : UniformPositiveC1Family Kz Family radius supBound derivBound lowerBound),
    ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
      IsSourceLateralProjection P X γ M Z ∧
        (∀ α ∈ Kα, IsReflectionData P γ α (B α) Z) ∧
        ∀ η : ℝ, 0 < η → (∀ α ∈ Kα, η < oneInsertionErrorCeiling γ α) →
          ∃ C : ℝ, 0 ≤ C ∧
            ∀ z ∈ Kz, ∀ α ∈ Kα, ∀ F ∈ Family z, ∀ x : ℝ, 1 ≤ x →
              |(P {ω | ENNReal.ofReal x < localSingularMass M F z γ α ω}).toReal -
                oneInsertionTailCoefficient γ α z (F z) (reflectionBarR P γ α (B α) Z) *
                  Real.rpow x (-reflectionExponent γ α)| ≤
                C * Real.rpow x (-reflectionExponent γ α - η) ) :
    ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
      IsSourceLateralProjection P X γ M Z ∧ IsReflectionData P γ α3 (B α3) Z ∧
      Tendsto (fun ε : ℝ => ε * structureConstant P M γ μ (α3 - α2 + ε) α2 α3)
        (𝓝[>] 0)
        (𝓝 (bridgeMultiplicity α2 α3 * reflectionR P γ μ α3 (B α3) Z)) := by
  apply residue_structureConstant_bridge_of_insertion_tails P X M γ μ α2 α3 hγ hγ2 hμ hα hX hM hPole
  · exact hone
  · intro K2 K3 hK2 hK3 hpos2 hpos3 hsep A2 A3 hA2 hA3 hα2 hα3
      F2s F3s radius supBound derivBound lowerBound hF2 hF3
    exact sumtail_twoInsertion_tail_sum_uniform_of_oneInsertion_tail P X M γ hγ hγ2 hX hM
      K2 K3 hK2 hK3 hpos2 hpos3 hsep A2 A3 hA2 hA3 hα2 hα3
      F2s F3s radius supBound derivBound lowerBound hF2 hF3 hone

end DOZZ.Proofs

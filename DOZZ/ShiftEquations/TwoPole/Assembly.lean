/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.TwoPole.Expansion
import DOZZ.Correlations.SumTail.Assembly

/-!
# Proof of `structureConstant_two_pole_expansion`

The two-pole expansion from the two-insertion tail `twoInsertion_tail_sum_uniform`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- The two-pole expansion, from `structureConstant_two_pole_expansion_of_tail` and
`twoInsertion_tail_sum_uniform`. -/
theorem structureConstant_two_pole_expansion
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ η δ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hX : IsEquatorGFF P X)
    (hM : IsGMCOf P X γ M)
    (hWindow : TwoPoleWindow γ η δ) :
    ∃ B : ℝ → Ω → BrownianPath ×
        BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          IsReflectionData P γ (2 / γ + η)
            (B (2 / γ + η)) Z ∧
          IsReflectionData P γ (Q γ - η - γ / 2)
            (B (Q γ - η - γ / 2)) Z ∧
            ∃ V : Set ℂ, IsOpen V ∧
              (∀ x : ℝ, -2 * η - δ < x ∧ x < 1 / γ → (x : ℂ) ∈ V) ∧
              ∃ F r : ℂ → ℂ,
                MeromorphicOn F V ∧ DifferentiableOn ℂ r V ∧
                (∀ x : ℝ, 2 * η < x ∧ x < 1 / γ →
                  F (x : ℂ) =
                    (unitVolumeStructureConstant P M γ (Q γ - η - γ / 2) x
                      (2 / γ + η) : ℂ)) ∧
                ∀ᶠ z in codiscrete ℂ, z ∈ V →
                  F z =
                    (twoPoleFirstResidue P γ B Z η : ℂ) / (z - 2 * η) +
                    (twoPoleSecondResidue P γ B Z η : ℂ) / (z + 2 * η) + r z := by
  exact structureConstant_two_pole_expansion_of_tail P X M γ η δ hγ hγ2 hX hM hWindow
    (fun K2 K3 hK2 hK3 hpos2 hpos3 hsep A2 A3 hA2 hA3 hα2 hα3 F2s F3s radius supBound
        derivBound lowerBound hF2 hF3 =>
      twoInsertion_tail_sum_uniform P X M γ hγ hγ2 hX hM K2 K3 hK2 hK3 hpos2 hpos3 hsep A2 A3
        hA2 hA3 hα2 hα3 F2s F3s radius supBound derivBound lowerBound hF2 hF3)

end DOZZ.Proofs

end

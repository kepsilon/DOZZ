/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Shift.Wrappers
public import DOZZ.FourPoint.Crossing.GammaHalfCrossing

/-! Proof of `DOZZ.reflectionBarR_holomorphic_representation` from the unit-volume conjunct of the
γ/2 crossing `DOZZ.gammaHalf_crossing`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

theorem reflectionBarR_holomorphic_representation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (I : Set ℝ) (hIcompact : IsCompact I)
    (hI : ∀ α ∈ I, γ / 2 < α ∧ α < Q γ) :
    ∃ B : ℝ → Ω → BrownianPath ×
        BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α ∈ I,
            IsReflectionData P γ α (B α) Z) ∧
            ∃ V : Set ℂ, IsOpen V ∧
              (∀ α ∈ I, (α : ℂ) ∈ V) ∧
              ∃ f : ℂ → ℂ, DifferentiableOn ℂ f V ∧
                (∀ α ∈ I,
                  f (α : ℂ) =
                    (unitVolumeStructureConstant P M γ α γ α : ℂ)) ∧
                DifferentiableOn ℂ
                  (fun z => rbarCoefficient γ z * f z) V ∧
                (∀ α ∈ I,
                  rbarCoefficient γ (α : ℂ) * f (α : ℂ) =
                    (reflectionBarR P γ α (B α) Z : ℂ)) := by
  have _hc := hIcompact
  exact reflectionBarR_holomorphic_representation_of_crossing P X M γ hγ hγ2 hX hM
    (fun μ' α' ε α hμ' h1 h2 h3 h4 h5 =>
      (gammaHalf_crossing P X M γ μ' α' ε α hγ hγ2 hμ' h1 h2 h3 h4 h5 hX hM).2) I hI

end DOZZ.Proofs

end

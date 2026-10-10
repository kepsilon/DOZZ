/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Correlations.BridgeMultiplicity
import DOZZ.Correlations.Analytic.StructureConstantHolomorphic

/-! The statement `DOZZ.unitVolumeStructureConstant_holomorphic_near_extended_domain`,
proved by `DOZZ.Proofs.unitVolumeStructureConstant_holomorphic_near_extended_domain`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- Holomorphic extension of the unit-volume structure constant in the canonical frame, on a
neighborhood of `U₃`. -/
theorem unitVolumeStructureConstant_holomorphic_near_extended_domain
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∃ V : Set (Fin 3 → ℂ), IsOpen V ∧
      (∀ α : Fin 3 → ℝ, ExtendedSeiberg3 γ (α 0) (α 1) (α 2) → complexifyNCharges α ∈ V) ∧
      ∃ f : (Fin 3 → ℂ) → ℂ, DifferentiableOn ℂ f V ∧
        ∀ α : Fin 3 → ℝ, ExtendedSeiberg3 γ (α 0) (α 1) (α 2) →
          f (complexifyNCharges α) =
            (unitVolumeStructureConstant P M γ (α 0) (α 1) (α 2) : ℂ) := by exact DOZZ.Proofs.unitVolumeStructureConstant_holomorphic_near_extended_domain P X M γ hγ hγ2 hX hM

end DOZZ

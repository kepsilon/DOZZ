/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Correlations.BridgeMultiplicity
import DOZZ.Correlations.Symmetry.SymmetricExtended

/-! The statement `DOZZ.unitVolumeStructureConstant_symmetric_extended`,
proved by `DOZZ.Proofs.unitVolumeStructureConstant_symmetric_extended`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- Extended-domain permutation symmetry, required where the three-to-two residue bridge
(`DOZZ.structureConstant_threeToTwo_residue_bridge`,
`DOZZ.unitVolumeStructureConstant_threeToTwo_residue_bridge`) is used in the second slot. -/
theorem unitVolumeStructureConstant_symmetric_extended
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hα : ExtendedSeiberg3 γ α₁ α₂ α₃) :
    unitVolumeStructureConstant P M γ α₁ α₂ α₃ = unitVolumeStructureConstant P M γ α₂ α₁ α₃ ∧
      unitVolumeStructureConstant P M γ α₁ α₂ α₃ = unitVolumeStructureConstant P M γ α₁ α₃ α₂ ∧
      unitVolumeStructureConstant P M γ α₁ α₂ α₃ = unitVolumeStructureConstant P M γ α₃ α₂ α₁ := by exact DOZZ.Proofs.unitVolumeStructureConstant_symmetric_extended P X M γ α₁ α₂ α₃ hγ hγ2 hX hM hα

end DOZZ

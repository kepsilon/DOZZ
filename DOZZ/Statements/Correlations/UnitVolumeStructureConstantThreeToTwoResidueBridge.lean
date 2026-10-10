/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Correlations.BridgeMultiplicity
import DOZZ.Correlations.Residue.Assembly

/-! The statement `DOZZ.unitVolumeStructureConstant_threeToTwo_residue_bridge`,
proved by `DOZZ.Proofs.unitVolumeStructureConstant_threeToTwo_residue_bridge`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- Pole-free unit-volume form of the three-to-two residue bridge
`DOZZ.structureConstant_threeToTwo_residue_bridge` ([KRV, Remark 8.2]), on the same extended domain
(erratum K30, see docs/ERRATA-AND-DEVIATIONS.md). -/
theorem unitVolumeStructureConstant_threeToTwo_residue_bridge
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ α2 α3 : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : 0 < α2 ∧ α2 ≤ α3 ∧ γ / 2 < α3 ∧ α3 < Q γ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
      IsSourceLateralProjection P X γ M Z ∧ IsReflectionData P γ α3 (B α3) Z ∧
      Tendsto (fun ε : ℝ => ε * unitVolumeStructureConstant P M γ
          (α3 - α2 + ε) α2 α3) (𝓝[>] 0)
        (𝓝 (bridgeMultiplicity α2 α3 * reflectionExponent γ α3 *
          reflectionBarR P γ α3 (B α3) Z)) := by exact DOZZ.Proofs.unitVolumeStructureConstant_threeToTwo_residue_bridge P X M γ α2 α3 hγ hγ2 hα hX hM

end DOZZ

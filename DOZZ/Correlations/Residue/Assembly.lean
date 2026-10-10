/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Residue.OneTailReduction
import DOZZ.Statements.Correlations.OneInsertionTailUniform

/-! Both three-to-two residue bridges, `DOZZ.structureConstant_threeToTwo_residue_bridge`
([KRV, Proposition 8.1]) and `DOZZ.unitVolumeStructureConstant_threeToTwo_residue_bridge`
([KRV, Remark 8.2]), on their full domain (erratum K30, see docs/ERRATA-AND-DEVIATIONS.md). -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology
namespace DOZZ.Proofs

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
          reflectionBarR P γ α3 (B α3) Z)) := by
  exact residue_unitVolume_bridge_of_oneInsertion_tail P X M γ α2 α3 hγ hγ2 hα hX hM
    (DOZZ.oneInsertion_tail_uniform P X M γ hγ hγ2 hX hM)

theorem structureConstant_threeToTwo_residue_bridge
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ α2 α3 : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hα : 0 < α2 ∧ α2 ≤ α3 ∧ γ / 2 < α3 ∧ α3 < Q γ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hPole : ReflectionPoleFree γ α3) :
    ∃ B : ℝ → Ω → BrownianPath × BrownianPath, ∃ Z : Ω → Measure ℝ,
      IsSourceLateralProjection P X γ M Z ∧ IsReflectionData P γ α3 (B α3) Z ∧
      Tendsto (fun ε : ℝ => ε * structureConstant P M γ μ (α3 - α2 + ε) α2 α3)
        (𝓝[>] 0)
        (𝓝 (bridgeMultiplicity α2 α3 * reflectionR P γ μ α3 (B α3) Z)) := by
  exact residue_structureConstant_bridge_of_oneInsertion_tail P X M γ μ α2 α3
    hγ hγ2 hμ hα hX hM hPole
    (DOZZ.oneInsertion_tail_uniform P X M γ hγ hγ2 hX hM)

end DOZZ.Proofs

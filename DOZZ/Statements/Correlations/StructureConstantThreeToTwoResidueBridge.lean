/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Correlations.BridgeMultiplicity
import DOZZ.Correlations.Residue.Assembly

/-! The statement `DOZZ.structureConstant_threeToTwo_residue_bridge`,
proved by `DOZZ.Proofs.structureConstant_threeToTwo_residue_bridge`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- Full-volume three-to-two residue bridge [KRV, Proposition 8.1]: the unequal-charge residue is
2R; the equal-charge residue is 4R. The domain is `0 < α₂ ≤ α₃` with `γ/2 < α₃ < Q`, as needed for
its use in [KRV] (erratum K30, see docs/ERRATA-AND-DEVIATIONS.md). -/
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
        (𝓝 (bridgeMultiplicity α2 α3 * reflectionR P γ μ α3 (B α3) Z)) := by exact DOZZ.Proofs.structureConstant_threeToTwo_residue_bridge P X M γ μ α2 α3 hγ hγ2 hμ hα hX hM hPole

end DOZZ

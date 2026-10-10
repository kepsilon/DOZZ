/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.SeedOne.Reduction
public import DOZZ.FourPoint.Dual.FullFusion

/-! Proof of `dual_crossing_seed_one`: the dual-fusion reduction applied to
`dual_full_fusion_and_asymptotic`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

theorem dual_crossing_seed_one {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (X : Ω → Distr)
    (γ μ α ε α' : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hμ : 0 < μ)
    (hα : α < Q γ) (hε : ε < Q γ) (hα' : α' < Q γ)
    (hs : 2 * Q γ + 2 / γ < α + ε + α')
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∃ Bε : Ω → BrownianPath × BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
        IsReflectionData P γ ε Bε Z ∧
        structureConstant P M γ μ (α - 2 / γ) ε α' =
          dualCrossingMultiplier γ α' α ε *
            reflectionR P γ μ ε Bε Z *
              structureConstant P M γ μ α (2 * Q γ - ε - 2 / γ) α' := by
  exact dual_crossing_seed_one_of_fusion P M X γ μ α ε α' hγ hγ₂ hμ hα hε hα' hs hX hM
    (fun hH P M X γ μ α₁ α₂ α₃ η ξ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 hX hM =>
      dual_full_fusion_and_asymptotic hH P M X γ μ α₁ α₂ α₃ η ξ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
        h12 h13 h14 hX hM)

end DOZZ.Proofs

end

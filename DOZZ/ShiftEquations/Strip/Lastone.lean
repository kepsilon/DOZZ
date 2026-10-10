/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Strip.CoulombLimit

/-! The `lastone` structure-constant limit ([KRV, Lemma 10.6]), assembled from the supplied-space
Williams mass limit, GMC moment comparison, root symmetry, and the Gamma pole normalization. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- The limit `-4` of [KRV, Lemma 10.6], with the target charge order and sign of erratum K7 (see
docs/ERRATA-AND-DEVIATIONS.md). -/
theorem structureConstant_lastone_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ ε : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hε : 0 < ε ∧ ε < min (Q γ) (2 / γ))
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    Tendsto (fun δ : ℝ =>
      δ * structureConstant P M γ μ ε (Q γ - δ) (Q γ - ε))
      (𝓝[>] 0) (𝓝 (-4)) := by
  apply lastone_structureConstant_limit_of_moment P M γ μ ε hγ hμ
  exact lastone_rho_smallPower_limit P X M γ ε hγ hγ2
    ⟨hε.1, hε.2.trans_le (min_le_left _ _)⟩ hX hM

end DOZZ.Proofs

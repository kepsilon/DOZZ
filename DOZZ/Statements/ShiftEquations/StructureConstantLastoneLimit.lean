/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.ShiftEquations.TwoPoleWindow
import DOZZ.ShiftEquations.Strip.Lastone

/-! The statement `DOZZ.structureConstant_lastone_limit`,
proved by `DOZZ.Proofs.structureConstant_lastone_limit`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

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
      (𝓝[>] 0) (𝓝 (-4)) := by exact DOZZ.Proofs.structureConstant_lastone_limit P X M γ μ ε hγ hγ2 hμ hε hX hM

end DOZZ

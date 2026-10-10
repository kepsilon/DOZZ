/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.DualCrossingL
import DOZZ.ShiftEquations.Shifts.Assembly.SeedTwo

/-! The statement `DOZZ.dual_crossing_seed_two`, proved by `DOZZ.Proofs.dual_crossing_seed_two`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The second dual crossing relation [KRV, Proposition 9.10], on its full domain, with separate
conditioned path data for the two reflection drifts and one lateral projection. -/
theorem dual_crossing_seed_two {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (X : Ω → Distr)
    (γ μ α ε α' : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hμ : 0 < μ)
    (hα : α < Q γ) (hε : ε < Q γ) (hα' : α' < Q γ)
    (hs : 2 * Q γ + 2 / γ < α + ε + α')
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∃ Bε Bα : Ω → BrownianPath × BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
        IsReflectionData P γ ε Bε Z ∧
        IsReflectionData P γ α Bα Z ∧
        reflectionR P γ μ ε Bε Z *
            structureConstant P M γ μ (2 * Q γ - ε - 2 / γ) α α' =
          dualCrossingL γ ε α α' *
            reflectionR P γ μ α Bα Z *
              structureConstant P M γ μ ε (2 * Q γ - α - 2 / γ) α' := by exact DOZZ.Proofs.dual_crossing_seed_two P M X γ μ α ε α' hγ hγ₂ hμ hα hε hα' hs hX hM

end DOZZ

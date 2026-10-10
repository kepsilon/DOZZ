/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.ShiftEquations.TwoPoleSecondResidue

/-! The definition `DOZZ.TwoPoleWindow`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- An admissible eta-window for [KRV, Proposition 10.1]. These bounds put both charges in the
physical reflection interval, leave the next possible pole below `-2η`, and keep the remainder
exponent of `DOZZ.structureConstant_two_pole_expansion` below the two-insertion tail ceiling
`twoInsertionTailCeiling`. -/
def TwoPoleWindow (γ η δ : ℝ) : Prop :=
  0 < η ∧ η < min (2 / γ - γ / 2) (min (γ / 4) (1 / (2 * γ))) ∧
    0 < δ ∧ 2 * η + δ < 4 / γ - γ ∧ 4 * η + δ < γ ∧
      1 + (2 * η + δ) / γ <
        twoInsertionTailCeiling γ (2 / γ + η) (Q γ - η - γ / 2)

end DOZZ

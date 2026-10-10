/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.ShiftEquations.PoleSubtractedCutoff

/-! The definition `DOZZ.poleSubtractedObservable`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The real restriction of the pole-subtracted observable in [KRV, Lemma 10.3]. On the two unit
balls the epsilon-dependent factor cancels because `|x|_+ = |x|`; this is the actual local
subtraction used by the proof. -/
noncomputable def poleSubtractedObservable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (γ η ε : ℝ) : ℝ :=
  ∫ ω,
    (poleTotalMass γ ε (2 / γ + η) (2 / γ - η) (M ω)).toReal ^
        (1 - ε / γ) -
      (poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω)).toReal ^
        (1 - ε / γ) ∂P

end DOZZ

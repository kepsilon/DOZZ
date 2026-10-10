/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.ShiftEquations.PoleCutoffBaseMass

/-! The definition `DOZZ.poleSubtractedCutoff`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The limit-chaos analytic family `F_t` from [KRV, Lemma 10.3]: only the spatial domain is cut
off; the circle average supplies its Gaussian tilt and variance correction. -/
noncomputable def poleSubtractedCutoff {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Xc : Ω → ℂ → ℝ → ℝ) (M : Ω → Measure ℂ)
    (γ η : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  ∫ ω, Complex.exp (z * (Xc ω 0 n : ℂ) - (n : ℂ) * z ^ 2 / 2) *
    (((poleCutoffBaseMass M γ η n ω).toReal : ℂ) ^
        (1 - z / γ) -
      ((poleLocalMass γ (2 / γ + η) (2 / γ - η) (M ω)).toReal : ℂ) ^
        (1 - z / γ)) ∂P

end DOZZ

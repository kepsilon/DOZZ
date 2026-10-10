/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.GammaHalfOuterMass

/-! The definition `DOZZ.gammaHalfOuterMoment`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The negative moment of the outer mass. -/
noncomputable def gammaHalfOuterMoment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ p : ℝ)
    (z : ℂ) (ξ : ℝ) : ℝ :=
  (∫⁻ ω, ENNReal.rpow
    (gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ) (-p) ∂P).toReal

end DOZZ

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.GammaHalfKernel

/-! The definition `DOZZ.gammaHalfMoment`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The negative p moment of the literal gamma/2 kernel mass. -/
noncomputable def gammaHalfMoment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ : ℝ)
    (p : ℝ) (z : ℂ) : ℝ :=
  (∫⁻ ω, ENNReal.rpow
    (coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃) (-p) ∂P).toReal

end DOZZ

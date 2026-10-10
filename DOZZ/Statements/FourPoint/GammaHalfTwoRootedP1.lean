/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.GammaHalfRootKernelBar

/-! The definition `DOZZ.gammaHalfTwoRootedP1`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The two-rooted z-z contribution p1. -/
noncomputable def gammaHalfTwoRootedP1 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ p : ℝ) (z : ℂ) : ℂ :=
  ((p * (p + 1) * (γ ^ 2 / 4) ^ 2 : ℝ) : ℂ) * z ^ 2 *
    (∫ t in Set.Icc (0 : ℝ) 1, (1 - t : ℝ) *
      (∫ ω, ((ENNReal.rpow
        (coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![t * z, 0, 1] α₃)
        (-p - 2)).toReal : ℂ) *
        gammaHalfRootKernelZ M γ α₁ α₂ α₃ ω (t * z) ^ 2 ∂P) ∂volume)

end DOZZ

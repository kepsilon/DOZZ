/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.GammaHalfRootedR1

/-! The definition `DOZZ.gammaHalfRootedR2`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The one-rooted mixed z-zbar contribution r2. -/
noncomputable def gammaHalfRootedR2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ p : ℝ) (z : ℂ) : ℂ :=
  ((-2 * p * (γ ^ 2 / 4) ^ 2 : ℝ) : ℂ) * z * star z *
    (∫ t in Set.Icc (0 : ℝ) 1, (1 - t : ℝ) *
      (∫ ω, ((ENNReal.rpow
        (coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![t * z, 0, 1] α₃)
        (-p - 1)).toReal : ℂ) *
        (∫ x, ((gammaHalfKernel γ α₁ α₂ α₃ (t * z) x : ℂ) /
          (‖x - t * z‖ ^ 2)) ∂M ω) ∂P) ∂volume)

end DOZZ

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.GammaHalfMoment

/-! The definition `DOZZ.gammaHalfRootedMass`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The first-root covariance-shifted mass in the coefficient `A` of [KRV, Lemma 9.2]. -/
noncomputable def gammaHalfRootedMass {Ω : Type*}
    (γ α₁ α₂ α₃ : ℝ) (M : Ω → Measure ℂ) (ω : Ω) : ℝ≥0∞ :=
  coulombMass γ (gmcRootedMeasure γ 0 (M ω)) ![-γ / 2, α₁, α₂] ![0, 0, 1] α₃

end DOZZ

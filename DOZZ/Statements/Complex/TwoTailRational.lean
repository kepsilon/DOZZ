/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Complex.RealUpperTail

/-! The definition `DOZZ.twoTailRational`. -/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ

/-- The two subtracted terms of [KRV, Lemma 10.4]; c₁,c₂ > 0 and β₁ < β₂ in the theorem. -/
noncomputable def twoTailRational (c₁ c₂ β₁ β₂ : ℝ) (s : ℂ) : ℂ :=
  (c₁ : ℂ) * s / ((β₁ : ℂ) - s) + (c₂ : ℂ) * s / ((β₂ : ℂ) - s)

end DOZZ

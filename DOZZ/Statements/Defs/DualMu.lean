/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.ShiftCoeffA

/-! The definition `DOZZ.dualMu`. -/

@[expose] public section

open Complex MeasureTheory Set Filter Topology

namespace DOZZ

/-- The dual cosmological constant `μ̃ = (μ π l(γ²/4))^{4/γ²} / (π l(4/γ²))` ([KRV, §1.2]). It
may be negative or singular; it is an algebraic coefficient, not a coupling. -/
noncomputable def dualMu (γ μ : ℝ) : ℂ :=
  ((dozzBase γ μ : ℝ) : ℂ) ^ ((4 / γ ^ 2 : ℝ) : ℂ) / (Real.pi * lFun ((4 / γ ^ 2 : ℝ) : ℂ))

end DOZZ

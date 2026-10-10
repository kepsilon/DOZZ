/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.ShiftEquations.MobiusChart

/-! The definition `DOZZ.mobiusMap`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

noncomputable def mobiusMap (ψ : MobiusChart) (z : ℂ) : ℂ :=
  (ψ.a * z + ψ.b) / (ψ.c * z + ψ.d)

end DOZZ

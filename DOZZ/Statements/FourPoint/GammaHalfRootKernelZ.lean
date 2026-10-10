/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.GammaHalfOneRootedTerm

/-! The definition `DOZZ.gammaHalfRootKernelZ`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The raw first-root kernel integral used in the two-rooted Taylor contribution. -/
noncomputable def gammaHalfRootKernelZ {Ω : Type*}
    (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ : ℝ) (ω : Ω) (z : ℂ) : ℂ :=
  ∫ x, ((gammaHalfKernel γ α₁ α₂ α₃ z x : ℂ) / (x - z)) ∂M ω

end DOZZ

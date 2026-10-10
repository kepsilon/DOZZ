/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.GammaHalfRootKernelZ

/-! The definition `DOZZ.gammaHalfRootKernelBar`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The raw conjugate-root kernel integral. -/
noncomputable def gammaHalfRootKernelBar {Ω : Type*}
    (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ : ℝ) (ω : Ω) (z : ℂ) : ℂ :=
  ∫ x, ((gammaHalfKernel γ α₁ α₂ α₃ z x : ℂ) / star (x - z)) ∂M ω

end DOZZ

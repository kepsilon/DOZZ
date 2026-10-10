/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.GmcReferenceMeasure

/-! The definition `DOZZ.gmcRootedMeasure`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- The rooted measure `e^{γ²G(u,·)}M(d·)` appearing in the rooted identity of
[KRV, Corollary 12.2]. -/
noncomputable def gmcRootedMeasure (γ : ℝ) (u : ℂ) (M : Measure ℂ) : Measure ℂ :=
  M.withDensity (fun x => ENNReal.ofReal (Real.exp (γ ^ 2 * gffKernel u x)))

end DOZZ

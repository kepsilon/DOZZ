/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.CircleMeasure

/-! The definition `DOZZ.circleCross`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Cross energy `∬ f(y) G(y,z) dy dσ_{x,r}(z)`. -/
noncomputable def circleCross (x : ℂ) (r : ℝ) (f : TestFn) : ℝ :=
  ∫ y, f y * ∫ z, gffKernel y z ∂circleMeasure x r

end DOZZ

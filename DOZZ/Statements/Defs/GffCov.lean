/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.Distr

/-! The definition `DOZZ.gffCov`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- The covariance form `∬ f(x) G(x,y) g(y) dx dy`. -/
noncomputable def gffCov (f g : TestFn) : ℝ := ∫ x, ∫ y, f x * gffKernel x y * g y

end DOZZ

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.GmcRootedMeasure

/-! The definition `DOZZ.gffRootCovariance`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- The covariance of a test evaluation with the point-root potential, `∫G(u,x)f(x)dx`.
See [KRV, Corollary 12.2]. -/
noncomputable def gffRootCovariance (u : ℂ) (f : TestFn) : ℝ :=
  ∫ x, gffKernel u x * f x ∂volume

end DOZZ

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.NormPlus

/-! The definition `DOZZ.gffKernel`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- The covariance kernel `G(x,y) = log(1/|x-y|) + log|x|_+ + log|y|_+` ([KRV, (hatGformula)]),
off the diagonal (the diagonal is Lebesgue-null and circle-measure-null wherever used). -/
noncomputable def gffKernel (x y : ℂ) : ℝ := -Real.log ‖x - y‖ + Real.log (normPlus x) + Real.log (normPlus y)

end DOZZ

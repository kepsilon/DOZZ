/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GFFStructure.EquatorRestorationScalar

/-! The definition `DOZZ.exteriorPinnedKernel`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

universe u

namespace DOZZ

/-- Exterior-pinned kernel, used for `R > 1`. -/
noncomputable def exteriorPinnedKernel (R : ℝ) (_hR : 0 < R) (x y : ℂ) : ℝ :=
  -Real.log ‖x - y‖ + Real.log (max ‖x‖ R) + Real.log (max ‖y‖ R) - Real.log R

end DOZZ

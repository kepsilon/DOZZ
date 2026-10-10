/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu

/-! The definition `DOZZ.normPlus`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- `|x|_+ = max(1, |x|)` (notation of [KRV, §2.1]). -/
noncomputable def normPlus (x : ℂ) : ℝ := max 1 ‖x‖

end DOZZ

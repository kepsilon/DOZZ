/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.FirstPassageTime

/-! The definition `DOZZ.negativeLastExitTime`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- Last exit time of a negative conditioned path from `-c`. It is measurable on the
continuous-path carrier; finiteness and attainment are conclusions under the conditioned law. -/
noncomputable def negativeLastExitTime (p : BrownianPath) (c : ℝ) : ℝ≥0 :=
  sSup {t | p t = -c}

end DOZZ

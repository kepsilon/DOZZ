/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.StopBrownianPath

/-! The definition `DOZZ.firstPassageTime`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- First passage time of the path `p` to the upper level `c`. -/
noncomputable def firstPassageTime (p : BrownianPath) (c : ℝ) : ℝ≥0 :=
  sInf {t | c ≤ p t}

end DOZZ

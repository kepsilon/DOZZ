/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitDyadicShift
public import DOZZ.Brownian.LastExitPostPathMeasurability
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Dominated convergence for dyadic post-last-exit shifts

For paths with a finite attained last visit, the dyadic shifts converge in continuous-path
topology to the recentered post-last-exit path. This module passes that pathwise limit through
bounded continuous tests and expectation. The probabilistic last-exit cell identity is a separate
input to the last-exit decomposition.
-/

@[expose] public section

open MeasureTheory Filter
open Topology
open scoped NNReal

namespace DOZZ.Proofs

/-- The dyadic ceiling map is measurable as a function of the last-exit time. -/
theorem measurable_dyadicLastExitCeilingTime (n : ℕ) :
    Measurable (dyadicLastExitCeilingTime n) := by
  unfold dyadicLastExitCeilingTime
  fun_prop

/-- The random dyadic shift at the last-exit time is measurable on continuous path space. -/
theorem measurable_dyadicShiftAtLastExit (c : ℝ) (n : ℕ) :
    Measurable (fun p : BrownianPath =>
      brownianShiftPath (dyadicLastExitCeilingTime n (negativeLastExitTime p c)) p) := by
  have hτ : Measurable (fun p : BrownianPath => negativeLastExitTime p c) :=
    measurable_negativeLastExitTime_joint.comp
      ((measurable_const (a := c)).prodMk measurable_id)
  exact continuous_brownianShiftPath.measurable.comp
    ((measurable_dyadicLastExitCeilingTime n).comp hτ |>.prodMk measurable_id)


end DOZZ.Proofs

end

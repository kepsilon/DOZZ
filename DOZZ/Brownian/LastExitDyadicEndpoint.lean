/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitDyadicShift
public import DOZZ.Brownian.LastExitFinite
public import DOZZ.Brownian.ConditionedFutureKernel
public import Mathlib.Probability.BrownianMotion.Basic

/-!
# The dyadic endpoint state converges to the barrier

At each mesh level the endpoint is deterministic on the last-exit cell. For paths with an
attained finite last exit, continuity makes the conditioned state at those endpoints converge to
the barrier. This is the pathwise concentration input for the entrance-kernel limit.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal

namespace DOZZ.Proofs

/-- Along the dyadic right endpoints of a finite last exit, the positive-coordinate state minus
the barrier tends to zero. -/
theorem conditionedPositiveStateAt_dyadicLastExit_sub_tendsto_zero
    (p : BrownianPath) (c : ℝ)
    (hnonempty : ({u : ℝ≥0 | p u = -c}).Nonempty)
    (hbounded : BddAbove {u : ℝ≥0 | p u = -c}) :
    Tendsto
      (fun n => conditionedPositiveStateAt
        (dyadicLastExitCeilingTime n (negativeLastExitTime p c)) p - c)
      atTop (𝓝 0) := by
  have hpath := continuousPath_dyadicLastExitCeiling_eval_tendsto
    p c hnonempty hbounded
  have hstate : Tendsto
      (fun n => conditionedPositiveStateAt
        (dyadicLastExitCeilingTime n (negativeLastExitTime p c)) p)
      atTop (𝓝 c) := by
    simpa only [conditionedPositiveStateAt, neg_neg] using hpath.neg
  have hsub := hstate.sub
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => c) atTop (𝓝 c))
  simpa using hsub

/-- Almost surely, the conditioned state at the dyadic endpoint selected by the finite last exit
converges to the barrier. -/
theorem ae_conditionedPositiveStateAt_dyadicLastExit_sub_tendsto_zero
    {ν : ℝ} {P : Measure BrownianPath}
    (hP : IsNegativeConditionedBrownianLaw ν P)
    {B : Measure BrownianPath} [SFinite B]
    (hB : IsBrownianReal (fun t p => p t) B)
    (hν : 0 < ν) (c : ℝ≥0) (hc : 0 < (c : ℝ)) :
    ∀ᵐ p ∂P, Tendsto
      (fun n => conditionedPositiveStateAt
        (dyadicLastExitCeilingTime n (negativeLastExitTime p c)) p - c)
      atTop (𝓝 0) := by
  have hgood := ae_negativeConditionedLevelHitSet_nonempty_bddAbove hP hB hν c hc
  filter_upwards [hgood] with p hp
  exact conditionedPositiveStateAt_dyadicLastExit_sub_tendsto_zero
    p (c : ℝ) hp.1 hp.2

end DOZZ.Proofs

end

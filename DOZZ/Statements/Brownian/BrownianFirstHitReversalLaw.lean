/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.NegativeConditionedPostLastExitPath
import DOZZ.Brownian.BrownianFirstHitReversalLaw

/-! The statement `DOZZ.brownian_firstHit_reversal_law`,
proved by `DOZZ.Proofs.brownian_firstHit_reversal_law`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- Reversal at a first hit is an equality in law of lifetime-marked stopped paths. The right side
is the conditioned path stopped at its last exit, not a strong-Markov claim at that last exit.
See [KRV, Lemma 3.1 and Remark 3.2]. -/
theorem brownian_firstHit_reversal_law
    (ν c : ℝ) (hν : 0 < ν) (hc : 0 < c)
    (P : Measure BrownianPath)
    (hP : ProbabilityTheory.IsBrownianReal (fun t p => p t) P)
    (Qν : Measure BrownianPath) (hQν : IsNegativeConditionedBrownianLaw ν Qν)
    : AEMeasurable (reversedPositiveFirstHitSegment ν c) P ∧
      AEMeasurable (negativeConditionedLastExitSegment c) Qν ∧
      P.map (reversedPositiveFirstHitSegment ν c) =
        Qν.map (negativeConditionedLastExitSegment c) := by exact DOZZ.Proofs.brownian_firstHit_reversal_law ν c hν hc P hP Qν hQν

end DOZZ

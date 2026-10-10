/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-/
module

public import DOZZ.Brownian.Williams.StoppedPaths
public import DOZZ.Statements.Brownian.NegativeConditionedPostLastExitPath

/-!
# Measurability of the recentered post-last-exit path

The literal last-exit time is measurable on the continuous-path carrier. Joint continuity of path
evaluation then makes the path shifted to that time measurable, with the level added back.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Shift a continuous path by a nonnegative time and add a fixed level to all its values. -/
noncomputable def shiftPathAddConstant (c : ℝ) (z : ℝ≥0 × BrownianPath) : BrownianPath :=
  ⟨fun t => z.2 (z.1 + t) + c, by
    exact (z.2.continuous.comp (continuous_const.add continuous_id)).add continuous_const⟩

/-- Joint continuity of shifting a path and adding a fixed level. -/
theorem continuous_shiftPathAddConstant (c : ℝ) :
    Continuous (fun z : ℝ≥0 × BrownianPath => shiftPathAddConstant c z) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z : (ℝ≥0 × BrownianPath) × ℝ≥0 => z.1.2 (z.1.1 + z.2) + c)
  exact (continuous_eval.comp
    (continuous_fst.snd.prodMk (continuous_fst.fst.add continuous_snd))).add continuous_const

/-- The last-exit recentering map is measurable for every fixed level. -/
theorem measurable_negativeConditionedPostLastExitPath (c : ℝ) :
    Measurable (negativeConditionedPostLastExitPath c) := by
  have hτ : Measurable (fun p : BrownianPath => negativeLastExitTime p c) :=
    measurable_negativeLastExitTime_joint.comp
      ((measurable_const (a := c)).prodMk measurable_id)
  have hmap : Measurable (fun p : BrownianPath =>
      shiftPathAddConstant c (negativeLastExitTime p c, p)) :=
    (continuous_shiftPathAddConstant c).measurable.comp (hτ.prodMk measurable_id)
  have heq : (fun p : BrownianPath => shiftPathAddConstant c (negativeLastExitTime p c, p)) =
      negativeConditionedPostLastExitPath c := by
    funext p
    ext t
    rfl
  rw [← heq]
  exact hmap

/-- In particular, the post-last-exit map `DOZZ.negativeConditionedPostLastExitPath` is
almost-everywhere measurable under any path measure. -/
theorem aemeasurable_negativeConditionedPostLastExitPath
    (c : ℝ) (P : Measure BrownianPath) :
    AEMeasurable (negativeConditionedPostLastExitPath c) P :=
  (measurable_negativeConditionedPostLastExitPath c).aemeasurable

end DOZZ.Proofs

end

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitAvoidance
public import DOZZ.Brownian.Barrier.Restart
public import DOZZ.Statements.Brownian.NegativeConditionedPostLastExitPath

/-!
# Pathwise dyadic approximation of the post-last-exit path

Continuity of the path shift turns the deterministic dyadic right endpoints into convergence of
the entire recentered future path. This is the pathwise input to the last-exit cell limit.
-/

@[expose] public section

open Filter Topology
open scoped NNReal

namespace DOZZ.Proofs

/-- For a continuous path with an attained finite last visit to `-c`, the future increment path
started at the last exit is exactly the post-last-exit path recentered by `c`. -/
theorem negativeConditionedPostLastExitPath_eq_shiftPath
    (p : BrownianPath) (c : ℝ)
    (hnonempty : ({u : ℝ≥0 | p u = -c}).Nonempty)
    (hbounded : BddAbove {u : ℝ≥0 | p u = -c}) :
    negativeConditionedPostLastExitPath c p =
      brownianShiftPath (negativeLastExitTime p c) p := by
  have hlast : p (negativeLastExitTime p c) = -c :=
    negativeLastExitTime_mem_of_nonempty_bddAbove p c hnonempty hbounded
  ext t
  simp [negativeConditionedPostLastExitPath, brownianShiftPath, hlast]

/-- Shifting a path at the dyadic ceiling of its finite last exit converges, in the continuous
path topology, to the post-last-exit path. The times in the sequence are deterministic mesh
endpoints once the last-exit cell is fixed. -/
theorem brownianShiftPath_dyadicLastExit_tendsto
    (p : BrownianPath) (c : ℝ)
    (hnonempty : ({u : ℝ≥0 | p u = -c}).Nonempty)
    (hbounded : BddAbove {u : ℝ≥0 | p u = -c}) :
    Tendsto
      (fun n => brownianShiftPath
        (dyadicLastExitCeilingTime n (negativeLastExitTime p c)) p)
      atTop (𝓝 (negativeConditionedPostLastExitPath c p)) := by
  let L : ℝ≥0 := negativeLastExitTime p c
  have htimeReal : Tendsto
      (fun n : ℕ =>
        (dyadicLastExitCeilingTime n (negativeLastExitTime p c) : ℝ))
      atTop (𝓝 (L : ℝ)) := by
    simpa [L] using dyadicLastExitCeilingTime_coe_tendsto L
  have htime : Tendsto
      (fun n : ℕ => dyadicLastExitCeilingTime n (negativeLastExitTime p c))
      atTop (𝓝 L) := by
    apply NNReal.isEmbedding_coe.tendsto_nhds_iff.mpr
    exact htimeReal
  have hpair : Tendsto
      (fun n : ℕ =>
        (dyadicLastExitCeilingTime n (negativeLastExitTime p c), p))
      atTop (𝓝 (L, p)) :=
    htime.prodMk_nhds (tendsto_const_nhds : Tendsto (fun _ : ℕ => p) atTop (𝓝 p))
  have hshift : Tendsto
      (fun n : ℕ => brownianShiftPath
        (dyadicLastExitCeilingTime n (negativeLastExitTime p c)) p)
      atTop (𝓝 (brownianShiftPath L p)) := by
    exact (continuous_brownianShiftPath.tendsto (L, p)).comp hpair
  have hpost : negativeConditionedPostLastExitPath c p = brownianShiftPath L p := by
    simpa [L] using negativeConditionedPostLastExitPath_eq_shiftPath p c hnonempty hbounded
  simpa [hpost] using hshift

end DOZZ.Proofs

end

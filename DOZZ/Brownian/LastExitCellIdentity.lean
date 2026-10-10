/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitAfterAbove
public import DOZZ.Brownian.LastExitCellHistory
public import DOZZ.Brownian.LastExitAvoidanceTouch

/-!
# Last-exit cells are deterministic-time hit-and-avoid events

For a deterministic interval `[a,b)`, the event that the last visit to the barrier lies in that
interval agrees almost surely with a visit during the interval followed by strict rational
avoidance after `b`. The last exit itself is used only to index a cell; all conditioning is at `b`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace DOZZ.Proofs

/-- The event that the last visit to `-c` lies in the deterministic half-open interval `[a,b)`. -/
def negativeConditionedLastExitTimeCell (a b c : ℝ≥0) : Set BrownianPath :=
  {p | negativeLastExitTime p (c : ℝ) ∈ Set.Ico a b}

/-- The last-exit cell event is measurable on continuous path space. -/
theorem measurableSet_negativeConditionedLastExitTimeCell
    (a b c : ℝ≥0) :
    MeasurableSet (negativeConditionedLastExitTimeCell a b c) := by
  let τ : BrownianPath → ℝ≥0 := fun p => negativeLastExitTime p (c : ℝ)
  have hτ : Measurable τ :=
    measurable_negativeLastExitTime_joint.comp
      ((measurable_const (a := (c : ℝ))).prodMk measurable_id)
  have hI : MeasurableSet (Set.Ico a b) := measurableSet_Ico
  change MeasurableSet (τ ⁻¹' Set.Ico a b)
  exact hI.preimage hτ

/-- Almost surely, a last-exit cell is exactly a deterministic-time history hit followed by
strict rational avoidance of the future. -/
theorem negativeConditionedLastExitTimeCell_ae_eq_historyAvoidance
    {ν : ℝ} {P B : Measure BrownianPath} [SFinite B]
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (hB : IsBrownianReal (fun t p => p t) B)
    (hν : 0 < ν) (a b c : ℝ≥0)
    (hb : 0 < (b : ℝ)) (hc : 0 < (c : ℝ)) :
    negativeConditionedLastExitTimeCell a b c =ᵐ[P]
      conditionedPositiveHistoryHitsOnInterval a b c ∩
        conditionedPositiveFutureRationalAvoidance b c := by
  have hgood := ae_negativeConditionedLevelHitSet_nonempty_bddAbove
    hP hB hν c hc
  have habove := ae_negativeConditionedPath_above_after_lastExit
    hP hB hν c hc
  have hneq := ae_conditionedPositiveStateAt_ne hP b hb (c : ℝ)
  have htouch := conditionedPositiveFutureAvoidanceTouchEvent_measure_zero
    hP hB hν b hb c hc
  have hnotouch : ∀ᵐ p ∂P,
      p ∉ conditionedPositiveFutureAvoidanceTouchEvent b c :=
    measure_eq_zero_iff_ae_notMem.mp htouch
  filter_upwards [hgood, habove, hneq, hnotouch] with p hp hafter hpneq hpnotouch
  rcases hp with ⟨hnonempty, hbounded⟩
  have hcelliff := negativeLastExitTime_mem_Ico_iff_deterministic_visits
    p (c : ℝ) a b hnonempty hbounded
  have hcellToHitAvoid :
      p ∈ negativeConditionedLastExitTimeCell a b c →
        p ∈ conditionedPositiveHistoryHitsOnInterval a b c ∧
          p ∈ conditionedPositiveFutureRationalAvoidance b c := by
    intro hcell
    have hvisit := hcelliff.mp hcell
    rcases hvisit with ⟨⟨u, hau, hpu⟩, hnohit⟩
    have hub : u < b := lt_of_not_ge (fun hbu => hnohit u hbu hpu)
    have hhistory : p ∈ conditionedPositiveHistoryHitsOnInterval a b c := by
      refine ⟨u, hau, hub.le, ?_⟩
      simpa [conditionedPositiveStateAt] using congrArg Neg.neg hpu
    have havoid : p ∈ conditionedPositiveFutureRationalAvoidance b c := by
      simp only [conditionedPositiveFutureRationalAvoidance, Set.mem_iInter]
      intro q
      by_cases hq : 0 < (q : ℝ)
      · rw [conditionedPositiveFutureAvoidanceCoordinate, dite_eq_left hq]
        change (c : ℝ) < conditionedPositiveFutureRationalEvals b p q
        let qTime : ℝ≥0 := ⟨(q : ℝ), hq.le⟩
        let t : ℝ≥0 := b + qTime
        have hLt : negativeLastExitTime p (c : ℝ) < t := by
          have hLb : negativeLastExitTime p (c : ℝ) < b := hcell.2
          have hqpos : 0 < qTime := by
            change (0 : ℝ) < (q : ℝ)
            exact hq
          have hbt : b < t := lt_add_of_pos_right b hqpos
          exact hLb.trans hbt
        have hstate := hafter t hLt
        have heval : conditionedPositiveFutureRationalEvals b p q =
            conditionedPositiveStateAt t p := by
          simp [conditionedPositiveFutureRationalEvals, conditionedPositiveFuturePath,
            conditionedPositiveStateAt, t, qTime,
            max_eq_left hq.le]
        rw [heval]
        simpa [conditionedPositiveStateAt] using hstate
      · simp [conditionedPositiveFutureAvoidanceCoordinate, hq]
    exact ⟨hhistory, havoid⟩
  have hhitAvoidToCell :
      p ∈ conditionedPositiveHistoryHitsOnInterval a b c ∩
          conditionedPositiveFutureRationalAvoidance b c →
        p ∈ negativeConditionedLastExitTimeCell a b c := by
    rintro ⟨hhistory, havoid⟩
    have hnohit : ∀ u : ℝ≥0, b ≤ u → p u ≠ -(c : ℝ) := by
      intro u hub hpu
      by_cases hEq : u = b
      · subst u
        have hstate : conditionedPositiveStateAt b p = (c : ℝ) := by
          simpa [conditionedPositiveStateAt] using congrArg Neg.neg hpu
        exact hpneq hstate
      · have hbu : b < u := lt_of_le_of_ne hub (fun hbu => hEq hbu.symm)
        have hHit : p ∈ conditionedPositiveFutureAvoidanceTouchEvent b c :=
          conditionedPositiveFutureAvoidance_hit_implies_touch b c p havoid
            ⟨u, hbu, hpu⟩
        exact hpnotouch hHit
    rcases hhistory with ⟨u, hau, hub, hu⟩
    have hpu : p u = -(c : ℝ) := by
      have h := congrArg Neg.neg hu
      simpa [conditionedPositiveStateAt] using h
    have hlastiff := hcelliff.mpr ⟨⟨u, hau, hpu⟩, hnohit⟩
    exact hlastiff
  apply propext
  constructor
  · exact hcellToHitAvoid
  · exact hhitAvoidToCell

/-- The deterministic-time avoidance identity on a last-exit cell. Its right endpoint is the
deterministic time at which the past/future factorization is applied. -/
theorem negativeConditionedLastExitCell_avoidance_shift_setIntegral
    {ν : ℝ} {P B : Measure BrownianPath} [IsFiniteMeasure P] [SFinite B]
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (hB : IsBrownianReal (fun t p => p t) B)
    (a b c : ℝ≥0) (hb : 0 < (b : ℝ))
    (hν : 0 < ν) (hc : 0 < (c : ℝ))
    (C : Set (ℚ → ℝ)) (hC : MeasurableSet C) :
    (∫ p in negativeConditionedLastExitTimeCell a b c,
      lastExitShiftedFutureTest (c : ℝ) C
        (conditionedPositiveFutureRationalEvals b p) ∂P) =
      (∫ p in conditionedPositiveHistoryHitsOnInterval a b c,
        lastExitAvoidanceFactor ν (c : ℝ) (conditionedPositiveStateAt b p) *
          (brownianUpperConditionedReferenceFutureKernel B ν hν
            (conditionedPositiveStateAt b p - c)).real C ∂P) := by
  let H := conditionedPositiveHistoryHitsOnInterval a b c
  let E := conditionedPositiveFutureRationalAvoidance b c
  let T : BrownianPath → ℝ := fun p => lastExitShiftedFutureTest (c : ℝ) C
    (conditionedPositiveFutureRationalEvals b p)
  have hcell := negativeConditionedLastExitTimeCell_ae_eq_historyAvoidance
    hP hB hν a b c hb hc
  have hE : MeasurableSet E := by
    change MeasurableSet (⋂ q : ℚ,
      conditionedPositiveFutureAvoidanceCoordinate b c q)
    exact MeasurableSet.iInter fun q =>
      measurableSet_conditionedPositiveFutureAvoidanceCoordinate b c q
  calc
    (∫ p in negativeConditionedLastExitTimeCell a b c, T p ∂P) =
        (∫ p in H ∩ E, T p ∂P) := setIntegral_congr_set hcell
    _ = (∫ p in H, E.indicator T p ∂P) := by
      rw [← setIntegral_indicator hE]
    _ = (∫ p in H,
        lastExitAvoidanceFactor ν (c : ℝ) (conditionedPositiveStateAt b p) *
          (brownianUpperConditionedReferenceFutureKernel B ν hν
            (conditionedPositiveStateAt b p - c)).real C ∂P) :=
      conditionedPositiveHistory_intervalHit_avoidance_shift_setIntegral
        hP B hB a b hb hν c hc C hC

end DOZZ.Proofs

end

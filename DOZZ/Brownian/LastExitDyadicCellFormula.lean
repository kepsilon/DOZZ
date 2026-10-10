/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitCellIdentity
public import DOZZ.Brownian.LastExitKernelEntranceLimit

/-!
# The dyadic cell formula for rational-future events

On a dyadic last-exit cell, the shifted rational future is evaluated at its deterministic right
endpoint. The deterministic-time avoidance identity then expresses the cell probability with a
finite-dimensional reference-kernel test.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace DOZZ.Proofs

/-- Left endpoint of the `k`th cell at dyadic mesh `2⁻ⁿ`. -/
noncomputable def dyadicLastExitCellStartTime (n k : ℕ) : ℝ≥0 :=
  ⟨(k : ℝ) / (2 : ℝ) ^ n, div_nonneg (Nat.cast_nonneg k) (by positivity)⟩

/-- Right endpoint of the `k`th cell at dyadic mesh `2⁻ⁿ`. -/
noncomputable def dyadicLastExitCellEndTime (n k : ℕ) : ℝ≥0 :=
  ⟨((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n, div_nonneg (by positivity) (by positivity)⟩

theorem dyadicLastExitCellEndTime_pos (n k : ℕ) :
    0 < (dyadicLastExitCellEndTime n k : ℝ) := by
  change 0 < ((k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n
  positivity

/-- The event that the recentered positive-coordinate future at a deterministic endpoint lies in
a measurable set of rational sequences. -/
def dyadicLastExitCellFutureEvent (n k : ℕ) (c : ℝ≥0)
    (C : Set (ℚ → ℝ)) : Set BrownianPath :=
  {p | lastExitRationalShift (c : ℝ)
      (conditionedPositiveFutureRationalEvals (dyadicLastExitCellEndTime n k) p) ∈ C}

theorem measurableSet_dyadicLastExitCellFutureEvent
    (n k : ℕ) (c : ℝ≥0) (C : Set (ℚ → ℝ)) (hC : MeasurableSet C) :
    MeasurableSet (dyadicLastExitCellFutureEvent n k c C) := by
  let b := dyadicLastExitCellEndTime n k
  have hEval : Measurable (conditionedPositiveFutureRationalEvals b) :=
    measurable_conditionedPositiveFutureRationalEvals b
  have hShift : Measurable (fun y : ℚ → ℝ => lastExitRationalShift (c : ℝ) y) := by
    apply measurable_pi_iff.mpr
    intro r
    exact (measurable_pi_apply r).sub measurable_const
  change MeasurableSet
    ((fun p => lastExitRationalShift (c : ℝ)
      (conditionedPositiveFutureRationalEvals b p)) ⁻¹' C)
  exact hC.preimage (hShift.comp hEval)

/-- The test integrand in the last-exit cell formula is the indicator of the corresponding
rational-future event. -/
theorem lastExitShiftedFutureTest_eq_dyadicCellEventIndicator
    (n k : ℕ) (c : ℝ≥0) (C : Set (ℚ → ℝ)) (p : BrownianPath) :
    lastExitShiftedFutureTest (c : ℝ) C
        (conditionedPositiveFutureRationalEvals (dyadicLastExitCellEndTime n k) p) =
      (dyadicLastExitCellFutureEvent n k c C).indicator (fun _ => (1 : ℝ)) p := by
  rfl

/-- The deterministic-time cell identity, converted from an indicator integral to the probability
of the cell and future cylinder event. -/
theorem negativeConditionedDyadicLastExitCell_test_measure
    {ν : ℝ} {P B : Measure BrownianPath} [IsFiniteMeasure P] [SFinite B]
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (hB : IsBrownianReal (fun t p => p t) B)
    (hν : 0 < ν) (c : ℝ≥0) (hc : 0 < (c : ℝ))
    (n k : ℕ) (C : Set (ℚ → ℝ)) (hC : MeasurableSet C) :
    P.real (negativeConditionedLastExitTimeCell
      (dyadicLastExitCellStartTime n k) (dyadicLastExitCellEndTime n k) c ∩
      dyadicLastExitCellFutureEvent n k c C) =
      ∫ p in conditionedPositiveHistoryHitsOnInterval
          (dyadicLastExitCellStartTime n k) (dyadicLastExitCellEndTime n k) c,
        lastExitAvoidanceFactor ν (c : ℝ) (conditionedPositiveStateAt
          (dyadicLastExitCellEndTime n k) p) *
          (brownianUpperConditionedReferenceFutureKernel B ν hν
            (conditionedPositiveStateAt (dyadicLastExitCellEndTime n k) p - c)).real C
          ∂P := by
  let a := dyadicLastExitCellStartTime n k
  let b := dyadicLastExitCellEndTime n k
  let L := negativeConditionedLastExitTimeCell a b c
  let E := dyadicLastExitCellFutureEvent n k c C
  have hb : 0 < (b : ℝ) := dyadicLastExitCellEndTime_pos n k
  have hcell := negativeConditionedLastExitCell_avoidance_shift_setIntegral
    hP hB a b c hb hν hc C hC
  have hE : MeasurableSet E := measurableSet_dyadicLastExitCellFutureEvent n k c C hC
  have hL : MeasurableSet L := measurableSet_negativeConditionedLastExitTimeCell a b c
  have hprob : P.real (L ∩ E) = ∫ p in L ∩ E, (1 : ℝ) ∂P := by
    calc
      P.real (L ∩ E) =
          ∫ p, (L ∩ E).indicator (fun _ => (1 : ℝ)) p ∂P :=
        (integral_indicator_one (hL.inter hE)).symm
      _ = ∫ p in L ∩ E, (1 : ℝ) ∂P := integral_indicator (hL.inter hE)
  have htest : ∀ p : BrownianPath,
      lastExitShiftedFutureTest (c : ℝ) C
        (conditionedPositiveFutureRationalEvals b p) =
          E.indicator (fun _ => (1 : ℝ)) p := by
    intro p
    simpa [E, b] using lastExitShiftedFutureTest_eq_dyadicCellEventIndicator n k c C p
  calc
    P.real (L ∩ E) = ∫ p in L, E.indicator (fun _ => (1 : ℝ)) p ∂P := by
      calc
        P.real (L ∩ E) = ∫ p in L ∩ E, (1 : ℝ) ∂P := hprob
        _ = ∫ p in L, E.indicator (fun _ => (1 : ℝ)) p ∂P := by
          rw [← setIntegral_indicator hE]
    _ = ∫ p in L, lastExitShiftedFutureTest (c : ℝ) C
          (conditionedPositiveFutureRationalEvals b p) ∂P := by
      apply setIntegral_congr_fun hL
      intro p hp
      exact (htest p).symm
    _ = ∫ p in conditionedPositiveHistoryHitsOnInterval a b c,
        lastExitAvoidanceFactor ν (c : ℝ) (conditionedPositiveStateAt b p) *
          (brownianUpperConditionedReferenceFutureKernel B ν hν
            (conditionedPositiveStateAt b p - c)).real C ∂P := by
      simpa only [a, b, L] using hcell

end DOZZ.Proofs

end

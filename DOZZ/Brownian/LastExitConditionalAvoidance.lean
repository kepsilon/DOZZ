/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedFutureHistoryAvoidance
public import DOZZ.Brownian.LastExitReferenceAvoidanceShift

/-!
# Deterministic-time full-history avoidance identity

For measurable tests of the recentered rational future, the full-history conditional expectation
is the avoidance factor times the entrance-kernel expectation from the reduced endpoint. The
statement is localized to endpoints strictly above the barrier, where the killed-kernel shift
identity applies.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

def lastExitRationalShift (c : ℝ) (y : ℚ → ℝ) : ℚ → ℝ :=
  fun r => y r - c

/-- A sequence-valued future test after subtracting the barrier. -/
noncomputable def lastExitShiftedFutureTest (c : ℝ) (C : Set (ℚ → ℝ)) :
    (ℚ → ℝ) → ℝ :=
  fun y => (C.indicator (fun _ : ℚ → ℝ => (1 : ℝ))) (lastExitRationalShift c y)

private theorem measurable_lastExitRationalShift (c : ℝ) :
    Measurable (lastExitRationalShift c) := by
  apply measurable_pi_iff.mpr
  intro r
  exact (measurable_pi_apply r).sub measurable_const

private theorem lastExitAvoidanceFactor_pos_of_above
    {ν c x : ℝ} (hν : 0 < ν) (hc : 0 < c) (hcx : c < x) :
    0 < lastExitAvoidanceFactor ν c x := by
  have hHpos : ∀ {z : ℝ}, 0 < z → 0 < conditionedH ν z := by
    intro z hz
    rw [conditionedH, ite_eq_right hν.ne']
    apply sub_pos.mpr
    apply Real.exp_lt_one_iff.mpr
    nlinarith
  simp [lastExitAvoidanceFactor, hcx]
  exact div_pos (hHpos (sub_pos.mpr hcx)) (hHpos (lt_trans hc hcx))

private theorem conditionedPositiveFutureAvoidanceSequence_eq_reference
    (c : ℝ≥0) :
    conditionedPositiveFutureAvoidanceSequence c =
      brownianRationalFutureAbove (c : ℝ) := by
  ext y
  simp [conditionedPositiveFutureAvoidanceSequence, brownianRationalFutureAbove]

private theorem measurableSet_brownianReferenceAvoidanceAndTest
    (c : ℝ) {C : Set (ℚ → ℝ)} (hC : MeasurableSet C) :
    MeasurableSet {y : ℚ → ℝ |
      y ∈ brownianRationalFutureAbove c ∧ lastExitRationalShift c y ∈ C} := by
  exact (measurableSet_brownianRationalFutureAbove c).inter
    (hC.preimage (measurable_lastExitRationalShift c))

/-- Conditional expectation of an arbitrary measurable event of the recentered rational future,
given the complete history at a deterministic time. -/
theorem conditionedPositiveHistory_condExp_rationalFuture_avoidance_shift_on_above
    {ν : ℝ} {P : Measure BrownianPath} [IsFiniteMeasure P]
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (B : Measure BrownianPath) [SFinite B]
    (hB : IsBrownianReal (fun t p => p t) B)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (hν : 0 < ν)
    (c : ℝ≥0) (hc : 0 < (c : ℝ))
    (C : Set (ℚ → ℝ)) (hC : MeasurableSet C) :
    ∀ᵐ p ∂P, (c : ℝ) < conditionedPositiveStateAt t p →
      P[(conditionedPositiveFutureRationalAvoidance t c).indicator
        (fun p => lastExitShiftedFutureTest (c : ℝ) C
          (conditionedPositiveFutureRationalEvals t p)) |
        conditionedPositiveNaturalFiltration t] p =
        lastExitAvoidanceFactor ν (c : ℝ) (conditionedPositiveStateAt t p) *
          (brownianUpperConditionedReferenceFutureKernel B ν hν
            (conditionedPositiveStateAt t p - c)).real C := by
  classical
  let eval : BrownianPath → (ℚ → ℝ) := conditionedPositiveFutureRationalEvals t
  let shift := lastExitRationalShift (c : ℝ)
  let test : (ℚ → ℝ) → ℝ := lastExitShiftedFutureTest (c : ℝ) C
  let shiftedEval : BrownianPath → (ℚ → ℝ) := fun p => shift (eval p)
  let pathTestSet : Set BrownianPath := shiftedEval ⁻¹' C
  have hEval : Measurable eval := measurable_conditionedPositiveFutureRationalEvals t
  have hShift : Measurable shift := measurable_lastExitRationalShift (c : ℝ)
  have hShiftedEval : Measurable shiftedEval := hShift.comp hEval
  have hPathTestSet : MeasurableSet pathTestSet := hC.preimage hShiftedEval
  have hTest : Measurable test := by
    dsimp [test, lastExitShiftedFutureTest, shift]
    exact (measurable_const.indicator hC).comp hShift
  have hTestInt : Integrable (fun p => test (eval p)) P := by
    have hfun : (fun p => test (eval p)) =
        pathTestSet.indicator (fun _ : BrownianPath => (1 : ℝ)) := by
      funext p
      simp [test, lastExitShiftedFutureTest, pathTestSet, shiftedEval, shift,
        Set.indicator_apply]
    rw [hfun]
    exact (integrable_const (1 : ℝ)).indicator hPathTestSet
  have hcond := conditionedPositiveHistory_condExp_rationalFuture_avoidance
    hP t ht c test hTest.stronglyMeasurable hTestInt
  have hKernel := conditionedPositiveFutureKernel_eq_reference_ae
    hP B hB t ht hν
  have hKernelPath : ∀ᵐ p ∂P,
      conditionedPositiveFutureKernel t P (conditionedPositiveStateAt t p) =
        brownianUpperConditionedReferenceFutureKernel B ν hν
          (conditionedPositiveStateAt t p) :=
    P.tendsto_ae_map (measurable_conditionedPositiveStateAt t).aemeasurable hKernel
  have hAvoidEq := conditionedPositiveFutureAvoidanceSequence_eq_reference c
  filter_upwards [hcond, hKernelPath] with p hp hk
  intro hcx
  let x : ℝ := conditionedPositiveStateAt t p
  have hx : 0 < x := lt_trans hc hcx
  have hcond' :
    P[(conditionedPositiveFutureRationalAvoidance t c).indicator
        (fun p => test (eval p)) |
        conditionedPositiveNaturalFiltration t] p =
        ∫ y, (brownianRationalFutureAbove (c : ℝ)).indicator test y ∂
            brownianUpperConditionedReferenceFutureKernel B ν hν x := by
    have hp'' :
        P[(conditionedPositiveFutureRationalAvoidance t c).indicator
          (fun p => test (eval p)) |
          conditionedPositiveNaturalFiltration t] p =
          ∫ y, (conditionedPositiveFutureAvoidanceSequence c).indicator test y ∂
            conditionedPositiveFutureKernel t P x := by
      simpa [conditionedPositiveEndpointFutureKernel,
        Kernel.comp_deterministic_eq_comap, Kernel.comap_apply,
        conditionedPositiveHistory_current, eval, test, x] using hp
    rw [hk] at hp''
    rw [hAvoidEq] at hp''
    simpa [x] using hp''
  let D : Set (ℚ → ℝ) :=
    {y | y ∈ brownianRationalFutureAbove (c : ℝ) ∧ shift y ∈ C}
  have hshiftEq (y : ℚ → ℝ) : shift y = (fun r => y r - (c : ℝ)) := by
    funext r
    rfl
  have hD : MeasurableSet D :=
    measurableSet_brownianReferenceAvoidanceAndTest (c : ℝ) hC
  have hG : Measurable (C.indicator (fun _ : ℚ → ℝ => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hC
  have hshift :=
    brownianUpperConditionedReferenceFutureKernel_avoidance_shift_lintegral
      B hB ν (c : ℝ) x hν hc hcx
      (C.indicator (fun _ : ℚ → ℝ => (1 : ℝ≥0∞))) hG
  have hmeasure :
      (brownianUpperConditionedReferenceFutureKernel B ν hν x) D =
        ENNReal.ofReal (lastExitAvoidanceFactor ν (c : ℝ) x) *
          (brownianUpperConditionedReferenceFutureKernel B ν hν (x - c)) C := by
    calc
      (brownianUpperConditionedReferenceFutureKernel B ν hν x) D =
        ∫⁻ y, D.indicator (fun _ : ℚ → ℝ => (1 : ℝ≥0∞)) y ∂
            brownianUpperConditionedReferenceFutureKernel B ν hν x := by
          exact (lintegral_indicator_one hD).symm
      _ = ∫⁻ y, (brownianRationalFutureAbove (c : ℝ)).indicator
          (fun y => (C.indicator (fun _ : ℚ → ℝ => (1 : ℝ≥0∞)))
            (fun r => y r - (c : ℝ))) y ∂
            brownianUpperConditionedReferenceFutureKernel B ν hν x := by
          apply lintegral_congr
          intro y
          have hmemEq : (shift y ∈ C) =
              ((fun r => y r - (c : ℝ)) ∈ C) :=
            congrArg (fun z : ℚ → ℝ => z ∈ C) (hshiftEq y)
          by_cases hy : y ∈ brownianRationalFutureAbove (c : ℝ)
          · by_cases hcY : (fun r => y r - (c : ℝ)) ∈ C
            · simp [D, hmemEq, Set.indicator_apply, hy, hcY]
            · simp [D, hmemEq, Set.indicator_apply, hy, hcY]
          · simp [D, Set.indicator_apply, hy]
      _ = ENNReal.ofReal (lastExitAvoidanceFactor ν (c : ℝ) x) *
          ∫⁻ y, (C.indicator (fun _ : ℚ → ℝ => (1 : ℝ≥0∞))) y ∂
            brownianUpperConditionedReferenceFutureKernel B ν hν (x - c) := by
            exact hshift
      _ = _ := congrArg
        (fun z : ℝ≥0∞ => ENNReal.ofReal (lastExitAvoidanceFactor ν (c : ℝ) x) * z)
        (lintegral_indicator_one hC)
  have hfactor : 0 < lastExitAvoidanceFactor ν (c : ℝ) x :=
    lastExitAvoidanceFactor_pos_of_above hν hc hcx
  have hmass :
      (brownianUpperConditionedReferenceFutureKernel B ν hν x).real
          D =
        lastExitAvoidanceFactor ν (c : ℝ) x *
          (brownianUpperConditionedReferenceFutureKernel B ν hν (x - c)).real C := by
    rw [measureReal_def, hmeasure, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hfactor.le, measureReal_def]
  have hintegral :
      (∫ y, (brownianRationalFutureAbove (c : ℝ)).indicator
          test y ∂
            brownianUpperConditionedReferenceFutureKernel B ν hν x) =
        (brownianUpperConditionedReferenceFutureKernel B ν hν x).real D := by
    calc
      (∫ y, (brownianRationalFutureAbove (c : ℝ)).indicator
          (fun y => (C.indicator (fun _ : ℚ → ℝ => (1 : ℝ))) (shift y)) y ∂
            brownianUpperConditionedReferenceFutureKernel B ν hν x) =
        ∫ y, D.indicator (fun _ : ℚ → ℝ => (1 : ℝ)) y ∂
            brownianUpperConditionedReferenceFutureKernel B ν hν x := by
          apply integral_congr_ae
          filter_upwards [] with y
          have hmemEq : (shift y ∈ C) =
              ((fun r => y r - (c : ℝ)) ∈ C) :=
            congrArg (fun z : ℚ → ℝ => z ∈ C) (hshiftEq y)
          by_cases hy : y ∈ brownianRationalFutureAbove (c : ℝ)
          · by_cases hcY : (fun r => y r - (c : ℝ)) ∈ C
            · simp [D, hmemEq,
                Set.indicator_apply, hy, hcY]
            · simp [D, hmemEq,
                Set.indicator_apply, hy, hcY]
          · simp [D, Set.indicator_apply, hy]
      _ = _ := integral_indicator_one hD
  rw [hcond', hintegral, hmass]

end DOZZ.Proofs

end

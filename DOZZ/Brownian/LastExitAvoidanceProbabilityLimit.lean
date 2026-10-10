/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitCellHistory
public import DOZZ.Brownian.LastExitAvoidanceStateLimit

/-!
# Late-time rational survival probability

The full-history avoidance identity identifies the probability of staying above a fixed level at
all positive rational future offsets with the mean Doob avoidance factor.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal Topology

namespace DOZZ.Proofs

/-- The rational future survival event has probability equal to the mean deterministic-time
avoidance factor. -/
theorem conditionedPositiveFutureRationalAvoidance_realMeasure_eq_integral_factor
    {ν : ℝ} {P B : Measure BrownianPath}
    [SFinite B]
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (hB : IsBrownianReal (fun t p => p t) B)
    (hν : 0 < ν) (t : ℝ≥0) (ht : 0 < (t : ℝ))
    (c : ℝ≥0) (hc : 0 < (c : ℝ)) :
    P.real (conditionedPositiveFutureRationalAvoidance t c) =
      ∫ p, lastExitAvoidanceFactor ν (c : ℝ) (conditionedPositiveStateAt t p) ∂P := by
  let : IsProbabilityMeasure P := hP.2.1
  let E := conditionedPositiveFutureRationalAvoidance t c
  have hE : MeasurableSet E := by
    change MeasurableSet (⋂ q : ℚ,
      conditionedPositiveFutureAvoidanceCoordinate t c q)
    exact MeasurableSet.iInter fun q =>
      measurableSet_conditionedPositiveFutureAvoidanceCoordinate t c q
  have hfactorization := conditionedPositiveHistory_avoidance_shift_setIntegral
    hP B hB t ht hν c hc Set.univ MeasurableSet.univ
    Set.univ MeasurableSet.univ
  have hleft :
      (∫ p in Set.univ,
        E.indicator (fun p => lastExitShiftedFutureTest (c : ℝ) Set.univ
          (conditionedPositiveFutureRationalEvals t p)) p ∂P) = P.real E := by
    rw [setIntegral_univ]
    have htest : (fun p : BrownianPath =>
        lastExitShiftedFutureTest (c : ℝ) Set.univ
          (conditionedPositiveFutureRationalEvals t p)) = fun _ => (1 : ℝ) := by
      funext p
      simp [lastExitShiftedFutureTest]
    rw [htest]
    calc
      _ = ∫ p, E.indicator (1 : BrownianPath → ℝ) p ∂P := by congr 1
      _ = P.real E := integral_indicator_one hE
  have hmass (p : BrownianPath) :
      lastExitAvoidanceFactor ν (c : ℝ) (conditionedPositiveStateAt t p) *
        (brownianUpperConditionedReferenceFutureKernel B ν hν
          (conditionedPositiveStateAt t p - c)).real Set.univ =
        lastExitAvoidanceFactor ν (c : ℝ) (conditionedPositiveStateAt t p) := by
    by_cases hcx : (c : ℝ) < conditionedPositiveStateAt t p
    · have hx : 0 < conditionedPositiveStateAt t p - (c : ℝ) := sub_pos.mpr hcx
      have : IsProbabilityMeasure
          (brownianBelowConditionedLaw B ν
            (conditionedPositiveStateAt t p - (c : ℝ))) :=
        isProbabilityMeasure_brownianBelowConditionedLaw B hB ν
          (conditionedPositiveStateAt t p - (c : ℝ)) hν hx
      have : IsProbabilityMeasure
          (brownianUpperConditionedReferenceFutureKernel B ν hν
            (conditionedPositiveStateAt t p - (c : ℝ))) := by
        rw [brownianUpperConditionedReferenceFutureKernel_apply_conditioned
          B ν (conditionedPositiveStateAt t p - (c : ℝ)) hν hx]
        infer_instance
      have hreal :
          (brownianUpperConditionedReferenceFutureKernel B ν hν
            (conditionedPositiveStateAt t p - (c : ℝ))).real Set.univ = 1 := by
        rw [measureReal_def]
        simp
      rw [hreal, mul_one]
    · simp [lastExitAvoidanceFactor, hcx]
  have hright :
      (∫ p in Set.univ,
        lastExitAvoidanceFactor ν (c : ℝ) (conditionedPositiveStateAt t p) *
          (brownianUpperConditionedReferenceFutureKernel B ν hν
            (conditionedPositiveStateAt t p - c)).real Set.univ ∂P) =
      ∫ p, lastExitAvoidanceFactor ν (c : ℝ)
          (conditionedPositiveStateAt t p) ∂P := by
    rw [setIntegral_univ]
    apply integral_congr_ae
    exact ae_of_all P hmass
  rw [← hleft, hfactorization, hright]

/-- The rational future survival probability tends to one at large deterministic times. -/
theorem conditionedPositiveFutureRationalAvoidance_realMeasure_tendsto_one_atTop
    {ν : ℝ} {P B : Measure BrownianPath} [SFinite B]
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (hB : IsBrownianReal (fun t p => p t) B)
    (hν : 0 < ν) (c : ℝ≥0) (hc : 0 < (c : ℝ)) :
    Tendsto (fun t : ℝ≥0 =>
      P.real (conditionedPositiveFutureRationalAvoidance t c)) atTop (𝓝 1) := by
  have hlimit := tendsto_integral_lastExitAvoidanceFactor_atTop hP hν (c : ℝ) hc
  apply hlimit.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with t ht
  simpa [conditionedPositiveStateAt] using
    (conditionedPositiveFutureRationalAvoidance_realMeasure_eq_integral_factor
      hP hB hν t (by exact_mod_cast ht) c hc).symm

end DOZZ.Proofs

end

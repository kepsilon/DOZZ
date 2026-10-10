/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitHistoryAvoidanceFactorization
public import DOZZ.Brownian.LastExitReferenceTouch

/-!
# Real-time future touches under rational avoidance

At every deterministic time, the full-history avoidance identity assigns zero mass to rational
survival accompanied by an actual future touch. The Brownian reference kernel reduces this event
to an atom of its global maximum law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Topology
open scoped NNReal

namespace DOZZ.Proofs

/-- Strict rational future avoidance together with a rational future approaching the barrier. -/
def conditionedPositiveFutureAvoidanceTouchEvent (t c : ℝ≥0) : Set BrownianPath :=
  conditionedPositiveFutureRationalAvoidance t c ∩
    (fun p => lastExitRationalShift (c : ℝ)
      (conditionedPositiveFutureRationalEvals t p)) ⁻¹'
        brownianPositiveRationalTouchZero


/-- Under rational avoidance, a real-time future hit forces the shifted rational future to
approach zero. -/
theorem conditionedPositiveFutureAvoidance_hit_implies_touch
    (t c : ℝ≥0) (p : BrownianPath)
    (hp : p ∈ conditionedPositiveFutureRationalAvoidance t c)
    (hHit : ∃ u : ℝ≥0, t < u ∧ p u = -(c : ℝ)) :
    p ∈ conditionedPositiveFutureAvoidanceTouchEvent t c := by
  rcases hHit with ⟨u, htu, hpu⟩
  have hsreal : 0 < (u : ℝ) - (t : ℝ) :=
    sub_pos.mpr (by exact_mod_cast htu)
  let s : ℝ≥0 := ⟨(u : ℝ) - (t : ℝ), hsreal.le⟩
  have hs : 0 < (s : ℝ) := hsreal
  have hts : t + s = u := by
    apply Subtype.ext
    change (t : ℝ) + ((u : ℝ) - (t : ℝ)) = (u : ℝ)
    ring
  have hpathHit : conditionedPositiveFuturePath t p s = (c : ℝ) := by
    change -(p (t + s)) = (c : ℝ)
    rw [hts, hpu]
    simp
  have havoid (r : ℚ) (hr : 0 < (r : ℝ)) :
      (c : ℝ) < conditionedPositiveFutureRationalEvals t p r := by
    have hcoord := (Set.mem_iInter.mp hp) r
    simpa [conditionedPositiveFutureAvoidanceCoordinate, hr] using hcoord
  let F : ℝ → ℝ := fun z => conditionedPositiveFuturePath t p
    ⟨max z 0, le_max_right z 0⟩
  have hFval (z : ℝ) (hz : 0 ≤ z) :
      F z = conditionedPositiveFuturePath t p ⟨z, hz⟩ := by
    dsimp [F]
    congr 1
    exact Subtype.ext (max_eq_left hz)
  have hFcont : Continuous (fun z : ℝ => conditionedPositiveFuturePath t p
      ⟨max z 0, le_max_right z 0⟩) := by
    exact (conditionedPositiveFuturePath t p).continuous.comp
      ((continuous_max.comp (continuous_id.prodMk continuous_const)).subtype_mk
        (fun z => le_max_right z 0))
  have htouch : lastExitRationalShift (c : ℝ)
      (conditionedPositiveFutureRationalEvals t p) ∈
      brownianPositiveRationalTouchZero := by
    constructor
    · intro r hr
      simp only [lastExitRationalShift]
      exact sub_pos.mpr (havoid r hr)
    · intro n
      have hF : Continuous F := hFcont
      have hFs : F (s : ℝ) = (c : ℝ) := by
        rw [hFval (s : ℝ) s.property]
        exact hpathHit
      let U : Set ℝ := Set.Ioi 0 ∩ F ⁻¹' Set.Iio ((c : ℝ) + 1 / ((n : ℝ) + 1))
      have hU : IsOpen U := isOpen_Ioi.inter (isOpen_Iio.preimage hF)
      have hsU : (s : ℝ) ∈ U := by
        refine ⟨hs, ?_⟩
        change F (s : ℝ) < (c : ℝ) + 1 / ((n : ℝ) + 1)
        rw [hFs]
        have : 0 < 1 / ((n : ℝ) + 1) := by positivity
        exact lt_add_of_pos_right (c : ℝ) this
      obtain ⟨r, hrU⟩ := Rat.denseRange_cast.exists_mem_open hU ⟨(s : ℝ), hsU⟩
      have hr : 0 < (r : ℝ) := hrU.1
      have hFr : F (r : ℝ) < (c : ℝ) + 1 / ((n : ℝ) + 1) := hrU.2
      have hEval : conditionedPositiveFutureRationalEvals t p r = F (r : ℝ) := by
        rfl
      refine ⟨r, hr, ?_⟩
      simp only [lastExitRationalShift, hEval]
      linarith
  exact ⟨hp, htouch⟩

/-- For every positive barrier and every deterministic positive time, the probability of strict
rational survival and an actual later level visit is zero. -/
theorem conditionedPositiveFutureAvoidanceTouchEvent_measure_zero
    {ν : ℝ} {P B : Measure BrownianPath} [SFinite B]
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (hB : IsBrownianReal (fun t p => p t) B)
    (hν : 0 < ν) (t : ℝ≥0) (ht : 0 < (t : ℝ))
    (c : ℝ≥0) (hc : 0 < (c : ℝ)) :
    P (conditionedPositiveFutureAvoidanceTouchEvent t c) = 0 := by
  let : IsProbabilityMeasure P := hP.2.1
  have hfact := conditionedPositiveHistory_avoidance_shift_setIntegral
    hP B hB t ht hν c hc brownianPositiveRationalTouchZero
    measurableSet_brownianPositiveRationalTouchZero Set.univ MeasurableSet.univ
  have havoid : MeasurableSet (conditionedPositiveFutureRationalAvoidance t c) := by
    change MeasurableSet (⋂ q : ℚ,
      conditionedPositiveFutureAvoidanceCoordinate t c q)
    exact MeasurableSet.iInter fun q =>
      measurableSet_conditionedPositiveFutureAvoidanceCoordinate t c q
  have hshift : Measurable (lastExitRationalShift (c : ℝ)) := by
    apply measurable_pi_iff.mpr
    intro r
    exact (measurable_pi_apply r).sub measurable_const
  have heval : Measurable (conditionedPositiveFutureRationalEvals t) :=
    measurable_conditionedPositiveFutureRationalEvals t
  let shiftedEval : BrownianPath → (ℚ → ℝ) := fun p =>
    lastExitRationalShift (c : ℝ) (conditionedPositiveFutureRationalEvals t p)
  let E : Set BrownianPath :=
    conditionedPositiveFutureRationalAvoidance t c ∩
      shiftedEval ⁻¹' brownianPositiveRationalTouchZero
  have hE : MeasurableSet E := by
    exact havoid.inter (measurableSet_brownianPositiveRationalTouchZero.preimage
      (hshift.comp heval))
  have hleft :
      (∫ p in Set.univ,
        (conditionedPositiveFutureRationalAvoidance t c).indicator
          (fun p => lastExitShiftedFutureTest (c : ℝ)
            brownianPositiveRationalTouchZero
            (conditionedPositiveFutureRationalEvals t p)) p ∂P) = P.real E := by
    rw [setIntegral_univ]
    have hfun : (fun p : BrownianPath =>
        (conditionedPositiveFutureRationalAvoidance t c).indicator
          (fun p => lastExitShiftedFutureTest (c : ℝ)
            brownianPositiveRationalTouchZero
            (conditionedPositiveFutureRationalEvals t p)) p) =
        E.indicator (fun _ => (1 : ℝ)) := by
      funext p
      by_cases hp : p ∈ conditionedPositiveFutureRationalAvoidance t c
      · by_cases hq : shiftedEval p ∈ brownianPositiveRationalTouchZero
        · simp [E, shiftedEval, lastExitShiftedFutureTest,
            hp, hq]
        · simp [E, shiftedEval, lastExitShiftedFutureTest,
            hp, hq]
      · simp [E, hp]
    rw [hfun]
    change (∫ p, E.indicator (1 : BrownianPath → ℝ) p ∂P) = P.real E
    exact integral_indicator_one hE
  have hmass (p : BrownianPath) :
      lastExitAvoidanceFactor ν (c : ℝ) (conditionedPositiveStateAt t p) *
        (brownianUpperConditionedReferenceFutureKernel B ν hν
          (conditionedPositiveStateAt t p - (c : ℝ))).real
            brownianPositiveRationalTouchZero = 0 := by
    by_cases hcx : (c : ℝ) < conditionedPositiveStateAt t p
    · have ha : 0 < conditionedPositiveStateAt t p - (c : ℝ) := sub_pos.mpr hcx
      have hzero := brownianUpperConditionedReferenceFutureKernel_measure_touchZero
        B hB ν (conditionedPositiveStateAt t p - (c : ℝ)) hν ha
      have hreal :
          (brownianUpperConditionedReferenceFutureKernel B ν hν
            (conditionedPositiveStateAt t p - (c : ℝ))).real
              brownianPositiveRationalTouchZero = 0 := by
        rw [measureReal_def, hzero]
        simp
      rw [hreal, mul_zero]
    · simp [lastExitAvoidanceFactor, hcx]
  have hright :
      (∫ p in Set.univ,
        lastExitAvoidanceFactor ν (c : ℝ) (conditionedPositiveStateAt t p) *
          (brownianUpperConditionedReferenceFutureKernel B ν hν
            (conditionedPositiveStateAt t p - (c : ℝ))).real
              brownianPositiveRationalTouchZero ∂P) = 0 := by
    rw [setIntegral_univ]
    have hzero : (fun p : BrownianPath =>
        lastExitAvoidanceFactor ν (c : ℝ) (conditionedPositiveStateAt t p) *
          (brownianUpperConditionedReferenceFutureKernel B ν hν
            (conditionedPositiveStateAt t p - (c : ℝ))).real
              brownianPositiveRationalTouchZero) = fun _ => (0 : ℝ) := by
      funext p
      exact hmass p
    rw [hzero, integral_zero]
  have hreal : P.real E = 0 := by
    rw [hleft, hright] at hfact
    exact hfact
  change P E = 0
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).1 hreal

end DOZZ.Proofs

end

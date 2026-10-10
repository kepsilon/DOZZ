/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Williams.ReversalMarkedLaw
public import DOZZ.Brownian.Williams.StoppedPreterminalUniqueness

/-!
# First-hit reversal as an equality of stopped continuous path laws

The deterministic-time avoidance identity gives the last-exit marked past density.
Kernel transposition and harmonic cancellation identify every preterminal marked law with
the reversed first-hit law. The initial and terminal values then determine the whole stopped
continuous path measure. No Markov property at a last exit is used.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace DOZZ.Proofs

/-- Reversal at a first hit is the conditioned path stopped at its last exit, with its lifetime
retained. This proves `DOZZ.brownian_firstHit_reversal_law`. -/
theorem brownian_firstHit_reversal_law
    (ν c : ℝ) (hν : 0 < ν) (hc : 0 < c)
    (P : Measure BrownianPath)
    (hP : ProbabilityTheory.IsBrownianReal (fun t p => p t) P)
    (Qν : Measure BrownianPath) (hQν : IsNegativeConditionedBrownianLaw ν Qν)
    : AEMeasurable (reversedPositiveFirstHitSegment ν c) P ∧
      AEMeasurable (negativeConditionedLastExitSegment c) Qν ∧
      P.map (reversedPositiveFirstHitSegment ν c) =
        Qν.map (negativeConditionedLastExitSegment c) := by
  let : IsProbabilityMeasure P := (hP.hasLaw_eval 0).isProbabilityMeasure
  let : IsProbabilityMeasure Qν := hQν.2.1
  refine ⟨(measurable_reversedPositiveFirstHitSegment ν c).aemeasurable,
    (measurable_negativeConditionedLastExitSegment c).aemeasurable, ?_⟩
  let X := reversedPositiveFirstHitSegment ν c
  let Y := negativeConditionedLastExitSegment c
  let μ := P.map X
  let η := Qν.map Y
  have hX : Measurable X := measurable_reversedPositiveFirstHitSegment ν c
  have hY : Measurable Y := measurable_negativeConditionedLastExitSegment c
  have hmark : SameStoppedPreterminalLaws μ η := by
    intro n ss hss hs0
    rw [Measure.restrict_map hX (measurableSet_lt measurable_const measurable_fst),
      Measure.restrict_map hY (measurableSet_lt measurable_const measurable_fst),
      Measure.map_map (measurable_stoppedPreterminalObservation n ss) hX,
      Measure.map_map (measurable_stoppedPreterminalObservation n ss) hY]
    have heX : stoppedPreterminalObservation n ss ∘ X =
        brownianFirstHitReversedIncreasingObservation ν c n ss := by
      funext p
      apply Prod.ext
      · funext i
        change -(driftedBrownianPath ν p
          (firstPassageTime (driftedBrownianPath ν p) c-
            min (ss i) (firstPassageTime (driftedBrownianPath ν p) c))-c) = _
        rw [min_comm, tsub_min]
        change -(p _+ν*(_ : ℝ)-c) = c-(p _+ν*(_ : ℝ))
        ring
      · rfl
    rw [heX]
    change (P.restrict {p | ss (Fin.last n) < firstPassageTime (driftedBrownianPath ν p) c}).map
      (brownianFirstHitReversedIncreasingObservation ν c n ss) =
      (Qν.restrict {p | ss (Fin.last n) < negativeLastExitTime p c}).map
        (stoppedPreterminalObservation n ss ∘ Y)
    have heY : stoppedPreterminalObservation n ss ∘ Y =ᵐ[
        Qν.restrict {p | ss (Fin.last n) < negativeLastExitTime p c}]
        conditionedLastExitMarkedObservation c n ss := by
      filter_upwards [ae_restrict_mem (measurableSet_lt measurable_const
        (measurable_negativeLastExitTime_joint.comp (measurable_const.prodMk measurable_id)))] with p hp
      apply Prod.ext
      · funext i
        change -(p (min (ss i) (negativeLastExitTime p c))) = -(p (ss i))
        rw [min_eq_left ((hss.monotone (Fin.le_last i)).trans hp.le)]
      · rfl
    rw [Measure.map_congr heY]
    exact brownian_firstHit_reversal_finite_marked_law ν c hν hc P hP Qν hQν n ss hss hs0
  have hfirst := brownianPath_positiveDrift_firstHit_ae P hP ν c hν hc
  let cN := Real.toNNReal c
  have hcN : 0 < (cN : ℝ) := by simpa only [cN, Real.coe_toNNReal _ hc.le] using hc
  have hgood := ae_negativeConditionedLevelHitSet_nonempty_bddAbove hQν hP hν cN hcN
  simp only [cN, Real.coe_toNNReal _ hc.le] at hgood
  have hlast : ∀ᵐ p ∂Qν, p (negativeLastExitTime p c) = -c ∧ 0 < negativeLastExitTime p c := by
    filter_upwards [hgood, hQν.2.2.1] with p hp hp0
    have hv := negativeLastExitTime_mem_of_nonempty_bddAbove p c hp.1 hp.2
    refine ⟨hv, pos_iff_ne_zero.mpr ?_⟩
    intro heq
    rw [heq, hp0] at hv
    linarith
  have hμpos : ∀ᵐ z ∂μ, 0 < z.1 := by
    apply (ae_map_iff hX.aemeasurable (measurableSet_lt measurable_const measurable_fst)).mpr
    filter_upwards [hfirst] with p hp
    exact hp.1
  have hηpos : ∀ᵐ z ∂η, 0 < z.1 := by
    apply (ae_map_iff hY.aemeasurable (measurableSet_lt measurable_const measurable_fst)).mpr
    filter_upwards [hlast] with p hp
    exact hp.2
  have hμzero : ∀ᵐ z ∂μ, -(z.2 0) = 0 := by
    apply (ae_map_iff hX.aemeasurable
      (measurableSet_eq_fun (((ContinuousMap.measurable_eval 0).comp measurable_snd).neg)
        measurable_const)).mpr
    filter_upwards [hfirst] with p hp
    change -(driftedBrownianPath ν p
      (firstPassageTime (driftedBrownianPath ν p) c-min 0 (firstPassageTime (driftedBrownianPath ν p) c))-c) = 0
    simp only [zero_min, tsub_zero, hp.2, sub_self, neg_zero]
  have hηzero : ∀ᵐ z ∂η, -(z.2 0) = 0 := by
    apply (ae_map_iff hY.aemeasurable
      (measurableSet_eq_fun (((ContinuousMap.measurable_eval 0).comp measurable_snd).neg)
        measurable_const)).mpr
    filter_upwards [hQν.2.2.1] with p hp
    change -(p (min 0 (negativeLastExitTime p c))) = 0
    simp only [zero_min, hp, neg_zero]
  have hmEnd : MeasurableSet {z : StoppedBrownianPath | ∀ t, z.1 ≤ t → -(z.2 t) = c} := by
    have hclosed : IsClosed {z : StoppedBrownianPath | ∀ t, z.1 ≤ t → -(z.2 t) = c} := by
      have heq : {z : StoppedBrownianPath | ∀ t, z.1 ≤ t → -(z.2 t) = c} =
          {z | z.2 = stopBrownianPath z.2 z.1 ∧ -(z.2 z.1) = c} := by
        ext z
        constructor
        · intro hz
          refine ⟨?_, hz z.1 le_rfl⟩
          ext t
          change z.2 t = z.2 (min t z.1)
          by_cases ht : t ≤ z.1
          · rw [min_eq_left ht]
          · rw [min_eq_right (not_le.mp ht).le]
            exact neg_injective ((hz t (not_le.mp ht).le).trans (hz z.1 le_rfl).symm)
        · rintro ⟨hstop, hend⟩ t ht
          have he := congrArg (fun p : BrownianPath => p t) hstop
          change z.2 t = z.2 (min t z.1) at he
          rw [min_eq_right ht] at he
          rwa [he]
      rw [heq]
      exact (isClosed_eq continuous_snd
        continuous_stopBrownianPath).inter
        (isClosed_eq (continuous_eval.comp (continuous_snd.prodMk continuous_fst)).neg continuous_const)
    exact hclosed.measurableSet
  have hμend : ∀ᵐ z ∂μ, ∀ t, z.1 ≤ t → -(z.2 t) = c := by
    apply (ae_map_iff hX.aemeasurable hmEnd).mpr
    filter_upwards [hP.eval_zero_ae_eq_zero] with p hp
    intro t ht
    change -(driftedBrownianPath ν p
      (firstPassageTime (driftedBrownianPath ν p) c-
        min t (firstPassageTime (driftedBrownianPath ν p) c))-c) = c
    change firstPassageTime (driftedBrownianPath ν p) c ≤ t at ht
    rw [min_eq_right ht, tsub_self]
    change -(p 0+ν*(0 : ℝ≥0)-c) = c
    simp only [hp, NNReal.coe_zero, mul_zero, zero_add, zero_sub, neg_neg]
  have hηend : ∀ᵐ z ∂η, ∀ t, z.1 ≤ t → -(z.2 t) = c := by
    apply (ae_map_iff hY.aemeasurable hmEnd).mpr
    filter_upwards [hlast] with p hp
    intro t ht
    change negativeLastExitTime p c ≤ t at ht
    change -(p (min t (negativeLastExitTime p c))) = c
    rw [min_eq_right ht, hp.1, neg_neg]
  exact hmark.measure_eq hμpos hηpos hμzero hηzero c hμend hηend

end DOZZ.Proofs
end

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Williams.ReversalMarkedRectangles
public import DOZZ.Brownian.Williams.MarkedMeasureUniqueness

/-!
# Equality of the lifetime-marked preterminal observation laws

The deterministic-time avoidance identity identifies the last-exit past density.
The first-hit reversal density has exactly the same factors after harmonic cancellation.
Thus every nonempty finite observation tuple, with its actual lifetime mark and retained
strictly before that lifetime, has the same measure under the two path laws.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
namespace DOZZ.Proofs

/-- Finite positive entrance observations with the actual last-exit lifetime. -/
noncomputable def conditionedLastExitMarkedObservation (c : ℝ) (n : ℕ)
    (ss : Fin (n+1) → ℝ≥0) (p : BrownianPath) : (Fin (n+1) → ℝ) × ℝ :=
  ((fun i => -(p (ss i))), (negativeLastExitTime p c : ℝ))

theorem measurable_conditionedLastExitMarkedObservation (c : ℝ) (n : ℕ)
    (ss : Fin (n+1) → ℝ≥0) : Measurable (conditionedLastExitMarkedObservation c n ss) :=
  (measurable_pi_iff.mpr fun _ => (ContinuousMap.measurable_eval _).neg).prodMk
    (NNReal.continuous_coe.measurable.comp (measurable_negativeLastExitTime_joint.comp
      (measurable_const.prodMk measurable_id)))

/-- The complete finite preterminal observation/lifetime laws coincide. -/
theorem brownian_firstHit_reversal_finite_marked_law
    (ν c : ℝ) (hν : 0 < ν) (hc : 0 < c) (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (Q : Measure BrownianPath)
    (hQ : IsNegativeConditionedBrownianLaw ν Q) (n : ℕ)
    (ss : Fin (n+1) → ℝ≥0) (hss : StrictMono ss) (hs0 : 0 < ss 0) :
    (P.restrict {p : BrownianPath | ss (Fin.last n) < firstPassageTime (driftedBrownianPath ν p) c}).map
      (brownianFirstHitReversedIncreasingObservation ν c n ss) =
    (Q.restrict {p : BrownianPath | ss (Fin.last n) < negativeLastExitTime p c}).map
      (conditionedLastExitMarkedObservation c n ss) := by
  let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let : IsProbabilityMeasure Q := hQ.2.1
  let T : BrownianPath → ℝ≥0 := fun p => firstPassageTime (driftedBrownianPath ν p) c
  let L : BrownianPath → ℝ≥0 := fun p => negativeLastExitTime p c
  let μ := (P.restrict {p | ss (Fin.last n) < T p}).map
    (brownianFirstHitReversedIncreasingObservation ν c n ss)
  let η := (Q.restrict {p | ss (Fin.last n) < L p}).map
    (conditionedLastExitMarkedObservation c n ss)
  have hmT : Measurable T := (measurable_firstPassageTime c).comp
    (continuous_brownianDriftPath.comp (continuous_const.prodMk continuous_id)).measurable
  have hmL : Measurable L := measurable_negativeLastExitTime_joint.comp
    (measurable_const.prodMk measurable_id)
  have hmμ := measurable_brownianFirstHitReversedIncreasingObservation ν c n ss
  have hmη := measurable_conditionedLastExitMarkedObservation c n ss
  have hsμ : ∀ᵐ z ∂μ, (ss (Fin.last n) : ℝ) < z.2 := by
    apply (ae_map_iff hmμ.aemeasurable
      (measurableSet_lt measurable_const measurable_snd)).mpr
    filter_upwards [ae_restrict_mem (measurableSet_lt measurable_const hmT)] with p hp
    exact NNReal.coe_lt_coe.mpr hp
  have hsη : ∀ᵐ z ∂η, (ss (Fin.last n) : ℝ) < z.2 := by
    apply (ae_map_iff hmη.aemeasurable
      (measurableSet_lt measurable_const measurable_snd)).mpr
    filter_upwards [ae_restrict_mem (measurableSet_lt measurable_const hmL)] with p hp
    exact NNReal.coe_lt_coe.mpr hp
  apply measure_eq_of_prod_Ioc_above μ η (ss (Fin.last n) : ℝ) hsμ hsη
  intro A hA a b ha hab
  have ha0 : 0 ≤ a := (NNReal.coe_nonneg _).trans ha.le
  have hb0 : 0 ≤ b := ha0.trans hab.le
  let u := Real.toNNReal a
  let v := Real.toNNReal b
  let cN := Real.toNNReal c
  have hu : ss (Fin.last n) < u := by
    apply NNReal.coe_lt_coe.mp
    simpa only [u, Real.coe_toNNReal _ ha0] using ha
  have huv : u ≤ v := Real.toNNReal_mono hab.le
  have hcN : 0 < (cN : ℝ) := by simpa only [cN, Real.coe_toNNReal _ hc.le] using hc
  have htimes (i : Fin (n+1)) : 0 < (ss i : ℝ) :=
    NNReal.coe_pos.mpr (hs0.trans_le (hss.monotone (Fin.zero_le i)))
  have hηrect : η.real (A ×ˢ Ioc a b) =
      Q.real {p : BrownianPath | (fun i => -(p (ss i))) ∈ A ∧
        negativeLastExitTime p c ∈ Ioc u v} := by
    have hE : MeasurableSet (conditionedLastExitMarkedObservation c n ss ⁻¹' (A ×ˢ Ioc a b)) :=
      (hA.prod measurableSet_Ioc).preimage hmη
    have he : (conditionedLastExitMarkedObservation c n ss ⁻¹' (A ×ˢ Ioc a b)) ∩
        {p | ss (Fin.last n) < L p} =
        {p : BrownianPath | (fun i => -(p (ss i))) ∈ A ∧ negativeLastExitTime p c ∈ Ioc u v} := by
      ext p
      have hau : (u : ℝ) = a := Real.coe_toNNReal _ ha0
      have hbv : (v : ℝ) = b := Real.coe_toNNReal _ hb0
      rw [← hau, ← hbv]
      simp only [mem_inter_iff, mem_preimage, mem_prod, mem_Ioc,
        conditionedLastExitMarkedObservation, mem_ofPred_eq, NNReal.coe_lt_coe,
        NNReal.coe_le_coe, L]
      constructor
      · rintro ⟨⟨hp, hlow, hhigh⟩, _⟩
        exact ⟨hp, hlow, hhigh⟩
      · rintro ⟨hp, hlow, hhigh⟩
        exact ⟨⟨hp, hlow, hhigh⟩, hu.trans hlow⟩
    unfold Measure.real
    change ((Q.restrict {p | ss (Fin.last n) < L p}).map
      (conditionedLastExitMarkedObservation c n ss) (A ×ˢ Ioc a b)).toReal = _
    rw [Measure.map_apply hmη (hA.prod measurableSet_Ioc), Measure.restrict_apply hE, he]
  have hlast := negativeConditionedLaw_finitePast_lastExit_Ioc hQ hB hν cN hcN n ss htimes hss u v hu huv A hA
  simp only [cN, Real.coe_toNNReal _ hc.le, u, v, Real.coe_toNNReal _ ha0,
    Real.coe_toNNReal _ hb0] at hlast
  have hreal : μ.real (A ×ˢ Ioc a b) = η.real (A ×ˢ Ioc a b) := by
    rw [brownianPath_firstHit_reversedIncreasing_rectangle P hB ν c hν hc n ss hss hs0 A hA a b,
      hηrect, hlast]
  have heq := congrArg ENNReal.ofReal hreal
  simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)] using heq

end DOZZ.Proofs
end

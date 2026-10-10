/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitPastCDF

/-!
# Last-exit density with finite past observations

Taking increments of the deterministic-time last-exit CDF identifies the joint lifetime density
while retaining every measurable finite past cylinder.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
namespace DOZZ.Proofs

/-- The joint finite-past and last-exit lifetime law on every interval beyond the last observation.
The final factor is the boundary density from Lemma `lem:last-density`. -/
theorem negativeConditionedLaw_finitePast_lastExit_Ioc
    {ν : ℝ} {P B : Measure BrownianPath} [SFinite B]
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (hB : IsBrownianReal (fun t p => p t) B)
    (hν : 0 < ν) (c : ℝ≥0) (hc : 0 < (c : ℝ))
    (k : ℕ) (ss : Fin (k+1) → ℝ≥0) (hs : ∀ i, 0 < (ss i : ℝ))
    (hmono : StrictMono ss) (u v : ℝ≥0) (hu : ss (Fin.last k) < u) (huv : u ≤ v)
    (A : Set (Fin (k+1) → ℝ)) (hA : MeasurableSet A) :
    P.real {p : BrownianPath | (fun i => -(p (ss i))) ∈ A ∧
      negativeLastExitTime p (c : ℝ) ∈ Ioc u v} =
      ∫ x in A, ∫ t in Ioc (u : ℝ) (v : ℝ),
        conditionedPositiveTransitionDensity ν (t-(ss (Fin.last k) : ℝ))
          (x (Fin.last k)) (c : ℝ) * ν / conditionedH ν (c : ℝ)
        ∂(volume : Measure ℝ)
        ∂(volume : Measure (Fin (k+1) → ℝ)).withDensity
          (conditionedPositiveFDDVectorDensity ν (fun i => (ss i : ℝ))) := by
  let : IsProbabilityMeasure P := hP.2.1
  let evalPast : BrownianPath → (Fin (k+1) → ℝ) := fun p i => -(p (ss i))
  let μ : Measure (Fin (k+1) → ℝ) := volume.withDensity
    (conditionedPositiveFDDVectorDensity ν (fun i => (ss i : ℝ)))
  let E : ℝ≥0 → Set BrownianPath := fun w =>
    {p | evalPast p ∈ A ∧ negativeLastExitTime p (c : ℝ) ≤ w}
  have hmPast : Measurable evalPast :=
    measurable_pi_iff.mpr fun _ => (ContinuousMap.measurable_eval _).neg
  have hmτ : Measurable (fun p : BrownianPath => negativeLastExitTime p (c : ℝ)) :=
    measurable_negativeLastExitTime_joint.comp (measurable_const.prodMk measurable_id)
  have hE (w : ℝ≥0) : MeasurableSet (E w) :=
    (hA.preimage hmPast).inter ((measurableSet_Iic (a := w)).preimage hmτ)
  have hpastLaw : P.map evalPast = μ :=
    negativeConditionedLaw_positiveFDD hP (k+1) (by omega) ss hs hmono
  have : IsProbabilityMeasure μ := by
    rw [← hpastLaw]
    exact (Measure.isProbabilityMeasure_map_iff hmPast.aemeasurable).mpr inferInstance
  have hxpos : ∀ᵐ x ∂μ, 0 < x (Fin.last k) := by
    rw [← hpastLaw]
    exact (ae_map_iff hmPast.aemeasurable
      (measurableSet_lt measurable_const (measurable_pi_apply _))).2
        (conditionedPositiveStateAt_pos_ae hP (ss (Fin.last k)) (hs (Fin.last k)))
  have hi (w : ℝ≥0) (hw : ss (Fin.last k) < w) :
      Integrable (fun x => lastExitGaussianKernelCDF ν (c : ℝ) (x (Fin.last k))
        ((w : ℝ)-(ss (Fin.last k) : ℝ))) μ := by
    have hm : Measurable (fun x : Fin (k+1) → ℝ => lastExitGaussianKernelCDF ν (c : ℝ)
        (x (Fin.last k)) ((w : ℝ)-(ss (Fin.last k) : ℝ))) :=
      (measurable_lastExitGaussianKernelCDF_state ν (c : ℝ)
        ((w : ℝ)-(ss (Fin.last k) : ℝ))).comp (measurable_pi_apply (Fin.last k))
    apply Integrable.mono' (integrable_const (1 : ℝ)) hm.aestronglyMeasurable
    filter_upwards [hxpos] with x hx
    have hb := lastExitGaussianKernelCDF_bounds ν (c : ℝ) (x (Fin.last k)) _ hν hc hx
      (sub_pos.mpr (NNReal.coe_lt_coe.mpr hw))
    rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact hb.2
  have hdiff : {p : BrownianPath | evalPast p ∈ A ∧ negativeLastExitTime p (c : ℝ) ∈ Ioc u v} =
      E v \ E u := by
    ext p
    simp only [E, mem_ofPred_eq, Set.mem_sdiff, mem_Ioc]
    constructor
    · rintro ⟨hA, huL, hLv⟩
      exact ⟨⟨hA,hLv⟩, fun h => (not_le_of_gt huL) h.2⟩
    · rintro ⟨⟨hA,hLv⟩, hnot⟩
      exact ⟨hA, lt_of_not_ge (fun hLu => hnot ⟨hA,hLu⟩), hLv⟩
  have hsub : E u ⊆ E v := fun p hp => ⟨hp.1, hp.2.trans huv⟩
  have hv : ss (Fin.last k) < v := hu.trans_le huv
  calc
    _ = P.real (E v) - P.real (E u) := by
      rw [hdiff, measureReal_sdiff hsub (hE u) (measure_ne_top _ _)]
    _ = (∫ x in A, lastExitGaussianKernelCDF ν (c : ℝ) (x (Fin.last k))
          ((v : ℝ)-(ss (Fin.last k) : ℝ)) ∂μ) -
        ∫ x in A, lastExitGaussianKernelCDF ν (c : ℝ) (x (Fin.last k))
          ((u : ℝ)-(ss (Fin.last k) : ℝ)) ∂μ := by
      rw [negativeConditionedLaw_finitePast_lastExit_CDF hP hB hν c hc k ss hs hmono v hv A hA,
        negativeConditionedLaw_finitePast_lastExit_CDF hP hB hν c hc k ss hs hmono u hu A hA]
    _ = ∫ x in A, lastExitGaussianKernelCDF ν (c : ℝ) (x (Fin.last k))
          ((v : ℝ)-(ss (Fin.last k) : ℝ)) -
        lastExitGaussianKernelCDF ν (c : ℝ) (x (Fin.last k))
          ((u : ℝ)-(ss (Fin.last k) : ℝ)) ∂μ :=
      (integral_sub (hi v hv).integrableOn (hi u hu).integrableOn).symm
    _ = _ := by
      apply setIntegral_congr_ae hA
      filter_upwards [hxpos] with x hx _
      exact (integral_lastExit_boundaryDensity_shifted_Ioc ν (c : ℝ) (x (Fin.last k))
        (ss (Fin.last k) : ℝ) (u : ℝ) (v : ℝ) hν hc hx
        (NNReal.coe_lt_coe.mpr hu) (NNReal.coe_le_coe.mpr huv)).symm

end DOZZ.Proofs

end

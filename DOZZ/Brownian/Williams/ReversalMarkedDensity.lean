/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Williams.ReversalDensityCancellation
public import DOZZ.Brownian.LastExitPastDensity

/-!
# Increasing-order marked reversal density

Reindexing the proved first-hit reversal law by the finite coordinate reversal preserves
Lebesgue measure. The resulting density uses the same observation order as the conditioned
last-exit law.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Set Function
open scoped NNReal ENNReal
namespace DOZZ.Proofs

/-- Reversed first-hit observations in increasing reversed-time order, with the lifetime mark. -/
noncomputable def brownianFirstHitReversedIncreasingObservation (ν c : ℝ) (n : ℕ)
    (ss : Fin (n+1) → ℝ≥0) (p : BrownianPath) : (Fin (n+1) → ℝ) × ℝ :=
  ((fun i => c-(p (firstPassageTime (driftedBrownianPath ν p) c-ss i)+
    ν*((firstPassageTime (driftedBrownianPath ν p) c-ss i : ℝ≥0) : ℝ))),
    (firstPassageTime (driftedBrownianPath ν p) c : ℝ))

/-- Joint measurability of the increasing-order observation and its lifetime. -/
theorem measurable_brownianFirstHitReversedIncreasingObservation (ν c : ℝ) (n : ℕ)
    (ss : Fin (n+1) → ℝ≥0) :
    Measurable (brownianFirstHitReversedIncreasingObservation ν c n ss) := by
  have hτ : Measurable (fun p : BrownianPath => firstPassageTime (driftedBrownianPath ν p) c) :=
    (measurable_firstPassageTime c).comp
      (continuous_brownianDriftPath.comp (continuous_const.prodMk continuous_id)).measurable
  apply Measurable.prodMk _ (NNReal.continuous_coe.measurable.comp hτ)
  apply measurable_pi_iff.mpr
  intro i
  have ht := hτ.sub (measurable_const (a := ss i))
  exact measurable_const.sub ((continuous_eval.measurable.comp (measurable_id.prodMk ht)).add
    (measurable_const.mul (NNReal.continuous_coe.measurable.comp ht)))

/-- Joint measurability of a conditioned transition in elapsed time and starting state. -/
theorem measurable_conditionedPositiveTransitionDensity_time_start (ν c : ℝ) :
    Measurable (fun z : ℝ × ℝ => conditionedPositiveTransitionDensity ν z.1 z.2 c) := by
  classical
  have hh : Measurable (fun z : ℝ × ℝ => conditionedH ν z.2) :=
    (measurable_conditionedH_ref ν).comp measurable_snd
  have hg : MeasurableSet {z : ℝ × ℝ | 0 ≤ ν ∧ 0 < z.1 ∧ 0 < z.2 ∧ 0 < c} := by
    by_cases hν : 0 ≤ ν
    · by_cases hc : 0 < c
      · simpa only [hν, hc, true_and, and_true, Set.ofPred_and] using
          (measurableSet_lt measurable_const measurable_fst).inter
            (measurableSet_lt measurable_const measurable_snd)
      · simp [hc]
    · simp [hν]
  have hheat (f : ℝ × ℝ → ℝ) (hf : Measurable f) :
      Measurable (fun z => brownianHeatDensity z.1 (f z)) := by
    unfold brownianHeatDensity
    apply Measurable.ite (measurableSet_lt measurable_const measurable_fst) _ measurable_const
    exact (Real.measurable_exp.comp ((hf.pow_const 2).neg.div
      (measurable_const.mul measurable_fst))).div
      (Real.continuous_sqrt.measurable.comp (measurable_const.mul measurable_fst))
  unfold conditionedPositiveTransitionDensity
  apply Measurable.ite hg _ measurable_const
  exact (((Real.measurable_exp.comp ((measurable_const.mul (measurable_const.sub measurable_snd)).sub
    ((measurable_const.mul measurable_fst).div_const 2))).mul
    ((hheat _ (measurable_const.sub measurable_snd)).sub
      (hheat _ (measurable_const.add measurable_snd)))).mul measurable_const).div hh

/-- Last-exit boundary density for a finite observed past. -/
noncomputable def brownianReversalBoundaryDensity (ν c : ℝ) (n : ℕ)
    (ss : Fin (n+1) → ℝ≥0) (z : (Fin (n+1) → ℝ) × ℝ) : ℝ :=
  conditionedPositiveTransitionDensity ν (z.2-(ss (Fin.last n) : ℝ))
    (z.1 (Fin.last n)) c * ν / conditionedH ν c

theorem measurable_brownianReversalBoundaryDensity (ν c : ℝ) (n : ℕ)
    (ss : Fin (n+1) → ℝ≥0) : Measurable (brownianReversalBoundaryDensity ν c n ss) :=
  (((measurable_conditionedPositiveTransitionDensity_time_start ν c).comp
    ((measurable_snd.sub measurable_const).prodMk
      ((measurable_pi_apply _).comp measurable_fst))).mul_const ν).div_const _

/-- The first-hit reversed marked law, in precisely the increasing observation order of the
conditioned last-exit FDD, has the entrance density times its boundary density. -/
theorem brownianPath_firstHit_reversedIncreasing_density_map (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν c : ℝ) (hν : 0 < ν) (hc : 0 < c)
    (n : ℕ) (ss : Fin (n+1) → ℝ≥0) (hss : StrictMono ss) (hs0 : 0 < ss 0) :
    (P.restrict {p : BrownianPath | ss (Fin.last n) < firstPassageTime (driftedBrownianPath ν p) c}).map
      (brownianFirstHitReversedIncreasingObservation ν c n ss) =
      ((((volume : Measure (Fin (n+1) → ℝ)).withDensity
        (conditionedPositiveFDDVectorDensity ν (fun i => (ss i : ℝ)))).prod volume).restrict
        {z : (Fin (n+1) → ℝ) × ℝ | (ss (Fin.last n) : ℝ) < z.2}).withDensity
          (fun z => ENNReal.ofReal (brownianReversalBoundaryDensity ν c n ss z)) := by
  let e : ((Fin (n+1) → ℝ) × ℝ) ≃ᵐ ((Fin (n+1) → ℝ) × ℝ) :=
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (n+1) => ℝ) (Fin.revPerm)).prodCongr
      (MeasurableEquiv.refl ℝ)
  have he (z : (Fin (n+1) → ℝ) × ℝ) : e z = ((fun i => z.1 i.rev),z.2) := by
    apply Prod.ext
    · funext i
      change (MeasurableEquiv.piCongrLeft (fun _ : Fin (n+1) => ℝ) Fin.revPerm) z.1 i = _
      simpa only [Fin.revPerm_apply, Fin.rev_rev] using
        MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin (n+1) => ℝ) Fin.revPerm z.1 i.rev
    · rfl
  have he' (z : (Fin (n+1) → ℝ) × ℝ) : e.symm z = ((fun i => z.1 i.rev),z.2) := by
    apply e.injective
    rw [e.apply_symm_apply, he]
    simp only [Fin.rev_rev]
  have hv : MeasurePreserving e (volume.prod volume) (volume.prod volume) :=
    (volume_measurePreserving_piCongrLeft (fun _ : Fin (n+1) => ℝ) Fin.revPerm).prod
      (MeasurePreserving.id (volume : Measure ℝ))
  let D := {z : (Fin (n+1) → ℝ) × ℝ | (ss (Fin.last n) : ℝ) < z.2}
  have hD : MeasurableSet D := measurableSet_lt measurable_const measurable_snd
  have hvD : MeasurePreserving e ((volume.prod volume).restrict D)
      ((volume.prod volume).restrict D) := by
    convert hv.restrict_preimage hD using 1
    congr 1
  have hm : Measurable (brownianFirstHitReversedObservation ν c n ss) := by
    have hcomp : brownianFirstHitReversedObservation ν c n ss =
        e ∘ brownianFirstHitReversedIncreasingObservation ν c n ss := by
      funext p
      simp only [comp_apply, he, brownianFirstHitReversedIncreasingObservation,
        brownianFirstHitReversedObservation]
    rw [hcomp]
    exact e.measurable.comp (measurable_brownianFirstHitReversedIncreasingObservation ν c n ss)
  have hobs : brownianFirstHitReversedIncreasingObservation ν c n ss =
      e ∘ brownianFirstHitReversedObservation ν c n ss := by
    funext p
    simp only [comp_apply, he, brownianFirstHitReversedIncreasingObservation,
      brownianFirstHitReversedObservation, Fin.rev_rev]
  have hd := measurable_brownianFirstHitReversedPDF ν c n ss
  rw [hobs, ← Measure.map_map e.measurable hm,
    brownianPath_firstHit_reversed_observation_density_map P hB ν c hν hc n ss hss hs0,
    map_withDensity_of_measurePreserving_equiv e _ _ hvD _ hd,
    prod_withDensity_left (measurable_conditionedPositiveFDDVectorDensity ν _),
    restrict_withDensity hD]
  rw [← withDensity_mul _
    (show Measurable (fun z : (Fin (n+1) → ℝ) × ℝ =>
      conditionedPositiveFDDVectorDensity ν (fun i => (ss i : ℝ)) z.1) from
      (measurable_conditionedPositiveFDDVectorDensity ν _).comp measurable_fst)
    (measurable_brownianReversalBoundaryDensity ν c n ss).ennreal_ofReal]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem hD] with z hz
  rw [comp_apply, brownianFirstHitReversedPDF_eq_lastExitDensity ν c hν hc n ss hss hs0
    (e.symm z) (by simpa only [he', D, mem_ofPred_eq] using hz)]
  simp only [he', Fin.rev_rev, Fin.rev_zero]
  have hp := conditionedPositiveFDDDensity_nonneg hν.le
    (List.ofFn fun i => (ss i : ℝ)) (List.ofFn z.1) (by simp)
  simp only [conditionedPositiveFDDVectorDensity, max_eq_right hp,
    brownianReversalBoundaryDensity, Pi.mul_apply]
  rw [← ENNReal.ofReal_mul hp]
  congr 1
  ring

/-- The boundary density is nonnegative everywhere; invalid elapsed times and states give zero. -/
theorem brownianReversalBoundaryDensity_nonneg (ν c : ℝ) (hν : 0 < ν) (hc : 0 < c)
    (n : ℕ) (ss : Fin (n+1) → ℝ≥0) (z : (Fin (n+1) → ℝ) × ℝ) :
    0 ≤ brownianReversalBoundaryDensity ν c n ss z := by
  have hh : 0 < conditionedH ν c := by
    rw [conditionedH, ite_eq_right hν.ne']
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith only [hν, hc]))
  by_cases ht : 0 < z.2-(ss (Fin.last n) : ℝ)
  · by_cases hx : 0 < z.1 (Fin.last n)
    · exact div_nonneg (mul_nonneg
        (conditionedPositiveTransitionDensity_nonneg hν.le ht hx c) hν.le) hh.le
    · simp [brownianReversalBoundaryDensity, conditionedPositiveTransitionDensity, hx]
  · simp [brownianReversalBoundaryDensity, conditionedPositiveTransitionDensity, ht]

/-- The final boundary factor itself enforces the lifetime cutoff. -/
theorem brownianPath_firstHit_reversedIncreasing_density_map_unrestricted
    (P : Measure BrownianPath) (hB : IsBrownianReal (fun t p => p t) P)
    (ν c : ℝ) (hν : 0 < ν) (hc : 0 < c) (n : ℕ)
    (ss : Fin (n+1) → ℝ≥0) (hss : StrictMono ss) (hs0 : 0 < ss 0) :
    (P.restrict {p : BrownianPath | ss (Fin.last n) < firstPassageTime (driftedBrownianPath ν p) c}).map
      (brownianFirstHitReversedIncreasingObservation ν c n ss) =
      (((volume : Measure (Fin (n+1) → ℝ)).withDensity
        (conditionedPositiveFDDVectorDensity ν (fun i => (ss i : ℝ)))).prod volume).withDensity
          (fun z => ENNReal.ofReal (brownianReversalBoundaryDensity ν c n ss z)) := by
  rw [brownianPath_firstHit_reversedIncreasing_density_map P hB ν c hν hc n ss hss hs0,
    ← restrict_withDensity (measurableSet_lt measurable_const measurable_snd)]
  apply Measure.restrict_eq_self_of_ae_mem
  apply (ae_withDensity_iff
    (measurable_brownianReversalBoundaryDensity ν c n ss).ennreal_ofReal).mpr
  apply ae_of_all
  intro z hz
  by_contra hnot
  change ¬ (ss (Fin.last n) : ℝ) < z.2 at hnot
  have ht : ¬ 0 < z.2-(ss (Fin.last n) : ℝ) := by
    simpa only [sub_pos] using hnot
  apply hz
  simp only [brownianReversalBoundaryDensity, conditionedPositiveTransitionDensity,
    ht, false_and, and_false, ite_false, zero_mul, zero_div, ENNReal.ofReal_zero]

end DOZZ.Proofs
end

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Brownian.Barrier.FirstHitJoint
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Order.Fin.Tuple

/-!
# Actual finite-dimensional first-hit laws with the lifetime mark

Finite positive elapsed times give strictly ordered positive observation
horizons. The remaining-level samples split pointwise into the first state
and the samples of the shifted full future. The whole actual marked finite
observation map is jointly measurable in the starting level and path.

The first-hit state/full-future law is the negative-drift killed-state density
multiplied by the original Brownian future law. It follows from the raw-past
restart and the actual one-step surviving state measure; no conditional path
law is assumed. The shifted clock identity splits the pre-hit event at the
complete observation horizon into its first-step pre-hit event and its
future pre-hit event, including the absolute lifetime mark.

Induction over the number of observations identifies every nonnegative
measurable finite observation/lifetime test with the iterated killed/hitting
integral. The base case is the actual full hitting density, including the
positive-lifetime boundary. Every subsequent step uses the actual state and
full-future law. Measurability of the iterated integral is proved with an
arbitrary external measurable parameter so later state integrations retain
all their earlier observations.

The observation times lie below the final horizon, which equals their last
observation time and the sum of the elapsed times. Every observed remaining
level is positive on the pre-hit event. The resulting finite marked measure
has exactly the actual survival mass. Its tests preserve order and every
bounded test is bounded by the same constant.

These are the actual deterministic finite marked laws needed by the ceiling
reversal argument. Passing from deterministic samples to samples indexed by
the random lifetime and identifying the conditioned last-exit marked law are
separate assembly steps, and neither is asserted by this module.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
namespace DOZZ.Proofs

/-- Absolute observation times obtained from a finite tuple of elapsed times. -/
def brownianFirstHitTimes : (n : ℕ) → (Fin n → ℝ≥0) → Fin n → ℝ≥0
  | 0, _ => fun i => Fin.elim0 i
  | n+1, ds => Fin.cons (ds 0) (fun i => ds 0+brownianFirstHitTimes n (Fin.tail ds) i)

/-- The horizon of a finite tuple of elapsed times. -/
def brownianFirstHitHorizon : (n : ℕ) → (Fin n → ℝ≥0) → ℝ≥0
  | 0, _ => 0
  | n+1, ds => ds 0+brownianFirstHitHorizon n (Fin.tail ds)

/-- Remaining-level samples at all the finite deterministic observation times. -/
def brownianFirstHitSamples (n : ℕ) (ds : Fin n → ℝ≥0) (a c : ℝ) (p : BrownianPath) : Fin n → ℝ :=
  fun i => c-(p (brownianFirstHitTimes n ds i)+a*(brownianFirstHitTimes n ds i : ℝ))

/-- Joint measurability of the actual finite sample tuple in the starting level and path. -/
theorem measurable_brownianFirstHitSamples (n : ℕ) (ds : Fin n → ℝ≥0) (a : ℝ) :
    Measurable (fun z : ℝ × BrownianPath => brownianFirstHitSamples n ds a z.1 z.2) := by
  apply measurable_pi_iff.mpr
  intro i
  exact measurable_fst.sub (((ContinuousMap.measurable_eval _).comp measurable_snd).add measurable_const)

/-- Inserting a scalar at the beginning of a finite real tuple is jointly measurable. -/
theorem measurable_fin_cons_real (n : ℕ) :
    Measurable (fun z : ℝ × (Fin n → ℝ) => Fin.cons (α := fun _ : Fin (n+1) => ℝ) z.1 z.2) := by
  apply measurable_pi_iff.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact measurable_fst
  · exact (measurable_pi_apply j).comp measurable_snd

/-- The actual deterministic sample tuple splits into the first remaining level and shifted future samples. -/
theorem brownianFirstHitSamples_cons (n : ℕ) (ds : Fin (n+1) → ℝ≥0) (a c : ℝ) (p : BrownianPath) :
    brownianFirstHitSamples (n+1) ds a c p = Fin.cons (c-(p (ds 0)+a*(ds 0 : ℝ)))
      (brownianFirstHitSamples n (Fin.tail ds) a (c-(p (ds 0)+a*(ds 0 : ℝ))) (brownianShiftPath (ds 0) p)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [brownianFirstHitSamples,brownianFirstHitTimes,Fin.cons_zero]
  · simp only [brownianFirstHitSamples,brownianFirstHitTimes,Fin.cons_succ]
    change c-(p (ds 0+brownianFirstHitTimes n (Fin.tail ds) j)+
      a*((ds 0+brownianFirstHitTimes n (Fin.tail ds) j : ℝ≥0) : ℝ)) =
      (c-(p (ds 0)+a*(ds 0 : ℝ)))-((p (ds 0+brownianFirstHitTimes n (Fin.tail ds) j)-p (ds 0))+
        a*(brownianFirstHitTimes n (Fin.tail ds) j : ℝ))
    push_cast
    ring_nf

/-- The killed/hitting iterated integral for a finite deterministic sample tuple and its absolute lifetime. -/
noncomputable def brownianFirstHitFiniteIntegral (a : ℝ) :
    (n : ℕ) → (Fin n → ℝ≥0) → ℝ → (((Fin n → ℝ) × ℝ) → ℝ≥0∞) → ℝ≥0∞
  | 0, _, c, H => ∫⁻ t, ENNReal.ofReal (brownianFirstHitDensity a c t)*H ((fun i : Fin 0 => Fin.elim0 i),t)
  | n+1, ds, c, H => ∫⁻ y, ENNReal.ofReal (brownianKilledTransitionPDF (-a) (ds 0) c y)*
      brownianFirstHitFiniteIntegral a n (Fin.tail ds) y
        (fun z => H (Fin.cons y z.1,(ds 0 : ℝ)+z.2))


/-- The actual pre-hit remaining state and full Brownian future have the killed-state density times the original future path law. -/
theorem brownianPath_firstHit_state_future_lintegral (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (s : ℝ≥0) (hs : s ≠ 0) (J : ℝ × BrownianPath → ℝ≥0∞) (hJ : Measurable J) :
    (∫⁻ p in {p : BrownianPath | s < firstPassageTime (driftedBrownianPath a p) c},
      J (c-(p s+a*(s : ℝ)),brownianShiftPath s p) ∂P) =
      ∫⁻ y, ENNReal.ofReal (brownianKilledTransitionPDF (-a) s c y)*∫⁻ q, J (y,q) ∂P := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hX : Measurable[brownianRawFiltration (fun u (p : BrownianPath) => p u)
      (fun u => ContinuousMap.measurable_eval u) s] (fun p => c-(p s+a*(s : ℝ))) :=
    measurable_const.sub ((measurable_brownianPath_eval_raw s s le_rfl).add measurable_const)
  rw [Measure.restrict_congr_set (brownianPath_positiveDrift_firstHit_event_ae P hB a c ha hc s hs)]
  calc
    _ = ∫⁻ p in {p : BrownianPath | ∀ u : ℝ≥0, u ≤ s → p u+a*(u : ℝ) ≤ c},
        ∫⁻ q, J (c-(p s+a*(s : ℝ)),q) ∂P ∂P :=
      brownianPath_past_event_restart_lintegral P hB s _
        (measurableSet_brownianPath_drift_barrier_raw a c s) _ hX J hJ
    _ = _ := brownianPath_upperKilled_remaining_lintegral P hB a c hc s hs
      (fun y => ∫⁻ q, J (y,q) ∂P) (Measurable.lintegral_prod_right (f := fun y q => J (y,q)) hJ)

/-- The actual finite sample tuple and first-hit lifetime are jointly measurable in level and path. -/
theorem measurable_brownianFirstHitObservation (n : ℕ) (ds : Fin n → ℝ≥0) (a : ℝ) :
    Measurable (fun z : ℝ × BrownianPath =>
      (brownianFirstHitSamples n ds a z.1 z.2,(firstPassageTime (driftedBrownianPath a z.2) z.1 : ℝ))) :=
  (measurable_brownianFirstHitSamples n ds a).prodMk
    (NNReal.continuous_coe.measurable.comp (measurable_firstPassageTime_drift_joint a))

/-- Prepending a sampled state and translating the lifetime clock is jointly measurable. -/
theorem measurable_brownianFirstHit_prepend (n : ℕ) (s : ℝ≥0) :
    Measurable (fun z : ℝ × ((Fin n → ℝ) × ℝ) =>
      (Fin.cons (α := fun _ : Fin (n+1) => ℝ) z.1 z.2.1,(s : ℝ)+z.2.2)) := by
  exact ((measurable_fin_cons_real n).comp
    (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
    (measurable_const.add (measurable_snd.comp measurable_snd))

/-- Finite future observations retained only before their last horizon form a jointly measurable test. -/
theorem measurable_brownianFirstHit_future_test (n : ℕ) (ds : Fin n → ℝ≥0) (a : ℝ) (s : ℝ≥0)
    (H : ((Fin (n+1) → ℝ) × ℝ) → ℝ≥0∞) (hH : Measurable H) :
    Measurable (fun z : ℝ × BrownianPath =>
      if brownianFirstHitHorizon n ds < firstPassageTime (driftedBrownianPath a z.2) z.1 then
        H (Fin.cons z.1 (brownianFirstHitSamples n ds a z.1 z.2),
          (s : ℝ)+(firstPassageTime (driftedBrownianPath a z.2) z.1 : ℝ)) else 0) := by
  classical
  apply Measurable.ite (measurableSet_lt measurable_const (measurable_firstPassageTime_drift_joint a))
  · exact (hH.comp (measurable_brownianFirstHit_prepend n s)).comp
      (measurable_fst.prodMk (measurable_brownianFirstHitObservation n ds a))
  · exact measurable_const

/-- The finite marked observation test at the whole horizon splits almost surely into the pre-hit first-step event and the actual future marked test. -/
theorem brownianFirstHit_observation_split_ae (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a c : ℝ) (ha : 0 < a)
    (n : ℕ) (ds : Fin (n+1) → ℝ≥0) (H : ((Fin (n+1) → ℝ) × ℝ) → ℝ≥0∞) :
    (fun p => if brownianFirstHitHorizon (n+1) ds < firstPassageTime (driftedBrownianPath a p) c then
      H (brownianFirstHitSamples (n+1) ds a c p,(firstPassageTime (driftedBrownianPath a p) c : ℝ)) else 0) =ᵐ[P]
    (fun p => if ds 0 < firstPassageTime (driftedBrownianPath a p) c then
      if brownianFirstHitHorizon n (Fin.tail ds) <
          firstPassageTime (driftedBrownianPath a (brownianShiftPath (ds 0) p)) (c-(p (ds 0)+a*(ds 0 : ℝ))) then
        H (Fin.cons (c-(p (ds 0)+a*(ds 0 : ℝ)))
          (brownianFirstHitSamples n (Fin.tail ds) a (c-(p (ds 0)+a*(ds 0 : ℝ))) (brownianShiftPath (ds 0) p)),
          (ds 0 : ℝ)+(firstPassageTime (driftedBrownianPath a (brownianShiftPath (ds 0) p)) (c-(p (ds 0)+a*(ds 0 : ℝ))) : ℝ))
      else 0 else 0) := by
  classical
  filter_upwards [brownianPath_positiveDrift_firstHit_shift_ae P hB a c ha (ds 0)] with p hp
  by_cases hpre : ds 0 < firstPassageTime (driftedBrownianPath a p) c
  · have hc := hp hpre
    have hg : brownianFirstHitHorizon (n+1) ds < firstPassageTime (driftedBrownianPath a p) c ↔
        brownianFirstHitHorizon n (Fin.tail ds) <
          firstPassageTime (driftedBrownianPath a (brownianShiftPath (ds 0) p)) (c-(p (ds 0)+a*(ds 0 : ℝ))) := by
      rw [brownianFirstHitHorizon,hc]
      exact add_lt_add_iff_left _
    rw [ite_eq_left hpre]
    simp only [hg,brownianFirstHitSamples_cons]
    simp only [hc,NNReal.coe_add]
  · have hg : ¬ brownianFirstHitHorizon (n+1) ds < firstPassageTime (driftedBrownianPath a p) c := by
      intro hg
      have hh : ds 0 ≤ brownianFirstHitHorizon (n+1) ds := le_add_of_nonneg_right (show 0 ≤ brownianFirstHitHorizon n (Fin.tail ds) from zero_le)
      exact hpre (hh.trans_lt hg)
    simp only [ite_eq_right hpre,ite_eq_right hg]

/-- Every actual finite pre-hit sample tuple together with the absolute first-hit lifetime has the full iterated killed/hitting density law. -/
theorem brownianPath_firstHit_finite_lintegral (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (n : ℕ) (ds : Fin n → ℝ≥0) (hds : ∀ i, 0 < ds i)
    (H : ((Fin n → ℝ) × ℝ) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ p in {p : BrownianPath | brownianFirstHitHorizon n ds < firstPassageTime (driftedBrownianPath a p) c},
      H (brownianFirstHitSamples n ds a c p,(firstPassageTime (driftedBrownianPath a p) c : ℝ)) ∂P) =
      brownianFirstHitFiniteIntegral a n ds c H := by
  classical
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  induction n generalizing c with
  | zero =>
      have he : {p : BrownianPath | brownianFirstHitHorizon 0 ds < firstPassageTime (driftedBrownianPath a p) c} =ᵐ[P] univ := by
        filter_upwards [brownianPath_positiveDrift_firstHit_ae P hB a c ha hc] with p hp
        exact propext ⟨fun _ => mem_univ p,fun _ => hp.1⟩
      rw [Measure.restrict_congr_set he,Measure.restrict_univ]
      have hempty (p : BrownianPath) : brownianFirstHitSamples 0 ds a c p = (fun i : Fin 0 => (Fin.elim0 i : ℝ)) := by
        funext i
        exact Fin.elim0 i
      simp only [hempty,brownianFirstHitFiniteIntegral]
      exact brownianPath_positiveDrift_firstHit_density_lintegral P hB a c ha hc
        (fun t => H ((fun i : Fin 0 => (Fin.elim0 i : ℝ)),t))
        (hH.comp (show Measurable (fun t : ℝ => ((fun i : Fin 0 => (Fin.elim0 i : ℝ)),t)) from
          measurable_const.prodMk measurable_id))
  | succ n ih =>
      let J : ℝ × BrownianPath → ℝ≥0∞ := fun z =>
        if brownianFirstHitHorizon n (Fin.tail ds) < firstPassageTime (driftedBrownianPath a z.2) z.1 then
          H (Fin.cons z.1 (brownianFirstHitSamples n (Fin.tail ds) a z.1 z.2),
            (ds 0 : ℝ)+(firstPassageTime (driftedBrownianPath a z.2) z.1 : ℝ)) else 0
      have hJ : Measurable J := measurable_brownianFirstHit_future_test n (Fin.tail ds) a (ds 0) H hH
      have hmτ : Measurable (fun p : BrownianPath => firstPassageTime (driftedBrownianPath a p) c) :=
        (measurable_firstPassageTime c).comp
          (continuous_driftedBrownianPath.measurable.comp (measurable_const.prodMk measurable_id))
      have hA : MeasurableSet {p : BrownianPath | brownianFirstHitHorizon (n+1) ds < firstPassageTime (driftedBrownianPath a p) c} :=
        measurableSet_lt measurable_const hmτ
      have hS : MeasurableSet {p : BrownianPath | ds 0 < firstPassageTime (driftedBrownianPath a p) c} :=
        measurableSet_lt measurable_const hmτ
      have hsplit : (∫⁻ p in {p : BrownianPath | brownianFirstHitHorizon (n+1) ds < firstPassageTime (driftedBrownianPath a p) c},
          H (brownianFirstHitSamples (n+1) ds a c p,(firstPassageTime (driftedBrownianPath a p) c : ℝ)) ∂P) =
          ∫⁻ p in {p : BrownianPath | ds 0 < firstPassageTime (driftedBrownianPath a p) c},
            J (c-(p (ds 0)+a*(ds 0 : ℝ)),brownianShiftPath (ds 0) p) ∂P := by
        rw [← lintegral_indicator hA,← lintegral_indicator hS]
        exact lintegral_congr_ae (brownianFirstHit_observation_split_ae P hB a c ha n ds H)
      rw [hsplit,brownianPath_firstHit_state_future_lintegral P hB a c ha hc (ds 0) (ne_of_gt (hds 0)) J hJ]
      change (∫⁻ y, ENNReal.ofReal (brownianKilledTransitionPDF (-a) (ds 0) c y)*∫⁻ q, J (y,q) ∂P) =
        ∫⁻ y, ENNReal.ofReal (brownianKilledTransitionPDF (-a) (ds 0) c y)*
          brownianFirstHitFiniteIntegral a n (Fin.tail ds) y (fun z => H (Fin.cons y z.1,(ds 0 : ℝ)+z.2))
      apply lintegral_congr
      intro y
      by_cases hy : 0 < y
      · congr 1
        have hqt : Measurable (fun q : BrownianPath => firstPassageTime (driftedBrownianPath a q) y) :=
          (measurable_firstPassageTime y).comp
            (continuous_driftedBrownianPath.measurable.comp (measurable_const.prodMk measurable_id))
        have he : (fun q => J (y,q)) =
            {q : BrownianPath | brownianFirstHitHorizon n (Fin.tail ds) < firstPassageTime (driftedBrownianPath a q) y}.indicator
              (fun q => H (Fin.cons y (brownianFirstHitSamples n (Fin.tail ds) a y q),
                (ds 0 : ℝ)+(firstPassageTime (driftedBrownianPath a q) y : ℝ))) := by
          funext q
          simp only [J,Set.indicator_apply,mem_ofPred_eq]
        rw [he,lintegral_indicator (measurableSet_lt measurable_const hqt)]
        exact ih y hy (Fin.tail ds) (fun i => hds i.succ)
          (fun z => H (Fin.cons y z.1,(ds 0 : ℝ)+z.2))
          ((hH.comp (measurable_brownianFirstHit_prepend n (ds 0))).comp
            (measurable_const.prodMk measurable_id))
      · simp only [brownianKilledTransitionPDF,hy,and_false,ite_false,ENNReal.ofReal_zero,zero_mul]

/-- Every deterministic observation time is bounded by the last observation horizon. -/
theorem brownianFirstHitTimes_le_horizon (n : ℕ) (ds : Fin n → ℝ≥0) (i : Fin n) :
    brownianFirstHitTimes n ds i ≤ brownianFirstHitHorizon n ds := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · change ds 0 ≤ ds 0+brownianFirstHitHorizon n (Fin.tail ds)
        exact le_add_of_nonneg_right (show 0 ≤ brownianFirstHitHorizon n (Fin.tail ds) from zero_le)
      · change ds 0+brownianFirstHitTimes n (Fin.tail ds) j ≤ ds 0+brownianFirstHitHorizon n (Fin.tail ds)
        simpa only [add_comm] using add_le_add_right (ih (Fin.tail ds) j) (ds 0)

/-- Positive elapsed times give positive deterministic observation times. -/
theorem brownianFirstHitTimes_pos (n : ℕ) (ds : Fin n → ℝ≥0) (hds : ∀ i, 0 < ds i) (i : Fin n) :
    0 < brownianFirstHitTimes n ds i := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
      refine Fin.cases (hds 0) (fun j => ?_) i
      exact (hds 0).trans_le (le_add_of_nonneg_right (show 0 ≤ brownianFirstHitTimes n (Fin.tail ds) j from zero_le))


/-- The last observation time is exactly the complete elapsed-time horizon. -/
theorem brownianFirstHitTimes_last (n : ℕ) (ds : Fin (n+1) → ℝ≥0) :
    brownianFirstHitTimes (n+1) ds (Fin.last n) = brownianFirstHitHorizon (n+1) ds := by
  induction n with
  | zero => simp only [brownianFirstHitTimes,brownianFirstHitHorizon,Fin.last_zero,Fin.cons_zero,add_zero]
  | succ n ih =>
      change ds 0+brownianFirstHitTimes (n+1) (Fin.tail ds) (Fin.last n) = ds 0+brownianFirstHitHorizon (n+1) (Fin.tail ds)
      rw [ih]

/-- The finite absolute observation times are strictly ordered when all elapsed times are positive. -/
theorem strictMono_brownianFirstHitTimes (n : ℕ) (ds : Fin n → ℝ≥0) (hds : ∀ i, 0 < ds i) :
    StrictMono (brownianFirstHitTimes n ds) := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      change StrictMono (Fin.cons (ds 0) (fun i => ds 0+brownianFirstHitTimes n (Fin.tail ds) i))
      rw [Fin.strictMono_cons]
      constructor
      · intro i
        have hp := brownianFirstHitTimes_pos n (Fin.tail ds) (fun j => hds j.succ) i
        exact lt_add_of_pos_right _ hp
      · intro i j hij
        simpa only [add_comm] using add_lt_add_right (ih (Fin.tail ds) (fun k => hds k.succ) hij) (ds 0)

/-- The finite killed/hitting iterated integral has exactly the actual pre-hit probability as its mass. -/
theorem brownianFirstHitFiniteIntegral_one (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (n : ℕ) (ds : Fin n → ℝ≥0) (hds : ∀ i, 0 < ds i) :
    brownianFirstHitFiniteIntegral a n ds c (fun _ => 1) =
      P {p : BrownianPath | brownianFirstHitHorizon n ds < firstPassageTime (driftedBrownianPath a p) c} := by
  have he := brownianPath_firstHit_finite_lintegral P hB a c ha hc n ds hds (fun _ => 1) measurable_const
  simpa only [lintegral_one,Measure.restrict_apply MeasurableSet.univ,univ_inter] using he.symm



/-- The literal finite sample/lifetime map is measurable on the original continuous-path carrier. -/
theorem measurable_brownianFirstHitObservation_fixed (n : ℕ) (ds : Fin n → ℝ≥0) (a c : ℝ) :
    Measurable (fun p : BrownianPath =>
      (brownianFirstHitSamples n ds a c p,(firstPassageTime (driftedBrownianPath a p) c : ℝ))) :=
  (measurable_brownianFirstHitObservation n ds a).comp (measurable_const.prodMk measurable_id)



end DOZZ.Proofs

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Brownian.Barrier.KilledMarkov

/-!
# Joint pre-hit states, lifetimes and raw pasts

A raw-past event can be retained in the deterministic full-future restart law.
The proof applies the actual product law to the observable together with its
event indicator, then uses Tonelli. Drifted barrier events belong to the raw
past. An actual finite first hit exceeds a horizon exactly when the whole
past is strictly below its level; maximum atomlessness identifies this event
with the closed barrier almost surely under the positive-drift Brownian law.

The surviving remaining level has the negative-drift killed transition
kernel. The shifted first-hit clock is jointly measurable in that level and
its actual future Brownian path. Restart at the deterministic horizon and the
proved full hitting density therefore identify the complete joint law of the
remaining level and the absolute lifetime. Both its nonnegative test identity
and its product-density pushforward are actual measure equalities.

The same argument retains every raw-past observable, including the entire
stopped continuous path, in the conditional remaining-lifetime identity.
All tests are nonnegative; no auxiliary integrability assumption is added.
Finite lifetime cells integrate the hitting density over the translated cell
while retaining every past test. This supplies actual cell identities for the
ceiling approximation rather than assuming a first-hit reversal law.

The joint density is supported on positive states and positive remaining
times. Its mass is exactly the actual pre-hit probability and hence at most
one. No assertion of Markov restart at a last exit is used here. Multi-time
killed paths and the reversed lifetime-marked limit remain to be assembled.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace DOZZ.Proofs

/-- Every raw-past event can be retained while integrating a jointly measurable past/future test. -/
theorem brownianPath_past_event_restart_lintegral {E : Type*} [MeasurableSpace E]
    (P : Measure BrownianPath) (hB : IsBrownianReal (fun t p => p t) P)
    (s : ℝ≥0) (A : Set BrownianPath)
    (hA : MeasurableSet[brownianRawFiltration (fun u (p : BrownianPath) => p u)
      (fun u => ContinuousMap.measurable_eval u) s] A)
    (X : BrownianPath → E)
    (hX : Measurable[brownianRawFiltration (fun u (p : BrownianPath) => p u)
      (fun u => ContinuousMap.measurable_eval u) s] X)
    (F : E × BrownianPath → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p in A, F (X p,brownianShiftPath s p) ∂P) =
      ∫⁻ p in A, ∫⁻ q, F (X p,q) ∂P ∂P := by
  classical
  let I : BrownianPath → ℝ≥0∞ := A.indicator (fun _ => 1)
  let J : (E × ℝ≥0∞) × BrownianPath → ℝ≥0∞ := fun z => z.1.2*F (z.1.1,z.2)
  have hJ : Measurable J := (measurable_snd.comp measurable_fst).mul
    (hF.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd))
  have hh := brownianPath_deterministic_restart_lintegral P hB s (fun p => (X p,I p))
    (hX.prodMk (measurable_const.indicator hA)) J hJ
  have hAg : MeasurableSet A := (brownianRawFiltration _ _).le s A hA
  have he (p : BrownianPath) (q : BrownianPath) : J ((X p,I p),q) = A.indicator (fun p => F (X p,q)) p := by
    by_cases hp : p ∈ A <;> simp only [J,I,Set.indicator_apply,hp,ite_true,ite_false,one_mul,zero_mul]
  have hl : (fun p => J ((X p,I p),brownianShiftPath s p)) = A.indicator
      (fun p => F (X p,brownianShiftPath s p)) := by
    funext p
    exact he p _
  have hr : (fun p => ∫⁻ q, J ((X p,I p),q) ∂P) = A.indicator
      (fun p => ∫⁻ q, F (X p,q) ∂P) := by
    funext p
    by_cases hp : p ∈ A
    · simp only [he,Set.indicator_apply,ite_eq_left hp]
    · simp only [he,Set.indicator_apply,ite_eq_right hp,lintegral_zero]
  rw [hl,hr,lintegral_indicator hAg,lintegral_indicator hAg] at hh
  exact hh

/-- A drifted upper barrier is measurable in the raw past of its finite horizon. -/
theorem measurableSet_brownianPath_drift_barrier_raw (a c : ℝ) (s : ℝ≥0) :
    MeasurableSet[brownianRawFiltration (fun u (p : BrownianPath) => p u)
      (fun u => ContinuousMap.measurable_eval u) s]
      {p : BrownianPath | ∀ u : ℝ≥0, u ≤ s → p u+a*(u : ℝ) ≤ c} := by
  have hm := (measurableSet_brownianPath_drift_barrier a c s).preimage (measurable_stopBrownianPath_raw s)
  have he : (fun p : BrownianPath => stopBrownianPath p s) ⁻¹'
      {p : BrownianPath | ∀ u : ℝ≥0, u ≤ s → p u+a*(u : ℝ) ≤ c} =
      {p : BrownianPath | ∀ u : ℝ≥0, u ≤ s → p u+a*(u : ℝ) ≤ c} := by
    ext p
    apply forall_congr'
    intro u
    apply imp_congr_right
    intro hu
    change (p (min u s)+a*(u : ℝ) ≤ c) ↔ p u+a*(u : ℝ) ≤ c
    rw [min_eq_left hu]
  rwa [he] at hm

/-- A nonempty first-hit clock exceeds a horizon exactly when all earlier values are strictly below the level. -/
theorem firstPassageTime_gt_iff_strict_barrier (p : BrownianPath) (c : ℝ) (s : ℝ≥0)
    (hh : ∃ u : ℝ≥0, c ≤ p u) :
    s < firstPassageTime p c ↔ ∀ u : ℝ≥0, u ≤ s → p u < c := by
  rw [← not_le,firstPassageTime_le_iff]
  constructor
  · intro hn u hu
    exact not_le.mp (fun h => hn (Or.inr ⟨u,hu,h⟩))
  · intro hb hn
    rcases hn with hn | ⟨u,hu,hcu⟩
    · exact hn hh
    · exact not_le.mpr (hb u hu) hcu

/-- The literal actual pre-hit event agrees almost surely with the closed finite-horizon upper barrier. -/
theorem brownianPath_positiveDrift_firstHit_event_ae (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (s : ℝ≥0) (hs : s ≠ 0) :
    {p : BrownianPath | s < firstPassageTime (driftedBrownianPath a p) c} =ᵐ[P]
      {p : BrownianPath | ∀ u : ℝ≥0, u ≤ s → p u+a*(u : ℝ) ≤ c} := by
  have he : {p : BrownianPath | s < firstPassageTime (driftedBrownianPath a p) c} =ᵐ[P]
      {p : BrownianPath | ∀ u : ℝ≥0, u ≤ s → p u+a*(u : ℝ) < c} := by
    filter_upwards [brownianPath_positiveDrift_hits_ae P hB a c ha] with p hp
    exact propext (firstPassageTime_gt_iff_strict_barrier (driftedBrownianPath a p) c s hp)
  exact he.trans (brownianPath_drift_barrier_ae_strict P hB a c hc s hs).symm

/-- The actual pre-hit remaining level has the negative-drift killed endpoint density. -/
theorem brownianPath_upperKilled_remaining_map (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a c : ℝ) (hc : 0 < c)
    (s : ℝ≥0) (hs : s ≠ 0) :
    (P.restrict {p : BrownianPath | ∀ u : ℝ≥0, u ≤ s → p u+a*(u : ℝ) ≤ c}).map
      (fun p => c-(p s+a*(s : ℝ))) =
      volume.withDensity (fun y => ENNReal.ofReal (brownianKilledTransitionPDF (-a) s c y)) := by
  have hm : Measurable (fun p : BrownianPath => p s+a*(s : ℝ)) :=
    (ContinuousMap.measurable_eval s).add measurable_const
  have he := brownianPath_lowerKilled_endpoint_map_eq_upper P hB (-a) c s
  rw [neg_neg,Measure.map_map (show Measurable (fun y : ℝ => c-y) from
    measurable_const.sub measurable_id) hm] at he
  simp only [Function.comp_def] at he
  rw [← he]
  exact brownianPath_lowerKilled_endpoint_map P hB (-a) c hc s hs

/-- Every nonnegative remaining-level test before the upper barrier integrates against the actual killed kernel. -/
theorem brownianPath_upperKilled_remaining_lintegral (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a c : ℝ) (hc : 0 < c)
    (s : ℝ≥0) (hs : s ≠ 0) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p in {p : BrownianPath | ∀ u : ℝ≥0, u ≤ s → p u+a*(u : ℝ) ≤ c},
      F (c-(p s+a*(s : ℝ))) ∂P) =
      ∫⁻ y, ENNReal.ofReal (brownianKilledTransitionPDF (-a) s c y)*F y := by
  have hm : Measurable (fun p : BrownianPath => c-(p s+a*(s : ℝ))) :=
    measurable_const.sub ((ContinuousMap.measurable_eval s).add measurable_const)
  calc
    _ = ∫⁻ y, F y ∂(P.restrict {p : BrownianPath | ∀ u : ℝ≥0, u ≤ s → p u+a*(u : ℝ) ≤ c}).map
        (fun p => c-(p s+a*(s : ℝ))) := (lintegral_map hF hm).symm
    _ = ∫⁻ y, F y ∂volume.withDensity (fun y => ENNReal.ofReal (brownianKilledTransitionPDF (-a) s c y)) := by
      rw [brownianPath_upperKilled_remaining_map P hB a c hc s hs]
    _ = _ := lintegral_withDensity_eq_lintegral_mul volume
      (((measurable_brownianKilledTransitionPDF (-a) s).comp
        (measurable_const.prodMk measurable_id)).ennreal_ofReal) hF

/-- The first-hit clock of a future path is jointly measurable in that future and its remaining level. -/
theorem measurable_firstPassageTime_drift_joint (a : ℝ) :
    Measurable (fun z : ℝ × BrownianPath => firstPassageTime (driftedBrownianPath a z.2) z.1) := by
  have hm : Measurable (fun z : ℝ × BrownianPath => driftedBrownianPath a z.2) :=
    continuous_driftedBrownianPath.measurable.comp (measurable_const.prodMk measurable_snd)
  exact measurable_firstPassageTime_joint.comp (measurable_fst.prodMk hm)

/-- The actual remaining level at a deterministic pre-hit time and the complete first-hit lifetime have their killed/hitting density law. -/
theorem brownianPath_firstHit_state_lifetime_lintegral (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (s : ℝ≥0) (hs : s ≠ 0) (H : ℝ × ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ p in {p : BrownianPath | s < firstPassageTime (driftedBrownianPath a p) c},
      H (c-(p s+a*(s : ℝ)),(firstPassageTime (driftedBrownianPath a p) c : ℝ)) ∂P) =
      ∫⁻ y, ENNReal.ofReal (brownianKilledTransitionPDF (-a) s c y)*
        ∫⁻ t, ENNReal.ofReal (brownianFirstHitDensity a y t)*H (y,(s : ℝ)+t) := by
  classical
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  let A : Set BrownianPath := {p | ∀ u : ℝ≥0, u ≤ s → p u+a*(u : ℝ) ≤ c}
  let X : BrownianPath → ℝ := fun p => c-(p s+a*(s : ℝ))
  let J : ℝ × BrownianPath → ℝ≥0∞ := fun z =>
    H (z.1,(s : ℝ)+(firstPassageTime (driftedBrownianPath a z.2) z.1 : ℝ))
  have hJ : Measurable J := hH.comp (measurable_fst.prodMk
    (measurable_const.add (NNReal.continuous_coe.measurable.comp (measurable_firstPassageTime_drift_joint a))))
  have hA : MeasurableSet A := measurableSet_brownianPath_drift_barrier a c s
  have hAr : MeasurableSet[brownianRawFiltration (fun u (p : BrownianPath) => p u)
      (fun u => ContinuousMap.measurable_eval u) s] A :=
    measurableSet_brownianPath_drift_barrier_raw a c s
  have hX : Measurable[brownianRawFiltration (fun u (p : BrownianPath) => p u)
      (fun u => ContinuousMap.measurable_eval u) s] X :=
    measurable_const.sub ((measurable_brownianPath_eval_raw s s le_rfl).add measurable_const)
  have he := brownianPath_positiveDrift_firstHit_event_ae P hB a c ha hc s hs
  have hclock : (fun p => H (X p,(firstPassageTime (driftedBrownianPath a p) c : ℝ))) =ᵐ[P.restrict A]
      (fun p => J (X p,brownianShiftPath s p)) := by
    filter_upwards [ae_restrict_of_ae he,ae_restrict_of_ae
      (brownianPath_positiveDrift_firstHit_shift_ae P hB a c ha s),ae_restrict_mem hA] with p hep hsp hp
    have hpre : s < firstPassageTime (driftedBrownianPath a p) c := by
      rw [hep]
      exact hp
    have hτ := hsp hpre
    dsimp [X,J]
    rw [hτ,NNReal.coe_add]
  rw [Measure.restrict_congr_set he]
  calc
    _ = ∫⁻ p in A, J (X p,brownianShiftPath s p) ∂P := lintegral_congr_ae hclock
    _ = ∫⁻ p in A, ∫⁻ q, J (X p,q) ∂P ∂P :=
      brownianPath_past_event_restart_lintegral P hB s A hAr X hX J hJ
    _ = ∫⁻ y, ENNReal.ofReal (brownianKilledTransitionPDF (-a) s c y)*∫⁻ q, J (y,q) ∂P :=
      brownianPath_upperKilled_remaining_lintegral P hB a c hc s hs
        (fun y => ∫⁻ q, J (y,q) ∂P) (Measurable.lintegral_prod_right (f := fun y q => J (y,q)) hJ)
    _ = _ := by
      apply lintegral_congr
      intro y
      by_cases hy : 0 < y
      · congr 1
        exact brownianPath_positiveDrift_firstHit_density_lintegral P hB a y ha hy
          (fun t => H (y,(s : ℝ)+t))
          (hH.comp (measurable_const.prodMk (measurable_const.add measurable_id)))
      · simp only [brownianKilledTransitionPDF,hy,and_false,ite_false,ENNReal.ofReal_zero,zero_mul]

/-- The killed endpoint times the remaining hitting density is jointly measurable in state and remaining time. -/
theorem measurable_brownianFirstHitStateDensity (a c : ℝ) (s : ℝ≥0) :
    Measurable (fun z : ℝ × ℝ => ENNReal.ofReal (brownianKilledTransitionPDF (-a) s c z.1)*
      ENNReal.ofReal (brownianFirstHitDensity a z.1 z.2)) := by
  exact (((measurable_brownianKilledTransitionPDF (-a) s).comp
    (measurable_const.prodMk measurable_fst)).ennreal_ofReal).mul
    ((measurable_brownianFirstHitDensity_joint.comp
      (measurable_const.prodMk measurable_id)).ennreal_ofReal)


/-- Before an actual first hit, every raw-past observable has the complete remaining first-hit density as its conditional lifetime law. -/
theorem brownianPath_firstHit_past_lifetime_lintegral {E : Type*} [MeasurableSpace E]
    (P : Measure BrownianPath) (hB : IsBrownianReal (fun t p => p t) P)
    (a c : ℝ) (ha : 0 < a) (hc : 0 < c) (s : ℝ≥0) (hs : s ≠ 0)
    (Y : BrownianPath → E)
    (hY : Measurable[brownianRawFiltration (fun u (p : BrownianPath) => p u)
      (fun u => ContinuousMap.measurable_eval u) s] Y)
    (H : E × ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ p in {p : BrownianPath | s < firstPassageTime (driftedBrownianPath a p) c},
      H (Y p,(firstPassageTime (driftedBrownianPath a p) c : ℝ)) ∂P) =
      ∫⁻ p in {p : BrownianPath | s < firstPassageTime (driftedBrownianPath a p) c},
        ∫⁻ t, ENNReal.ofReal (brownianFirstHitDensity a (c-(p s+a*(s : ℝ))) t)*H (Y p,(s : ℝ)+t) ∂volume ∂P := by
  classical
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  let A : Set BrownianPath := {p | ∀ u : ℝ≥0, u ≤ s → p u+a*(u : ℝ) ≤ c}
  let X : BrownianPath → E × ℝ := fun p => (Y p,c-(p s+a*(s : ℝ)))
  let J : (E × ℝ) × BrownianPath → ℝ≥0∞ := fun z =>
    H (z.1.1,(s : ℝ)+(firstPassageTime (driftedBrownianPath a z.2) z.1.2 : ℝ))
  have hmτ : Measurable (fun z : (E × ℝ) × BrownianPath =>
      firstPassageTime (driftedBrownianPath a z.2) z.1.2) :=
    (measurable_firstPassageTime_drift_joint a).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hJ : Measurable J := hH.comp ((measurable_fst.comp measurable_fst).prodMk
    (measurable_const.add (NNReal.continuous_coe.measurable.comp hmτ)))
  have hA : MeasurableSet A := measurableSet_brownianPath_drift_barrier a c s
  have hAr : MeasurableSet[brownianRawFiltration (fun u (p : BrownianPath) => p u)
      (fun u => ContinuousMap.measurable_eval u) s] A :=
    measurableSet_brownianPath_drift_barrier_raw a c s
  have hX : Measurable[brownianRawFiltration (fun u (p : BrownianPath) => p u)
      (fun u => ContinuousMap.measurable_eval u) s] X := hY.prodMk
    (measurable_const.sub ((measurable_brownianPath_eval_raw s s le_rfl).add measurable_const))
  have he := brownianPath_positiveDrift_firstHit_event_ae P hB a c ha hc s hs
  have hpre : ∀ᵐ p ∂P.restrict A, s < firstPassageTime (driftedBrownianPath a p) c := by
    filter_upwards [ae_restrict_of_ae he,ae_restrict_mem hA] with p hep hp
    rw [hep]
    exact hp
  have hclock : (fun p => H (Y p,(firstPassageTime (driftedBrownianPath a p) c : ℝ))) =ᵐ[P.restrict A]
      (fun p => J (X p,brownianShiftPath s p)) := by
    filter_upwards [hpre,ae_restrict_of_ae
      (brownianPath_positiveDrift_firstHit_shift_ae P hB a c ha s)] with p hp hsp
    dsimp [X,J]
    rw [hsp hp,NNReal.coe_add]
  rw [Measure.restrict_congr_set he]
  calc
    _ = ∫⁻ p in A, J (X p,brownianShiftPath s p) ∂P := lintegral_congr_ae hclock
    _ = ∫⁻ p in A, ∫⁻ q, J (X p,q) ∂P ∂P :=
      brownianPath_past_event_restart_lintegral P hB s A hAr X hX J hJ
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [hpre] with p hp
      have hy : 0 < c-(p s+a*(s : ℝ)) :=
        firstPassageTime_before_level_pos (driftedBrownianPath a p) c s hp
      exact brownianPath_positiveDrift_firstHit_density_lintegral P hB a _ ha hy
        (fun t => H (Y p,(s : ℝ)+t))
        (hH.comp (measurable_const.prodMk (measurable_const.add measurable_id)))

/-- The state/lifetime density has exactly the pre-hit survival mass. -/
theorem lintegral_brownianFirstHitStateDensity (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a c : ℝ) (ha : 0 < a) (hc : 0 < c)
    (s : ℝ≥0) (hs : s ≠ 0) :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (brownianKilledTransitionPDF (-a) s c z.1)*
      ENNReal.ofReal (brownianFirstHitDensity a z.1 z.2) ∂volume.prod volume) =
      P {p : BrownianPath | s < firstPassageTime (driftedBrownianPath a p) c} := by
  have he := brownianPath_firstHit_state_lifetime_lintegral P hB a c ha hc s hs
    (fun _ => 1) measurable_const
  simp only [mul_one,lintegral_one,Measure.restrict_apply MeasurableSet.univ,univ_inter] at he
  rw [lintegral_prod _ (measurable_brownianFirstHitStateDensity a c s).aemeasurable]
  rw [he]
  apply lintegral_congr
  intro y
  change (∫⁻ t : ℝ, ENNReal.ofReal (brownianKilledTransitionPDF (-a) s c y)*
    ENNReal.ofReal (brownianFirstHitDensity a y t)) = _
  exact lintegral_const_mul (ENNReal.ofReal (brownianKilledTransitionPDF (-a) s c y))
    (measurable_brownianFirstHitDensity a y).ennreal_ofReal





end DOZZ.Proofs

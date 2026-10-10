/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Brownian.Barrier.FirstHitDensity

/-!
# Actual killed Brownian Markov laws

The raw past at a deterministic horizon contains the whole stopped continuous
path. Its joint law with the shifted full future is the actual product law,
obtained from the already proved bounded raw stopping-time restart. Every
jointly measurable nonnegative past/future test therefore satisfies Tonelli's
factorization on the original path space.

Lower survival is measurable both in that raw past and jointly in the initial
state and future path. Splitting survival at a deterministic horizon is a
pointwise identity, including the common endpoint. These facts identify the
actual two-time killed endpoint law with the product of the two Gaussian
killed transition kernels, for either sign of the drift. They also give the
weak Chapman--Kolmogorov identity and the full product-density pushforward.
The density has mass at most one because it describes actual surviving paths.

A separate deterministic argument identifies a first hit after a horizon
with that horizon plus the first hit by the shifted future path. It respects
the empty-hit convention by requiring an actual hit. Positive drift
supplies that condition almost surely. The remaining level is positive on
the pre-hit event, so the proved first-hit density applies there.

This is an actual law construction, rather than a killed-Markov assumption.
The ceiling-grid reversed marked-path law still requires its lifetime and
multi-time assembly; these two-time identities alone do not prove reversal.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace DOZZ.Proofs

/-- A raw-history evaluation is measurable at every later deterministic horizon. -/
theorem measurable_brownianPath_eval_raw (s t : ℝ≥0) (ht : t ≤ s) :
    Measurable[brownianRawFiltration (fun u (p : BrownianPath) => p u)
      (fun u => ContinuousMap.measurable_eval u) s] (fun p : BrownianPath => p t) := by
  exact Measurable.of_comap_le (le_iSup_of_le t (le_iSup_of_le ht le_rfl))

/-- The entire path stopped at a deterministic time is measurable in the raw past. -/
theorem measurable_stopBrownianPath_raw (s : ℝ≥0) :
    Measurable[brownianRawFiltration (fun u (p : BrownianPath) => p u)
      (fun u => ContinuousMap.measurable_eval u) s] (fun p : BrownianPath => stopBrownianPath p s) := by
  let := brownianRawFiltration (fun u (p : BrownianPath) => p u) (fun u => ContinuousMap.measurable_eval u) s
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  exact measurable_brownianPath_eval_raw s (min t s) (min_le_right _ _)

/-- A deterministic raw-past observable and the actual full future path have product law. -/
theorem brownianPath_deterministic_restart_joint_map {E : Type*} [MeasurableSpace E]
    (P : Measure BrownianPath) (hB : IsBrownianReal (fun t p => p t) P)
    (s : ℝ≥0) (X : BrownianPath → E)
    (hX : Measurable[brownianRawFiltration (fun u (p : BrownianPath) => p u)
      (fun u => ContinuousMap.measurable_eval u) s] X) :
    P.map (fun p => (X p,brownianShiftPath s p)) = (P.map X).prod P := by
  apply brownianPath_bounded_restart_joint_map P hB (fun _ => s)
    (isStoppingTime_const _ s) s (fun _ => le_rfl) X
  change Measurable[(isStoppingTime_const (brownianRawFiltration (fun u (p : BrownianPath) => p u)
    (fun u => ContinuousMap.measurable_eval u)) s).measurableSpace] X
  rw [IsStoppingTime.measurableSpace_const]
  exact hX

/-- Every jointly measurable past/future test integrates against the actual independent future law. -/
theorem brownianPath_deterministic_restart_lintegral {E : Type*} [MeasurableSpace E]
    (P : Measure BrownianPath) (hB : IsBrownianReal (fun t p => p t) P)
    (s : ℝ≥0) (X : BrownianPath → E)
    (hX : Measurable[brownianRawFiltration (fun u (p : BrownianPath) => p u)
      (fun u => ContinuousMap.measurable_eval u) s] X)
    (F : E × BrownianPath → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F (X p,brownianShiftPath s p) ∂P) =
      ∫⁻ p, ∫⁻ q, F (X p,q) ∂P ∂P := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hmX : Measurable X := hX.mono ((brownianRawFiltration _ _).le s) le_rfl
  have hmV : Measurable (fun p : BrownianPath => brownianShiftPath s p) :=
    continuous_brownianShiftPath.measurable.comp (measurable_const.prodMk measurable_id)
  calc
    _ = ∫⁻ z, F z ∂P.map (fun p => (X p,brownianShiftPath s p)) :=
      (lintegral_map hF (hmX.prodMk hmV)).symm
    _ = ∫⁻ z, F z ∂(P.map X).prod P := by
      rw [brownianPath_deterministic_restart_joint_map P hB s X hX]
    _ = ∫⁻ x, ∫⁻ q, F (x,q) ∂P ∂P.map X := lintegral_prod F hF.aemeasurable
    _ = _ := lintegral_map (show Measurable (fun x => ∫⁻ q, F (x,q) ∂P) from Measurable.lintegral_prod_right (f := fun x q => F (x,q)) hF) hmX

/-- The finite-horizon positive-half-line survival event for a path started at a real state. -/
def brownianLowerSurvival (a x : ℝ) (T : ℝ≥0) : Set BrownianPath :=
  {p | ∀ u : ℝ≥0, u ≤ T → 0 ≤ x+p u+a*(u : ℝ)}

/-- Stopping at a horizon preserves its lower survival event pointwise. -/
theorem stopBrownianPath_lowerSurvival (a x : ℝ) (T : ℝ≥0) (p : BrownianPath) :
    stopBrownianPath p T ∈ brownianLowerSurvival a x T ↔ p ∈ brownianLowerSurvival a x T := by
  apply forall_congr'
  intro u
  apply imp_congr_right
  intro hu
  change (0 ≤ x+p (min u T)+a*(u : ℝ)) ↔ 0 ≤ x+p u+a*(u : ℝ)
  rw [min_eq_left hu]

/-- Lower survival is a measurable event on the continuous-path carrier. -/
theorem measurableSet_brownianLowerSurvival (a x : ℝ) (T : ℝ≥0) :
    MeasurableSet (brownianLowerSurvival a x T) := by
  have he : brownianLowerSurvival a x T =
      (fun p : BrownianPath => -p) ⁻¹' {p : BrownianPath | ∀ u : ℝ≥0, u ≤ T → p u+(-a)*(u : ℝ) ≤ x} := by
    ext p
    apply forall_congr'
    intro u
    apply imp_congr_right
    intro hu
    change (0 ≤ x+p u+a*(u : ℝ)) ↔ -p u+(-a)*(u : ℝ) ≤ x
    constructor <;> intro h <;> linarith
  rw [he]
  exact (measurableSet_brownianPath_drift_barrier (-a) x T).preimage measurable_neg


/-- Survival over two successive horizons is exactly past survival and shifted future survival. -/
theorem brownianLowerSurvival_add (a x : ℝ) (s t : ℝ≥0) (p : BrownianPath) :
    p ∈ brownianLowerSurvival a x (s+t) ↔
      p ∈ brownianLowerSurvival a x s ∧
        brownianShiftPath s p ∈ brownianLowerSurvival a (x+p s+a*(s : ℝ)) t := by
  constructor
  · intro h
    refine ⟨fun u hu => h u (hu.trans (le_add_of_nonneg_right (show 0 ≤ t from zero_le))),?_⟩
    intro u hu
    have hh := h (s+u) (show s+u ≤ s+t from by exact_mod_cast add_le_add_right (NNReal.coe_le_coe.mpr hu) (s : ℝ))
    change 0 ≤ x+p (s+u)+a*((s+u : ℝ≥0) : ℝ) at hh
    change 0 ≤ (x+p s+a*(s : ℝ))+(p (s+u)-p s)+a*(u : ℝ)
    push_cast at hh
    linarith
  · rintro ⟨h1,h2⟩ u hu
    by_cases hus : u ≤ s
    · exact h1 u hus
    · have hsu : s ≤ u := le_of_not_ge hus
      have hut : u-s ≤ t := (tsub_le_iff_right).mpr (by simpa only [add_comm] using hu)
      have hh := h2 (u-s) hut
      change 0 ≤ (x+p s+a*(s : ℝ))+(p (s+(u-s))-p s)+a*((u-s : ℝ≥0) : ℝ) at hh
      rw [add_tsub_cancel_of_le hsu,NNReal.coe_sub hsu] at hh
      linarith

/-- Survival is jointly measurable in the initial state and the actual future path. -/
theorem measurableSet_brownianLowerSurvival_joint (a : ℝ) (T : ℝ≥0) :
    MeasurableSet {z : ℝ × BrownianPath | z.2 ∈ brownianLowerSurvival a z.1 T} := by
  have hmM : Measurable (fun p : BrownianPath => ⨆ u : Iic T, p u) :=
    (measurable_brownianPath_runningMaximum T).mono ((brownianRawFiltration _ _).le T) le_rfl
  have hmN : Measurable (fun z : ℝ × BrownianPath => brownianDriftPath (-a) (-z.2)) :=
    continuous_brownianDriftPath.measurable.comp (measurable_const.prodMk measurable_snd.neg)
  have he : {z : ℝ × BrownianPath | z.2 ∈ brownianLowerSurvival a z.1 T} =
      {z | (⨆ u : Iic T, brownianDriftPath (-a) (-z.2) u) ≤ z.1} := by
    ext z
    change (∀ u : ℝ≥0, u ≤ T → 0 ≤ z.1+z.2 u+a*(u : ℝ)) ↔
      (⨆ u : Iic T, brownianDriftPath (-a) (-z.2) u) ≤ z.1
    rw [← brownianPath_barrier_iff_runningMaximum]
    apply forall_congr'
    intro u
    apply imp_congr_right
    intro hu
    change (0 ≤ z.1+z.2 u+a*(u : ℝ)) ↔ -z.2 u+(-a)*(u : ℝ) ≤ z.1
    constructor <;> intro h <;> linarith
  rw [he]
  exact measurableSet_le (hmM.comp hmN) measurable_fst

/-- A surviving past can be tested jointly with the independent full Brownian future. -/
theorem brownianPath_surviving_restart_lintegral (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a x : ℝ) (s : ℝ≥0)
    (F : ℝ × BrownianPath → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p in brownianLowerSurvival a x s, F (x+p s+a*(s : ℝ),brownianShiftPath s p) ∂P) =
      ∫⁻ p in brownianLowerSurvival a x s, ∫⁻ q, F (x+p s+a*(s : ℝ),q) ∂P ∂P := by
  classical
  let J : BrownianPath × BrownianPath → ℝ≥0∞ := fun z =>
    if z.1 ∈ brownianLowerSurvival a x s then F (x+z.1 s+a*(s : ℝ),z.2) else 0
  have hJ : Measurable J := Measurable.ite
    ((measurableSet_brownianLowerSurvival a x s).preimage measurable_fst)
    (hF.comp (((measurable_const.add ((ContinuousMap.measurable_eval s).comp measurable_fst)).add measurable_const).prodMk measurable_snd))
    measurable_const
  have hh := brownianPath_deterministic_restart_lintegral P hB s
    (fun p => stopBrownianPath p s) (measurable_stopBrownianPath_raw s) J hJ
  have hl : (fun p => J (stopBrownianPath p s,brownianShiftPath s p)) =
      (brownianLowerSurvival a x s).indicator
        (fun p => F (x+p s+a*(s : ℝ),brownianShiftPath s p)) := by
    funext p
    have he : stopBrownianPath p s s = p s := by
      change p (min s s) = p s
      rw [min_self]
    simp only [J,Set.indicator_apply,stopBrownianPath_lowerSurvival,he]
  have hr : (fun p => ∫⁻ q, J (stopBrownianPath p s,q) ∂P) =
      (brownianLowerSurvival a x s).indicator
        (fun p => ∫⁻ q, F (x+p s+a*(s : ℝ),q) ∂P) := by
    funext p
    by_cases hp : p ∈ brownianLowerSurvival a x s
    · have he : stopBrownianPath p s s = p s := by
        change p (min s s) = p s
        rw [min_self]
      simp only [J,Set.indicator_apply,stopBrownianPath_lowerSurvival,ite_eq_left hp,he]
    · simp only [J,Set.indicator_apply,stopBrownianPath_lowerSurvival,ite_eq_right hp,lintegral_zero]
  rw [hl,hr,lintegral_indicator (measurableSet_brownianLowerSurvival a x s),
    lintegral_indicator (measurableSet_brownianLowerSurvival a x s)] at hh
  exact hh

/-- The actual two-time killed endpoint law factors through the two scalar killed transition densities. -/
theorem brownianPath_twoTime_killed_lintegral (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a x : ℝ) (hx : 0 < x)
    (s t : ℝ≥0) (hs : s ≠ 0) (ht : t ≠ 0)
    (H : ℝ × ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ p in brownianLowerSurvival a x (s+t),
      H (x+p s+a*(s : ℝ),x+p (s+t)+a*((s+t : ℝ≥0) : ℝ)) ∂P) =
      ∫⁻ y, ENNReal.ofReal (brownianKilledTransitionPDF a s x y)*
        ∫⁻ z, ENNReal.ofReal (brownianKilledTransitionPDF a t y z)*H (y,z) := by
  classical
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  let G : ℝ × BrownianPath → ℝ≥0∞ := fun z =>
    if z.2 ∈ brownianLowerSurvival a z.1 t then H (z.1,z.1+z.2 t+a*(t : ℝ)) else 0
  have hG : Measurable G := Measurable.ite (measurableSet_brownianLowerSurvival_joint a t)
    (hH.comp (measurable_fst.prodMk
      ((measurable_fst.add ((ContinuousMap.measurable_eval t).comp measurable_snd)).add measurable_const)))
    measurable_const
  have hh := brownianPath_surviving_restart_lintegral P hB a x s G hG
  have hl : (∫⁻ p in brownianLowerSurvival a x s,
      G (x+p s+a*(s : ℝ),brownianShiftPath s p) ∂P) =
      ∫⁻ p in brownianLowerSurvival a x (s+t),
        H (x+p s+a*(s : ℝ),x+p (s+t)+a*((s+t : ℝ≥0) : ℝ)) ∂P := by
    rw [← lintegral_indicator (measurableSet_brownianLowerSurvival a x s),
      ← lintegral_indicator (measurableSet_brownianLowerSurvival a x (s+t))]
    apply lintegral_congr
    intro p
    have he : (x+p s+a*(s : ℝ))+brownianShiftPath s p t+a*(t : ℝ) =
        x+p (s+t)+a*((s+t : ℝ≥0) : ℝ) := by
      change (x+p s+a*(s : ℝ))+(p (s+t)-p s)+a*(t : ℝ) = _
      push_cast
      ring_nf
    by_cases h1 : p ∈ brownianLowerSurvival a x s
    · by_cases h2 : brownianShiftPath s p ∈ brownianLowerSurvival a (x+p s+a*(s : ℝ)) t
      · have hp := (brownianLowerSurvival_add a x s t p).mpr ⟨h1,h2⟩
        simp only [G,Set.indicator_apply,ite_eq_left h1,ite_eq_left h2,ite_eq_left hp,he]
      · have hp : p ∉ brownianLowerSurvival a x (s+t) :=
          fun hp => h2 ((brownianLowerSurvival_add a x s t p).mp hp).2
        simp only [G,Set.indicator_apply,ite_eq_left h1,ite_eq_right h2,ite_eq_right hp]
    · have hp : p ∉ brownianLowerSurvival a x (s+t) :=
        fun hp => h1 ((brownianLowerSurvival_add a x s t p).mp hp).1
      simp only [Set.indicator_apply,ite_eq_right h1,ite_eq_right hp]
  rw [hl] at hh
  rw [hh]
  have ho := brownianPath_lowerKilled_endpoint_lintegral P hB a x hx s hs
    (fun y => ∫⁻ q, G (y,q) ∂P)
    (Measurable.lintegral_prod_right (f := fun y q => G (y,q)) hG)
  change (∫⁻ p in brownianLowerSurvival a x s, ∫⁻ q, G (x+p s+a*(s : ℝ),q) ∂P ∂P) = _ at ho
  rw [ho]
  apply lintegral_congr
  intro y
  by_cases hy : 0 < y
  · congr 1
    have he : (fun q => G (y,q)) = (brownianLowerSurvival a y t).indicator
        (fun q => H (y,y+q t+a*(t : ℝ))) := by
      funext q
      simp only [G,Set.indicator_apply]
    rw [he,lintegral_indicator (measurableSet_brownianLowerSurvival a y t)]
    exact brownianPath_lowerKilled_endpoint_lintegral P hB a y hy t ht
      (fun z => H (y,z)) (hH.comp (measurable_const.prodMk measurable_id))
  · simp only [brownianKilledTransitionPDF,hy,and_false,ite_false,ENNReal.ofReal_zero,zero_mul]

/-- A first hit strictly after a deterministic time is the shifted future first hit plus that time. -/
theorem firstPassageTime_eq_add_shift (p : BrownianPath) (c : ℝ) (s : ℝ≥0)
    (hh : ∃ u : ℝ≥0, c ≤ p u) (hs : s < firstPassageTime p c) :
    firstPassageTime p c = s+firstPassageTime (brownianShiftPath s p) (c-p s) := by
  let τ := firstPassageTime p c
  let σ := firstPassageTime (brownianShiftPath s p) (c-p s)
  have hsτ : s ≤ τ := hs.le
  have hf : ∃ u : ℝ≥0, c-p s ≤ brownianShiftPath s p u := by
    refine ⟨τ-s,?_⟩
    change c-p s ≤ p (s+(τ-s))-p s
    rw [add_tsub_cancel_of_le hsτ]
    exact sub_le_sub_right (firstPassageTime_mem p c hh) _
  have hσ : σ ≤ τ-s := by
    apply csInf_le (s := {u : ℝ≥0 | c-p s ≤ brownianShiftPath s p u}) (OrderBot.bddBelow _)
    change c-p s ≤ p (s+(τ-s))-p s
    rw [add_tsub_cancel_of_le hsτ]
    exact sub_le_sub_right (firstPassageTime_mem p c hh) _
  have hτ : τ ≤ s+σ := by
    apply csInf_le (s := {u : ℝ≥0 | c ≤ p u}) (OrderBot.bddBelow _)
    change c ≤ p (s+σ)
    have hm := firstPassageTime_mem (brownianShiftPath s p) (c-p s) hf
    change c-p s ≤ p (s+σ)-p s at hm
    linarith
  apply le_antisymm hτ
  have hl : s+σ ≤ s+(τ-s) := by simpa only [add_comm] using add_le_add_right hσ s
  rwa [add_tsub_cancel_of_le hsτ] at hl

/-- The remaining upper level is positive before the first hit. -/
theorem firstPassageTime_before_level_pos (p : BrownianPath) (c : ℝ) (s : ℝ≥0)
    (hs : s < firstPassageTime p c) : 0 < c-p s := by
  have hn : ¬ c ≤ p s := by
    intro hp
    have hle : firstPassageTime p c ≤ s :=
      csInf_le (s := {u : ℝ≥0 | c ≤ p u}) (OrderBot.bddBelow _) hp
    exact not_le.mpr hs hle
  exact sub_pos.mpr (not_le.mp hn)

/-- Shifting a drifted path adds the same deterministic drift to its shifted Brownian increments. -/
theorem brownianShiftPath_drift (a : ℝ) (s : ℝ≥0) (p : BrownianPath) :
    brownianShiftPath s (driftedBrownianPath a p) =
      driftedBrownianPath a (brownianShiftPath s p) := by
  ext u
  change (p (s+u)+a*((s+u : ℝ≥0) : ℝ))-(p s+a*(s : ℝ)) =
    (p (s+u)-p s)+a*(u : ℝ)
  push_cast
  ring_nf

/-- The actual first-hit clock has the deterministic shift identity on its pre-hit event. -/
theorem brownianPath_positiveDrift_firstHit_shift_ae (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a c : ℝ) (ha : 0 < a) (s : ℝ≥0) :
    ∀ᵐ p ∂P, s < firstPassageTime (driftedBrownianPath a p) c →
      firstPassageTime (driftedBrownianPath a p) c =
        s+firstPassageTime (driftedBrownianPath a (brownianShiftPath s p)) (c-(p s+a*(s : ℝ))) := by
  filter_upwards [brownianPath_positiveDrift_hits_ae P hB a c ha] with p hp hs
  have he := firstPassageTime_eq_add_shift (driftedBrownianPath a p) c s hp hs
  rw [brownianShiftPath_drift] at he
  change firstPassageTime (driftedBrownianPath a p) c =
    s+firstPassageTime (driftedBrownianPath a (brownianShiftPath s p)) (c-(p s+a*(s : ℝ))) at he
  exact he

/-- The two-time killed density is jointly measurable in both sampled states. -/
theorem measurable_brownianKilledPairDensity (a x : ℝ) (s t : ℝ≥0) :
    Measurable (fun z : ℝ × ℝ => ENNReal.ofReal (brownianKilledTransitionPDF a s x z.1)*
      ENNReal.ofReal (brownianKilledTransitionPDF a t z.1 z.2)) := by
  exact (((measurable_brownianKilledTransitionPDF a s).comp
    (measurable_const.prodMk measurable_fst)).ennreal_ofReal).mul
    (measurable_brownianKilledTransitionPDF a t).ennreal_ofReal

/-- The actual two-time killed pushforward has its full product-density measure, for every real drift. -/
theorem brownianPath_twoTime_killed_map (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a x : ℝ) (hx : 0 < x)
    (s t : ℝ≥0) (hs : s ≠ 0) (ht : t ≠ 0) :
    (P.restrict (brownianLowerSurvival a x (s+t))).map
      (fun p => (x+p s+a*(s : ℝ),x+p (s+t)+a*((s+t : ℝ≥0) : ℝ))) =
      (volume.prod volume).withDensity (fun z : ℝ × ℝ =>
        ENNReal.ofReal (brownianKilledTransitionPDF a s x z.1)*
          ENNReal.ofReal (brownianKilledTransitionPDF a t z.1 z.2)) := by
  apply Measure.ext_of_lintegral
  intro H hH
  have hm : Measurable (fun p : BrownianPath =>
      (x+p s+a*(s : ℝ),x+p (s+t)+a*((s+t : ℝ≥0) : ℝ))) := by
    fun_prop
  rw [lintegral_map hH hm,lintegral_withDensity_eq_lintegral_mul _
    (measurable_brownianKilledPairDensity a x s t) hH]
  rw [brownianPath_twoTime_killed_lintegral P hB a x hx s t hs ht H hH]
  rw [lintegral_prod _ ((measurable_brownianKilledPairDensity a x s t).mul hH).aemeasurable]
  apply lintegral_congr
  intro y
  rw [← lintegral_const_mul _ (show Measurable (fun z =>
    ENNReal.ofReal (brownianKilledTransitionPDF a t y z)*H (y,z)) from
      (((measurable_brownianKilledTransitionPDF a t).comp
        (measurable_const.prodMk measurable_id)).ennreal_ofReal).mul
        (hH.comp (measurable_const.prodMk measurable_id)))]
  apply lintegral_congr
  intro z
  exact (mul_assoc _ _ _).symm



end DOZZ.Proofs

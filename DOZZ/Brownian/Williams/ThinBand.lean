/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Brownian.Williams.MaximumGeometry
public import DOZZ.Brownian.Barrier.FirstHitDensity
public import DOZZ.Statements.Brownian.ConditionedH
/-!
# The exact Williams thin-band identity on actual Brownian paths

The entire lifetime-marked stopped prefix is measurable in its stopping
history. Bounded raw restart removes the remaining Gaussian likelihood for
all nonnegative prefix tests. Finite-horizon Gaussian tilting then changes
positive to negative drift with constant first-hit likelihood exp(-2νm).
Increasing lifetime cutoffs removes the cap without an integrability premise.

The actual maximum band is precisely a hit of its lower edge followed by
avoidance of its upper edge. Restart factors the full marked prefix and the
full future path. The avoidance mass is the literal harmonic factor, and
normalization defines the actual Brownian law conditioned below the band
width. The final theorem is the source thin-band equation with both scalar
factors retained. Identifying the zero-width entrance limit and integrating
the bands into the Williams disintegration are separate remaining steps.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace DOZZ.Proofs

/-- The entire stopped path is measurable in its stopping-time sigma algebra. -/
theorem measurable_stopBrownianPath_stopped (τ : BrownianPath → ℝ≥0)
    (hτ : IsStoppingTime (brownianRawFiltration (fun t (p : BrownianPath) => p t)
      (fun t => ContinuousMap.measurable_eval t)) (fun p => (τ p : WithTop ℝ≥0))) :
    Measurable[hτ.measurableSpace] (fun p => stopBrownianPath p (τ p)) := by
  have ha : StronglyAdapted (brownianRawFiltration (fun t (p : BrownianPath) => p t)
      (fun t => ContinuousMap.measurable_eval t)) (fun t p => stopBrownianPath p t) :=
    fun t => (measurable_stopBrownianPath_raw t).stronglyMeasurable
  have hc (p : BrownianPath) : Continuous (fun t => stopBrownianPath p t) :=
    continuous_stopBrownianPath.comp (continuous_id.prodMk continuous_const)
  have hm := measurable_stoppedValue (ha.isStronglyProgressive_of_continuous hc) hτ
  change Measurable[hτ.measurableSpace] (fun p => stopBrownianPath p ((τ p : WithTop ℝ≥0).untopA)) at hm
  simpa only [WithTop.untopA,WithTop.untopD_coe] using hm

/-- A raw stopped lifetime and its entire stopped path are jointly measurable. -/
theorem measurable_brownianStoppedMark_stopped (τ : BrownianPath → ℝ≥0)
    (hτ : IsStoppingTime (brownianRawFiltration (fun t (p : BrownianPath) => p t)
      (fun t => ContinuousMap.measurable_eval t)) (fun p => (τ p : WithTop ℝ≥0))) :
    Measurable[hτ.measurableSpace] (fun p => (τ p,stopBrownianPath p (τ p))) :=
  (measurable_finite_stoppingTime_stopped _ τ hτ).prodMk (measurable_stopBrownianPath_stopped τ hτ)

/-- The whole lifetime-marked stopped prefix can select the remaining Gaussian likelihood. -/
theorem brownianPath_bounded_restart_remainingLikelihood_marked (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (τ : BrownianPath → ℝ≥0)
    (hτ : IsStoppingTime (brownianRawFiltration (fun t (p : BrownianPath) => p t)
      (fun t => ContinuousMap.measurable_eval t)) (fun p => (τ p : WithTop ℝ≥0)))
    (T : ℝ≥0) (hτT : ∀ p, τ p ≤ T) (a : ℝ)
    (F : StoppedBrownianPath → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F (τ p,stopBrownianPath p (τ p))*brownianGaussianLikelihood a (T-τ p)
      (brownianShiftPath (τ p) p (T-τ p)) ∂P) =
      ∫⁻ p, F (τ p,stopBrownianPath p (τ p)) ∂P := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  let X : BrownianPath → StoppedBrownianPath := fun p => (τ p,stopBrownianPath p (τ p))
  have hX := measurable_brownianStoppedMark_stopped τ hτ
  have hmX : Measurable X := hX.mono hτ.measurableSpace_le le_rfl
  have hmτ := measurable_finite_brownian_stoppingTime _ τ hτ
  have hmV : Measurable (fun p => brownianShiftPath (τ p) p) :=
    continuous_brownianShiftPath.measurable.comp (hmτ.prodMk measurable_id)
  let G : StoppedBrownianPath × BrownianPath → ℝ≥0∞ :=
    fun z => F z.1*brownianGaussianLikelihood a (T-z.1.1) (z.2 (T-z.1.1))
  have hG : Measurable G :=
    (hF.comp (f := fun z : StoppedBrownianPath × BrownianPath => z.1) measurable_fst).mul
      ((measurable_brownian_remainingLikelihood a T).comp
        (f := fun z : StoppedBrownianPath × BrownianPath => (z.1.1, z.2))
        (measurable_fst.fst.prodMk measurable_snd))
  have hj := brownianPath_bounded_restart_joint_map P hB τ hτ T hτT X hX
  calc
    _ = ∫⁻ z, G z ∂P.map (fun p => (X p,brownianShiftPath (τ p) p)) :=
      (lintegral_map hG (hmX.prodMk hmV)).symm
    _ = ∫⁻ z, G z ∂(P.map X).prod P := by rw [hj]
    _ = ∫⁻ u, ∫⁻ p, G (u,p) ∂P ∂P.map X := lintegral_prod G hG.aemeasurable
    _ = ∫⁻ u, F u ∂P.map X := by
      apply lintegral_congr
      intro u
      change (∫⁻ p, F u*brownianGaussianLikelihood a (T-u.1) (p (T-u.1)) ∂P) = F u
      rw [lintegral_const_mul (F u)
        (show Measurable (fun p : BrownianPath => brownianGaussianLikelihood a (T-u.1) (p (T-u.1))) from
          (measurable_brownianGaussianLikelihood a (T-u.1)).comp (ContinuousMap.measurable_eval (T-u.1))),
        brownian_lintegral_gaussianLikelihood_one P hB.toIsPreBrownianReal a (T-u.1),mul_one]
    _ = _ := lintegral_map hF hmX

/-- Drifted capped first passage is a stopping time of the original raw Brownian history. -/
theorem cappedBrownianFirstPassage_drift_isStoppingTime (a c : ℝ) (T : ℝ≥0) :
    IsStoppingTime (brownianRawFiltration (fun t (p : BrownianPath) => p t)
      (fun t => ContinuousMap.measurable_eval t))
      (fun p => (cappedBrownianFirstPassage c T (driftedBrownianPath a p) : WithTop ℝ≥0)) := by
  intro s
  have hm : Measurable[brownianRawFiltration (fun t (p : BrownianPath) => p t)
      (fun t => ContinuousMap.measurable_eval t) s]
      (fun p => driftedBrownianPath a (stopBrownianPath p s)) :=
    continuous_driftedBrownianPath.measurable.comp
      (measurable_const.prodMk (measurable_stopBrownianPath_raw s))
  have hcross : MeasurableSet[brownianRawFiltration (fun t (p : BrownianPath) => p t)
      (fun t => ContinuousMap.measurable_eval t) s]
      {p : BrownianPath | ∃ u ≤ s, c ≤ driftedBrownianPath a p u} := by
    have hglobal : MeasurableSet {p : BrownianPath | ∃ u ≤ s, c ≤ p u} :=
      ((brownianRawFiltration _ _).le s) _ (measurableSet_brownianPath_crossing s c)
    have hh := hglobal.preimage hm
    convert hh using 1
    ext p
    constructor
    · rintro ⟨u,hu,hcu⟩
      refine ⟨u,hu,?_⟩
      change c ≤ p (min u s)+a*(u : ℝ)
      rw [min_eq_left hu]
      exact hcu
    · rintro ⟨u,hu,hcu⟩
      refine ⟨u,hu,?_⟩
      change c ≤ p (min u s)+a*(u : ℝ) at hcu
      rwa [min_eq_left hu] at hcu
  have he : {p : BrownianPath | (cappedBrownianFirstPassage c T (driftedBrownianPath a p) : WithTop ℝ≥0) ≤ s} =
      if T ≤ s then univ else {p | ∃ u ≤ s, c ≤ driftedBrownianPath a p u} := by
    ext p
    simp only [WithTop.coe_le_coe,cappedBrownianFirstPassage_le_iff]
    by_cases hTs : T ≤ s
    · simp [hTs]
    · simp only [hTs,mem_ofPred_eq,false_or]
      exact ⟨fun ⟨u,hus,_,hcu⟩ => ⟨u,hus,hcu⟩,
        fun ⟨u,hus,hcu⟩ => ⟨u,hus,hus.trans (lt_of_not_ge hTs).le,hcu⟩⟩
  rw [he]
  split_ifs
  · exact MeasurableSet.univ
  · exact hcross

/-- Adding drift to a stopped mark clips that drift at the literal marked lifetime. -/
noncomputable def brownianDriftStoppedMark (a : ℝ) (u : StoppedBrownianPath) : StoppedBrownianPath :=
  (u.1,stopBrownianPath (driftedBrownianPath a u.2) u.1)

/-- Drift addition on lifetime-marked stopped paths is continuous. -/
theorem continuous_brownianDriftStoppedMark (a : ℝ) : Continuous (brownianDriftStoppedMark a) :=
  continuous_fst.prodMk (continuous_stopBrownianPath.comp (continuous_fst.prodMk
    (continuous_driftedBrownianPath.comp (continuous_const.prodMk continuous_snd))))

/-- Stopping before the marked time commutes with adding a clipped drift. -/
theorem brownianDriftStoppedMark_stop (a : ℝ) (τ : ℝ≥0) (p : BrownianPath) :
    brownianDriftStoppedMark a (τ,stopBrownianPath p τ) = (τ,stopBrownianPath (driftedBrownianPath a p) τ) := by
  unfold brownianDriftStoppedMark
  apply Prod.ext
  · rfl
  dsimp only [Prod.fst,Prod.snd]
  apply ContinuousMap.ext
  intro t
  change p (min (min t τ) τ)+a*((min t τ : ℝ≥0) : ℝ) = p (min t τ)+a*((min t τ : ℝ≥0) : ℝ)
  rw [min_eq_left (min_le_right _ _)]

/-- The lifetime-marked drifted prefix is measurable in its genuine stopping history. -/
theorem measurable_brownianDriftStoppedMark_stopped (a : ℝ) (τ : BrownianPath → ℝ≥0)
    (hτ : IsStoppingTime (brownianRawFiltration (fun t (p : BrownianPath) => p t)
      (fun t => ContinuousMap.measurable_eval t)) (fun p => (τ p : WithTop ℝ≥0))) :
    Measurable[hτ.measurableSpace] (fun p => (τ p,stopBrownianPath (driftedBrownianPath a p) (τ p))) := by
  convert (continuous_brownianDriftStoppedMark a).measurable.comp
    (measurable_brownianStoppedMark_stopped τ hτ) using 1
  funext p
  exact (brownianDriftStoppedMark_stop a (τ p) p).symm

/-- On a positive-drift first hit the opposite-drift terminal likelihood has a constant stopped factor. -/
theorem brownianPath_oppositeDrift_likelihood_factor (ν m : ℝ) (T : ℝ≥0) (p : BrownianPath)
    (h0 : p 0 < m) (hh : cappedBrownianFirstPassage m T (driftedBrownianPath ν p) < T) :
    brownianGaussianLikelihood (-2*ν) T (p T) = ENNReal.ofReal (Real.exp (-2*ν*m))*
      brownianGaussianLikelihood (-2*ν) (T-cappedBrownianFirstPassage m T (driftedBrownianPath ν p))
        (brownianShiftPath (cappedBrownianFirstPassage m T (driftedBrownianPath ν p)) p
          (T-cappedBrownianFirstPassage m T (driftedBrownianPath ν p))) := by
  let τ := cappedBrownianFirstPassage m T (driftedBrownianPath ν p)
  have hτT := cappedBrownianFirstPassage_le m T (driftedBrownianPath ν p)
  have h0' : driftedBrownianPath ν p 0 < m := by
    change p 0+ν*(0 : ℝ) < m
    simpa only [mul_zero,add_zero] using h0
  have hv := cappedBrownianFirstPassage_value m T (driftedBrownianPath ν p) h0' hh
  change p τ+ν*(τ : ℝ) = m at hv
  have he : p τ+brownianShiftPath τ p (T-τ) = p T := by
    change p τ+(p (τ+(T-τ))-p τ) = p T
    rw [add_tsub_cancel_of_le hτT]
    ring
  calc
    _ = brownianGaussianLikelihood (-2*ν) τ (p τ)*
        brownianGaussianLikelihood (-2*ν) (T-τ) (brownianShiftPath τ p (T-τ)) := by
      rw [← brownianGaussianLikelihood_add,add_tsub_cancel_of_le hτT,he]
    _ = _ := by
      congr 1
      unfold brownianGaussianLikelihood
      congr 2
      calc
        _ = (-2*ν)*(p τ+ν*(τ : ℝ)) := by ring
        _ = _ := by rw [hv]

/-- Capping the Brownian input at the terminal time preserves drifted capped first passage. -/
theorem cappedBrownianFirstPassage_drift_stop (a c : ℝ) (T : ℝ≥0) (p : BrownianPath) :
    cappedBrownianFirstPassage c T (driftedBrownianPath a (stopBrownianPath p T)) =
      cappedBrownianFirstPassage c T (driftedBrownianPath a p) := by
  unfold cappedBrownianFirstPassage
  congr 1
  congr 1
  ext u
  change (u ≤ T ∧ c ≤ p (min u T)+a*(u : ℝ)) ↔ (u ≤ T ∧ c ≤ p u+a*(u : ℝ))
  by_cases hu : u ≤ T
  · rw [min_eq_left hu]
  · simp only [hu,false_and]

/-- Stopping a drifted prefix no later than the cap ignores all later changes to the Brownian input. -/
theorem stopBrownianPath_drift_stop (a : ℝ) (τ T : ℝ≥0) (p : BrownianPath) (hτ : τ ≤ T) :
    stopBrownianPath (driftedBrownianPath a (stopBrownianPath p T)) τ =
      stopBrownianPath (driftedBrownianPath a p) τ := by
  apply ContinuousMap.ext
  intro t
  change p (min (min t τ) T)+a*((min t τ : ℝ≥0) : ℝ) = p (min t τ)+a*((min t τ : ℝ≥0) : ℝ)
  rw [min_eq_left ((min_le_right _ _).trans hτ)]

/-- Successive literal drift translations add their parameters. -/
theorem driftedBrownianPath_add (a b : ℝ) (p : BrownianPath) :
    driftedBrownianPath a (driftedBrownianPath b p) = driftedBrownianPath (a+b) p := by
  apply ContinuousMap.ext
  intro t
  change (p t+b*(t : ℝ))+a*(t : ℝ) = p t+(a+b)*(t : ℝ)
  ring

/-- Finite first-hit prefixes change from positive to negative drift by the exact constant likelihood. -/
theorem brownianPath_oppositeDrift_firstHit_marked_lintegral (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν m : ℝ) (hm : 0 < m) (T : ℝ≥0)
    (F : StoppedBrownianPath → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p in {p | cappedBrownianFirstPassage m T (driftedBrownianPath (-ν) p) < T},
      F (cappedBrownianFirstPassage m T (driftedBrownianPath (-ν) p),
        stopBrownianPath (driftedBrownianPath (-ν) p)
          (cappedBrownianFirstPassage m T (driftedBrownianPath (-ν) p))) ∂P) =
      ENNReal.ofReal (Real.exp (-2*ν*m))*
        ∫⁻ p in {p | cappedBrownianFirstPassage m T (driftedBrownianPath ν p) < T},
          F (cappedBrownianFirstPassage m T (driftedBrownianPath ν p),
            stopBrownianPath (driftedBrownianPath ν p)
              (cappedBrownianFirstPassage m T (driftedBrownianPath ν p))) ∂P := by
  classical
  let τ : BrownianPath → ℝ≥0 := fun p => cappedBrownianFirstPassage m T (driftedBrownianPath ν p)
  have hτ := cappedBrownianFirstPassage_drift_isStoppingTime ν m T
  have hmτ := measurable_finite_brownian_stoppingTime _ τ hτ
  let H : Set BrownianPath := {p | τ p < T}
  have hH : MeasurableSet H := measurableSet_lt hmτ measurable_const
  let A : BrownianPath → StoppedBrownianPath :=
    fun p => (τ p,stopBrownianPath (driftedBrownianPath ν p) (τ p))
  have hmA : Measurable A := (measurable_brownianDriftStoppedMark_stopped ν τ hτ).mono
    hτ.measurableSpace_le le_rfl
  let J : BrownianPath → ℝ≥0∞ := H.indicator (fun p => F (A p))
  have hJ : Measurable J := (hF.comp hmA).indicator hH
  have hJstop (p : BrownianPath) : J (stopBrownianPath p T) = J p := by
    have htime : τ (stopBrownianPath p T) = τ p := cappedBrownianFirstPassage_drift_stop ν m T p
    have hpath := stopBrownianPath_drift_stop ν (τ p) T p (cappedBrownianFirstPassage_le m T _)
    simp only [J,H,A,Set.indicator_apply,mem_ofPred_eq,htime,hpath]
  have htilt := brownianFiniteTilt_stoppedPath_lintegral_all P hB.toIsPreBrownianReal (-2*ν) T J hJ
  have hds : ∀ p : BrownianPath, driftedBrownianPath ν (driftedBrownianPath (-2*ν) p) =
      driftedBrownianPath (-ν) p := by
    intro p
    rw [driftedBrownianPath_add]
    congr 1
    ring
  have hl : (fun p => J (stopBrownianPath (driftedBrownianPath (-2*ν) p) T)) =
      {p : BrownianPath | cappedBrownianFirstPassage m T (driftedBrownianPath (-ν) p) < T}.indicator
        (fun p => F (cappedBrownianFirstPassage m T (driftedBrownianPath (-ν) p),
          stopBrownianPath (driftedBrownianPath (-ν) p)
            (cappedBrownianFirstPassage m T (driftedBrownianPath (-ν) p)))) := by
    funext p
    rw [hJstop]
    simp only [J,H,A,τ,hds,Set.indicator_apply,mem_ofPred_eq]
  let L : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-2*ν*m))
  let F' : StoppedBrownianPath → ℝ≥0∞ :=
    (Prod.fst ⁻¹' Iio T).indicator (fun u => L*F (brownianDriftStoppedMark ν u))
  have hF' : Measurable F' := (measurable_const.mul
    (hF.comp (continuous_brownianDriftStoppedMark ν).measurable)).indicator
      (measurableSet_Iio.preimage measurable_fst)
  have hrem := brownianPath_bounded_restart_remainingLikelihood_marked P hB τ hτ T
    (fun p => cappedBrownianFirstPassage_le m T _) (-2*ν) F' hF'
  have hr : (fun p => brownianGaussianLikelihood (-2*ν) T (p T)*J (stopBrownianPath p T)) =ᵐ[P]
      (fun p => F' (τ p,stopBrownianPath p (τ p))*brownianGaussianLikelihood (-2*ν) (T-τ p)
        (brownianShiftPath (τ p) p (T-τ p))) := by
    filter_upwards [hB.eval_zero_ae_eq_zero] with p hp0
    rw [hJstop]
    by_cases hp : τ p < T
    · have hf := brownianPath_oppositeDrift_likelihood_factor ν m T p (hp0 ▸ hm) hp
      simp only [J,H,F',A,Set.indicator_apply,mem_ofPred_eq,mem_preimage,mem_Iio,
        ite_eq_left hp,brownianDriftStoppedMark_stop]
      rw [hf]
      exact mul_right_comm _ _ _
    · simp only [J,H,F',Set.indicator_apply,mem_ofPred_eq,mem_preimage,mem_Iio,
        ite_eq_right hp,mul_zero,zero_mul]
  have hr' : (fun p => F' (τ p,stopBrownianPath p (τ p))) = (fun p => L*J p) := by
    funext p
    simp only [F',J,H,A,Set.indicator_apply,mem_ofPred_eq,mem_preimage,mem_Iio,
      brownianDriftStoppedMark_stop]
    split_ifs <;> simp only [mul_zero]
  rw [hl] at htilt
  have hneg : MeasurableSet {p : BrownianPath | cappedBrownianFirstPassage m T (driftedBrownianPath (-ν) p) < T} :=
    measurableSet_lt (measurable_finite_brownian_stoppingTime _ _
      (cappedBrownianFirstPassage_drift_isStoppingTime (-ν) m T)) measurable_const
  rw [lintegral_indicator hneg] at htilt
  calc
    _ = _ := htilt
    _ = _ := lintegral_congr_ae hr
    _ = _ := hrem
    _ = L*∫⁻ p, J p ∂P := by rw [hr',lintegral_const_mul L hJ]
    _ = _ := by
      simp only [J,lintegral_indicator hH]
      rfl

/-- Restart factors every marked stopped prefix and every full drifted future test. -/
theorem brownianPath_bounded_restart_marked_lintegral (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (τ : BrownianPath → ℝ≥0)
    (hτ : IsStoppingTime (brownianRawFiltration (fun t (p : BrownianPath) => p t)
      (fun t => ContinuousMap.measurable_eval t)) (fun p => (τ p : WithTop ℝ≥0)))
    (T : ℝ≥0) (hτT : ∀ p, τ p ≤ T) (a : ℝ)
    (F : StoppedBrownianPath → ℝ≥0∞) (hF : Measurable F)
    (G : BrownianPath → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ p, F (τ p,stopBrownianPath (driftedBrownianPath a p) (τ p))*
      G (driftedBrownianPath a (brownianShiftPath (τ p) p)) ∂P) =
      (∫⁻ p, F (τ p,stopBrownianPath (driftedBrownianPath a p) (τ p)) ∂P)*
        ∫⁻ q, G (driftedBrownianPath a q) ∂P := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  let X : BrownianPath → StoppedBrownianPath :=
    fun p => (τ p,stopBrownianPath (driftedBrownianPath a p) (τ p))
  have hX := measurable_brownianDriftStoppedMark_stopped a τ hτ
  have hmX : Measurable X := hX.mono hτ.measurableSpace_le le_rfl
  have hmτ := measurable_finite_brownian_stoppingTime _ τ hτ
  have hmV : Measurable (fun p => brownianShiftPath (τ p) p) :=
    continuous_brownianShiftPath.measurable.comp (hmτ.prodMk measurable_id)
  have hmD : Measurable (driftedBrownianPath a) :=
    continuous_driftedBrownianPath.measurable.comp (measurable_const.prodMk measurable_id)
  let J : StoppedBrownianPath × BrownianPath → ℝ≥0∞ := fun z => F z.1*G (driftedBrownianPath a z.2)
  have hJ : Measurable J := (hF.comp measurable_fst).mul (hG.comp (hmD.comp measurable_snd))
  calc
    _ = ∫⁻ z, J z ∂P.map (fun p => (X p,brownianShiftPath (τ p) p)) :=
      (lintegral_map hJ (hmX.prodMk hmV)).symm
    _ = ∫⁻ z, J z ∂(P.map X).prod P := by
      rw [brownianPath_bounded_restart_joint_map P hB τ hτ T hτT X hX]
    _ = (∫⁻ u, F u ∂P.map X)*∫⁻ q, G (driftedBrownianPath a q) ∂P := by
      exact lintegral_prod_mul (hF.aemeasurable) (hG.comp hmD).aemeasurable
    _ = _ := by rw [lintegral_map hF hmX]

/-- Finite first-hit band tests factor at the genuine negative-drift stopping time. -/
theorem brownianPath_oppositeDrift_firstHit_marked_future_lintegral (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν m : ℝ) (hm : 0 < m) (T : ℝ≥0)
    (F : StoppedBrownianPath → ℝ≥0∞) (hF : Measurable F)
    (G : BrownianPath → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ p in {p | cappedBrownianFirstPassage m T (driftedBrownianPath (-ν) p) < T},
      F (cappedBrownianFirstPassage m T (driftedBrownianPath (-ν) p),
        stopBrownianPath (driftedBrownianPath (-ν) p)
          (cappedBrownianFirstPassage m T (driftedBrownianPath (-ν) p)))*
      G (driftedBrownianPath (-ν) (brownianShiftPath
        (cappedBrownianFirstPassage m T (driftedBrownianPath (-ν) p)) p)) ∂P) =
      ENNReal.ofReal (Real.exp (-2*ν*m))*
        (∫⁻ p in {p | cappedBrownianFirstPassage m T (driftedBrownianPath ν p) < T},
          F (cappedBrownianFirstPassage m T (driftedBrownianPath ν p),
            stopBrownianPath (driftedBrownianPath ν p)
              (cappedBrownianFirstPassage m T (driftedBrownianPath ν p))) ∂P)*
        ∫⁻ q, G (driftedBrownianPath (-ν) q) ∂P := by
  classical
  let τ : BrownianPath → ℝ≥0 := fun p => cappedBrownianFirstPassage m T (driftedBrownianPath (-ν) p)
  have hτ := cappedBrownianFirstPassage_drift_isStoppingTime (-ν) m T
  have hmτ := measurable_finite_brownian_stoppingTime _ τ hτ
  let H : Set BrownianPath := {p | τ p < T}
  have hH : MeasurableSet H := measurableSet_lt hmτ measurable_const
  let F' : StoppedBrownianPath → ℝ≥0∞ := (Prod.fst ⁻¹' Iio T).indicator F
  have hF' : Measurable F' := hF.indicator (measurableSet_Iio.preimage measurable_fst)
  have he := brownianPath_bounded_restart_marked_lintegral P hB τ hτ T
    (fun p => cappedBrownianFirstPassage_le m T _) (-ν) F' hF' G hG
  have hl : (fun p => F' (τ p,stopBrownianPath (driftedBrownianPath (-ν) p) (τ p))*
      G (driftedBrownianPath (-ν) (brownianShiftPath (τ p) p))) =
      H.indicator (fun p => F (τ p,stopBrownianPath (driftedBrownianPath (-ν) p) (τ p))*
        G (driftedBrownianPath (-ν) (brownianShiftPath (τ p) p))) := by
    funext p
    simp only [F',H,Set.indicator_apply,mem_ofPred_eq,mem_preimage,mem_Iio]
    split_ifs <;> simp only [zero_mul]
  have hr : (fun p => F' (τ p,stopBrownianPath (driftedBrownianPath (-ν) p) (τ p))) =
      H.indicator (fun p => F (τ p,stopBrownianPath (driftedBrownianPath (-ν) p) (τ p))) := by
    funext p
    simp only [F',H,Set.indicator_apply,mem_ofPred_eq,mem_preimage,mem_Iio]
  rw [hl,hr,lintegral_indicator hH,lintegral_indicator hH] at he
  exact he.trans (by rw [brownianPath_oppositeDrift_firstHit_marked_lintegral P hB ν m hm T F hF])

/-- The preterminal capped-hit event excludes the no-hit value zero. -/
theorem cappedBrownianFirstPassage_lt_iff_hit (p : BrownianPath) (m : ℝ) (T : ℝ≥0) :
    cappedBrownianFirstPassage m T p < T ↔
      (∃ u : ℝ≥0, m ≤ p u) ∧ firstPassageTime p m < T := by
  constructor
  · intro hc
    have hh : m ≤ p (cappedBrownianFirstPassage m T p) := by
      rcases cappedBrownianFirstPassage_mem m T p with hh | he
      · exact hh.2
      · exact (hc.ne he).elim
    have he := firstPassageTime_eq_capped_of_hit p m T
      ⟨_,(cappedBrownianFirstPassage_le m T p),hh⟩
    exact ⟨⟨_,hh⟩,he ▸ hc⟩
  · rintro ⟨hh,ht⟩
    have he := firstPassageTime_eq_capped_of_hit p m T
      ⟨firstPassageTime p m,ht.le,firstPassageTime_mem p m hh⟩
    exact he ▸ ht

/-- Every preterminal capped hit test is the actual first-hit test on its actual hitting event. -/
theorem brownianPath_capped_hit_setLIntegral_eq (P : Measure BrownianPath)
    (a m : ℝ) (T : ℝ≥0) (F : ℝ≥0 × BrownianPath → ℝ≥0∞) :
    (∫⁻ p in {p | cappedBrownianFirstPassage m T (driftedBrownianPath a p) < T},
      F (cappedBrownianFirstPassage m T (driftedBrownianPath a p),p) ∂P) =
      ∫⁻ p in {p | (∃ u : ℝ≥0, m ≤ driftedBrownianPath a p u) ∧
        firstPassageTime (driftedBrownianPath a p) m < T},
        F (firstPassageTime (driftedBrownianPath a p) m,p) ∂P := by
  have he : {p : BrownianPath | cappedBrownianFirstPassage m T (driftedBrownianPath a p) < T} =
      {p | (∃ u : ℝ≥0, m ≤ driftedBrownianPath a p u) ∧
        firstPassageTime (driftedBrownianPath a p) m < T} := by
    ext p
    exact cappedBrownianFirstPassage_lt_iff_hit _ m T
  rw [he]
  have hmD : Measurable (driftedBrownianPath a) :=
    continuous_driftedBrownianPath.measurable.comp (measurable_const.prodMk measurable_id)
  have hset : MeasurableSet {p : BrownianPath | (∃ u : ℝ≥0, m ≤ driftedBrownianPath a p u) ∧
      firstPassageTime (driftedBrownianPath a p) m < T} :=
    (measurableSet_brownianPath_joint_hit.preimage (measurable_const.prodMk hmD)).inter
      (measurableSet_lt (measurable_coe_nnreal_real.comp ((measurable_firstPassageTime m).comp hmD)) measurable_const)
  apply setLIntegral_congr_fun hset
  intro p hp
  have hh := firstPassageTime_eq_capped_of_hit (driftedBrownianPath a p) m T
    ⟨_,hp.2.le,firstPassageTime_mem _ m hp.1⟩
  change F (cappedBrownianFirstPassage m T (driftedBrownianPath a p),p) =
    F (firstPassageTime (driftedBrownianPath a p) m,p)
  rw [hh]

/-- Infinite-horizon restart and opposite-drift likelihood hold for the entire actual first-hit prefix. -/
theorem brownianPath_oppositeDrift_firstHit_full_lintegral (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν m : ℝ) (hν : 0 < ν) (hm : 0 < m)
    (F : StoppedBrownianPath → ℝ≥0∞) (hF : Measurable F)
    (G : BrownianPath → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ p in {p | ∃ u : ℝ≥0, m ≤ driftedBrownianPath (-ν) p u},
      F (positiveDriftFirstHitSegment (-ν) m p)*
        G (driftedBrownianPath (-ν) (brownianShiftPath
          (firstPassageTime (driftedBrownianPath (-ν) p) m) p)) ∂P) =
      ENNReal.ofReal (Real.exp (-2*ν*m))*
        (∫⁻ p, F (positiveDriftFirstHitSegment ν m p) ∂P)*
        ∫⁻ q, G (driftedBrownianPath (-ν) q) ∂P := by
  let E : ℝ → Set BrownianPath := fun a => {p | ∃ u : ℝ≥0, m ≤ driftedBrownianPath a p u}
  let S : ℝ → ℕ → Set BrownianPath := fun a n =>
    {p | (∃ u : ℝ≥0, m ≤ driftedBrownianPath a p u) ∧
      firstPassageTime (driftedBrownianPath a p) m < (n : ℝ≥0)+1}
  have hmono (a : ℝ) : Monotone (S a) := by
    intro n k hnk p hp
    have hnk' : (n : ℝ≥0)+1 ≤ (k : ℝ≥0)+1 := by exact_mod_cast Nat.add_le_add_right hnk 1
    exact ⟨hp.1,hp.2.trans_le hnk'⟩
  have hunion (a : ℝ) : (⋃ n, S a n) = E a := by
    ext p
    simp only [S,E,mem_iUnion,mem_ofPred_eq]
    constructor
    · rintro ⟨n,hh,_⟩
      exact hh
    · intro hh
      obtain ⟨n,hn⟩ := exists_nat_gt (firstPassageTime (driftedBrownianPath a p) m : ℝ)
      have hn' : firstPassageTime (driftedBrownianPath a p) m < (n : ℝ≥0) := by exact_mod_cast hn
      exact ⟨n,hh,hn'.trans (lt_add_one _)⟩
  let J : BrownianPath → ℝ≥0∞ := fun p => F (positiveDriftFirstHitSegment (-ν) m p)*
    G (driftedBrownianPath (-ν) (brownianShiftPath (firstPassageTime (driftedBrownianPath (-ν) p) m) p))
  let K : BrownianPath → ℝ≥0∞ := fun p => F (positiveDriftFirstHitSegment ν m p)
  let L : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-2*ν*m))
  let C : ℝ≥0∞ := ∫⁻ q, G (driftedBrownianPath (-ν) q) ∂P
  have he (n : ℕ) : (∫⁻ p in S (-ν) n, J p ∂P) = L*(∫⁻ p in S ν n, K p ∂P)*C := by
    have hh := brownianPath_oppositeDrift_firstHit_marked_future_lintegral P hB ν m hm
      ((n : ℝ≥0)+1) F hF G hG
    have hleft := brownianPath_capped_hit_setLIntegral_eq P (-ν) m ((n : ℝ≥0)+1)
      (fun z => F (z.1,stopBrownianPath (driftedBrownianPath (-ν) z.2) z.1)*
        G (driftedBrownianPath (-ν) (brownianShiftPath z.1 z.2)))
    have hright := brownianPath_capped_hit_setLIntegral_eq P ν m ((n : ℝ≥0)+1)
      (fun z => F (z.1,stopBrownianPath (driftedBrownianPath ν z.2) z.1))
    exact hleft.symm.trans (hh.trans (by rw [hright]; rfl))
  have hEp : P.restrict (E ν) = P := Measure.restrict_eq_self_of_ae_mem
    (brownianPath_positiveDrift_hits_ae P hB ν m hν)
  calc
    _ = ⨆ n, ∫⁻ p in S (-ν) n, J p ∂P := by
      change (∫⁻ p in E (-ν), J p ∂P) = _
      rw [← hunion (-ν)]
      exact setLIntegral_iUnion_of_directed J (hmono (-ν)).directed_le
    _ = ⨆ n, L*(∫⁻ p in S ν n, K p ∂P)*C := by simp_rw [he]
    _ = L*(⨆ n, ∫⁻ p in S ν n, K p ∂P)*C := by rw [← ENNReal.iSup_mul,← ENNReal.mul_iSup]
    _ = L*(∫⁻ p in E ν, K p ∂P)*C := by
      rw [← setLIntegral_iUnion_of_directed K (hmono ν).directed_le,hunion ν]
    _ = _ := by rw [hEp]

/-- Staying strictly below a constant level is a measurable whole-path event. -/
theorem measurableSet_brownianPath_below (ε : ℝ) :
    MeasurableSet {p : BrownianPath | ∀ t : ℝ≥0, p t < ε} := by
  have hh := measurableSet_brownianPath_joint_hit.preimage
    (measurable_const.prodMk measurable_id : Measurable (fun p : BrownianPath => (ε,p)))
  convert hh.compl using 1
  ext p
  simp only [mem_compl_iff,mem_preimage,mem_ofPred_eq,not_exists,not_le]

/-- Every point no later than an actual first hit lies at or below its level. -/
theorem brownianPath_le_before_firstPassage (p : BrownianPath) (m : ℝ)
    (h0 : p 0 < m) (hh : ∃ u : ℝ≥0, m ≤ p u) (t : ℝ≥0) (ht : t ≤ firstPassageTime p m) :
    p t ≤ m := by
  rcases ht.eq_or_lt with ht | ht
  · rw [ht,firstPassageTime_value_of_hit p m h0 hh]
  · have hn : ¬m ≤ p t := by
      intro h
      exact (not_le.mpr ht) (csInf_le (s := {u : ℝ≥0 | m ≤ p u}) (OrderBot.bddBelow _) h)
    exact (not_le.mp hn).le

/-- A thin maximum band is exactly a first hit followed by avoidance of the upper edge. -/
theorem brownianPath_maximum_band_iff (ν m ε : ℝ) (p : BrownianPath)
    (hm : p 0 < m) (hε : 0 < ε)
    (hb : BddAbove (range (fun t : ℝ≥0 => p t-ν*(t : ℝ))))
    (hat : ∃ σ : ℝ≥0, p σ-ν*(σ : ℝ) = driftedBrownianMaximum ν p) :
    (m ≤ driftedBrownianMaximum ν p ∧ driftedBrownianMaximum ν p < m+ε) ↔
      (∃ u : ℝ≥0, m ≤ driftedBrownianPath (-ν) p u) ∧
        ∀ t : ℝ≥0, driftedBrownianPath (-ν)
          (brownianShiftPath (firstPassageTime (driftedBrownianPath (-ν) p) m) p) t < ε := by
  let X := driftedBrownianPath (-ν) p
  let τ := firstPassageTime X m
  have hX0 : X 0 < m := by
    change p 0+(-ν)*(0 : ℝ) < m
    simpa only [mul_zero,add_zero] using hm
  have hmax (t : ℝ≥0) : p t-ν*(t : ℝ) ≤ driftedBrownianMaximum ν p := le_csSup hb (mem_range_self t)
  constructor
  · rintro ⟨hlo,hhi⟩
    have hh : ∃ u : ℝ≥0, m ≤ X u := by
      obtain ⟨σ,hσ⟩ := hat
      refine ⟨σ,?_⟩
      change m ≤ p σ+(-ν)*(σ : ℝ)
      simpa only [neg_mul,← sub_eq_add_neg] using hσ ▸ hlo
    refine ⟨hh,fun t => ?_⟩
    have hv := firstPassageTime_value_of_hit X m hX0 hh
    change p τ+(-ν)*(τ : ℝ) = m at hv
    have ht := (hmax (τ+t)).trans_lt hhi
    rw [NNReal.coe_add] at ht
    change (p (τ+t)-p τ)+(-ν)*(t : ℝ) < ε
    linarith only [ht,hv]
  · rintro ⟨hh,hfuture⟩
    have hv := firstPassageTime_value_of_hit X m hX0 hh
    have hlo : m ≤ driftedBrownianMaximum ν p := by
      have hl := hmax τ
      change p τ+(-ν)*(τ : ℝ) = m at hv
      linarith only [hl,hv]
    refine ⟨hlo,?_⟩
    obtain ⟨σ,hσ⟩ := hat
    by_cases hστ : σ ≤ τ
    · have hl := brownianPath_le_before_firstPassage X m hX0 hh σ hστ
      change p σ+(-ν)*(σ : ℝ) ≤ m at hl
      have hh' : p σ-ν*(σ : ℝ) ≤ m := by simpa only [neg_mul,← sub_eq_add_neg] using hl
      rw [hσ] at hh'
      exact hh'.trans_lt (lt_add_of_pos_right m hε)
    · have hτσ : τ ≤ σ := (lt_of_not_ge hστ).le
      have ht := hfuture (σ-τ)
      change (p (τ+(σ-τ))-p τ)+(-ν)*((σ-τ : ℝ≥0) : ℝ) < ε at ht
      rw [add_tsub_cancel_of_le hτσ,NNReal.coe_sub hτσ] at ht
      change p τ+(-ν)*(τ : ℝ) = m at hv
      linarith only [ht,hv,hσ]

/-- The exact thin-band identity on actual paths, with its full stopped prefix and future. -/
theorem brownianPath_maximum_band_lintegral (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν m ε : ℝ)
    (hν : 0 < ν) (hm : 0 < m) (hε : 0 < ε)
    (F : StoppedBrownianPath → ℝ≥0∞) (hF : Measurable F)
    (G : BrownianPath → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ p in {p | m ≤ driftedBrownianMaximum ν p ∧ driftedBrownianMaximum ν p < m+ε},
      F (positiveDriftFirstHitSegment (-ν) m p)*
        G (driftedBrownianPath (-ν) (brownianShiftPath
          (firstPassageTime (driftedBrownianPath (-ν) p) m) p)) ∂P) =
      ENNReal.ofReal (Real.exp (-2*ν*m))*(∫⁻ p, F (positiveDriftFirstHitSegment ν m p) ∂P)*
        ∫⁻ q in {q | ∀ t : ℝ≥0, driftedBrownianPath (-ν) q t < ε},
          G (driftedBrownianPath (-ν) q) ∂P := by
  classical
  let E : Set BrownianPath := {q | ∀ t : ℝ≥0, q t < ε}
  have hE : MeasurableSet E := measurableSet_brownianPath_below ε
  let G' : BrownianPath → ℝ≥0∞ := E.indicator G
  have hG' : Measurable G' := hG.indicator hE
  have he := brownianPath_oppositeDrift_firstHit_full_lintegral P hB ν m hν hm F hF G' hG'
  let H : Set BrownianPath := {p | ∃ u : ℝ≥0, m ≤ driftedBrownianPath (-ν) p u}
  have hmD : Measurable (driftedBrownianPath (-ν)) :=
    continuous_driftedBrownianPath.measurable.comp (measurable_const.prodMk measurable_id)
  have hH : MeasurableSet H := measurableSet_brownianPath_joint_hit.preimage (measurable_const.prodMk hmD)
  let B : Set BrownianPath := {p | m ≤ driftedBrownianMaximum ν p ∧ driftedBrownianMaximum ν p < m+ε}
  have hM := aemeasurable_driftedBrownianMaximum P hB ν hν
  have hBset : NullMeasurableSet B P := hM.nullMeasurableSet_preimage measurableSet_Ico
  let V : BrownianPath → BrownianPath := fun p => driftedBrownianPath (-ν)
    (brownianShiftPath (firstPassageTime (driftedBrownianPath (-ν) p) m) p)
  have hl : H.indicator (fun p => F (positiveDriftFirstHitSegment (-ν) m p)*G' (V p)) =ᵐ[P]
      B.indicator (fun p => F (positiveDriftFirstHitSegment (-ν) m p)*G (V p)) := by
    filter_upwards [brownianPath_negativeDrift_maximum_attained_ae P hB ν hν,hB.eval_zero_ae_eq_zero]
      with p hp hp0
    have hb := brownianPath_maximum_band_iff ν m ε p (hp0 ▸ hm) hε hp.1 hp.2
    change (p ∈ B ↔ p ∈ H ∧ V p ∈ E) at hb
    by_cases hhit : p ∈ H
    · by_cases hav : V p ∈ E
      · simp only [Set.indicator_apply,ite_eq_left hhit,ite_eq_left hav,G',ite_eq_left (hb.mpr ⟨hhit,hav⟩)]
      · simp only [Set.indicator_apply,ite_eq_left hhit,ite_eq_right hav,G',mul_zero,
          ite_eq_right (fun h => hav (hb.mp h).2)]
    · simp only [Set.indicator_apply,ite_eq_right hhit,ite_eq_right (fun h => hhit (hb.mp h).1)]
  have hr : (fun q => G' (driftedBrownianPath (-ν) q)) =
      {q : BrownianPath | ∀ t : ℝ≥0, driftedBrownianPath (-ν) q t < ε}.indicator
        (fun q => G (driftedBrownianPath (-ν) q)) := by
    funext q
    simp only [G',E,Set.indicator_apply,mem_ofPred_eq]
  have hbelow : MeasurableSet {q : BrownianPath | ∀ t : ℝ≥0, driftedBrownianPath (-ν) q t < ε} := hE.preimage hmD
  rw [hr,lintegral_indicator hbelow] at he
  rw [← lintegral_indicator hH] at he
  rw [lintegral_congr_ae hl,lintegral_indicator₀ hBset] at he
  exact he

/-- Whole-path upper avoidance has exactly the harmonic survival probability. -/
theorem brownianPath_below_measure (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν ε : ℝ) (hν : 0 < ν) (hε : 0 < ε) :
    P {p | ∀ t : ℝ≥0, driftedBrownianPath (-ν) p t < ε} =
      ENNReal.ofReal (conditionedH ν ε) := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hM := aemeasurable_driftedBrownianMaximum P hB ν hν
  have hzero : P.map (driftedBrownianMaximum ν) {ε} = 0 := by
    rw [brownianPath_globalMaximum_map P hB ν hν]
    let _ := noAtoms_brownianMaximumReferenceLaw ν
    exact measure_singleton ε
  have hne : ∀ᵐ x ∂P.map (driftedBrownianMaximum ν), x ≠ ε := by
    simpa only [ae_iff,Classical.not_not,Set.ofPred_eq_eq_singleton] using hzero
  have hi : P.map (driftedBrownianMaximum ν) (Ici ε) =
      P.map (driftedBrownianMaximum ν) (Ioi ε) := by
    apply measure_congr
    filter_upwards [hne] with x hx
    exact propext (le_iff_lt_or_eq.trans (or_iff_left hx.symm))
  have he : {p : BrownianPath | ∀ t : ℝ≥0, driftedBrownianPath (-ν) p t < ε} =ᵐ[P]
      driftedBrownianMaximum ν ⁻¹' Iio ε := by
    filter_upwards [brownianPath_negativeDrift_maximum_attained_ae P hB ν hν] with p hp
    apply propext
    constructor
    · intro hh
      obtain ⟨σ,hσ⟩ := hp.2
      have hs := hh σ
      change p σ+(-ν)*(σ : ℝ) < ε at hs
      change driftedBrownianMaximum ν p < ε
      simpa only [neg_mul,← sub_eq_add_neg,hσ] using hs
    · intro hh t
      have ht := le_csSup hp.1 (mem_range_self t)
      change driftedBrownianMaximum ν p < ε at hh
      change driftedBrownianPath (-ν) p t < ε
      change p t+(-ν)*(t : ℝ) < ε
      have hh' : p t-ν*(t : ℝ) < ε := ht.trans_lt hh
      simpa only [neg_mul,← sub_eq_add_neg] using hh'
  rw [measure_congr he,← Measure.map_apply_of_aemeasurable hM measurableSet_Iio,
    ← compl_Ici,prob_compl_eq_one_sub measurableSet_Ici,hi,
    brownianPath_globalMaximum_Ioi P hB ν ε hν hε.le]
  rw [conditionedH,ite_eq_right hν.ne',ENNReal.ofReal_sub 1 (Real.exp_pos _).le,ENNReal.ofReal_one]

/-- The actual law of negative-drift Brownian motion conditioned below a positive upper level. -/
noncomputable def brownianBelowConditionedLaw (P : Measure BrownianPath) (ν ε : ℝ) :
    Measure BrownianPath :=
  (ENNReal.ofReal (conditionedH ν ε))⁻¹ •
    (P.restrict {p | ∀ t : ℝ≥0, driftedBrownianPath (-ν) p t < ε}).map (driftedBrownianPath (-ν))

/-- The actual upper-conditioned future law is normalized, without an entrance-law assumption. -/
theorem isProbabilityMeasure_brownianBelowConditionedLaw (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν ε : ℝ) (hν : 0 < ν) (hε : 0 < ε) :
    IsProbabilityMeasure (brownianBelowConditionedLaw P ν ε) := by
  have hh : 0 < conditionedH ν ε := by
    rw [conditionedH,ite_eq_right hν.ne']
    apply sub_pos.mpr
    exact Real.exp_lt_one_iff.mpr (by nlinarith only [hν,hε])
  have hn : ENNReal.ofReal (conditionedH ν ε) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hh)
  have hmD : Measurable (driftedBrownianPath (-ν)) :=
    continuous_driftedBrownianPath.measurable.comp (measurable_const.prodMk measurable_id)
  refine ⟨?_⟩
  rw [brownianBelowConditionedLaw,Measure.smul_apply,smul_eq_mul,Measure.map_apply hmD MeasurableSet.univ,
    preimage_univ,Measure.restrict_apply MeasurableSet.univ,univ_inter,
    brownianPath_below_measure P hB ν ε hν hε,ENNReal.inv_mul_cancel hn ENNReal.ofReal_ne_top]

/-- Every test of the upper-conditioned law is its exact normalized avoidance integral. -/
theorem lintegral_brownianBelowConditionedLaw (P : Measure BrownianPath) (ν ε : ℝ)
    (G : BrownianPath → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ q, G q ∂brownianBelowConditionedLaw P ν ε) =
      (ENNReal.ofReal (conditionedH ν ε))⁻¹*
        ∫⁻ q in {q | ∀ t : ℝ≥0, driftedBrownianPath (-ν) q t < ε},
          G (driftedBrownianPath (-ν) q) ∂P := by
  have hmD : Measurable (driftedBrownianPath (-ν)) :=
    continuous_driftedBrownianPath.measurable.comp (measurable_const.prodMk measurable_id)
  rw [brownianBelowConditionedLaw,lintegral_smul_measure,smul_eq_mul,lintegral_map hG hmD]

/-- Conditioning below the band edge restores its exact harmonic mass for every nonnegative test. -/
theorem brownianPath_below_lintegral_eq_conditioned (P : Measure BrownianPath)
    (ν ε : ℝ) (hν : 0 < ν) (hε : 0 < ε)
    (G : BrownianPath → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ q in {q | ∀ t : ℝ≥0, driftedBrownianPath (-ν) q t < ε},
      G (driftedBrownianPath (-ν) q) ∂P) =
      ENNReal.ofReal (conditionedH ν ε)*∫⁻ q, G q ∂brownianBelowConditionedLaw P ν ε := by
  have hh : 0 < conditionedH ν ε := by
    rw [conditionedH,ite_eq_right hν.ne']
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith only [hν,hε]))
  rw [lintegral_brownianBelowConditionedLaw P ν ε G hG,← mul_assoc,
    ENNReal.mul_inv_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hh)) ENNReal.ofReal_ne_top,one_mul]

/-- The exact source thin-band identity, including its normalized future law and both scalar factors. -/
theorem brownianPath_williams_thinBand_lintegral (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν m ε : ℝ)
    (hν : 0 < ν) (hm : 0 < m) (hε : 0 < ε)
    (F : StoppedBrownianPath → ℝ≥0∞) (hF : Measurable F)
    (G : BrownianPath → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ p in {p | m ≤ driftedBrownianMaximum ν p ∧ driftedBrownianMaximum ν p < m+ε},
      F (positiveDriftFirstHitSegment (-ν) m p)*
        G (driftedBrownianPath (-ν) (brownianShiftPath
          (firstPassageTime (driftedBrownianPath (-ν) p) m) p)) ∂P) =
      ENNReal.ofReal (Real.exp (-2*ν*m))*ENNReal.ofReal (conditionedH ν ε)*
        (∫⁻ p, F (positiveDriftFirstHitSegment ν m p) ∂P)*
        ∫⁻ q, G q ∂brownianBelowConditionedLaw P ν ε := by
  rw [brownianPath_maximum_band_lintegral P hB ν m ε hν hm hε F hF G hG,
    brownianPath_below_lintegral_eq_conditioned P ν ε hν hε G hG]
  ring


end DOZZ.Proofs

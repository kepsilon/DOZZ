/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Brownian.Barrier.KilledEndpoint

/-!
# Stopped first-hit likelihood and the actual lifetime tilt

The full-path bounded restart law factors a stopped clock and the remaining
Brownian path. Tonelli's theorem and the Gaussian exponential expectation
remove the remaining likelihood for every nonnegative measurable clock test.
No integrability restriction on that test is required.

On the event of a preterminal hit, continuity gives the exact hit value. The
terminal likelihood therefore factors into the stopped likelihood and an
independent remaining Gaussian likelihood. This proves the stopped
change-of-drift identity at the actual capped first hit.

Stopping a path at its terminal horizon preserves its capped first-hit time.
The finite-horizon path tilt consequently transports every preterminal
first-hit lifetime test with exactly the stopped scalar likelihood.

Zero drift reaches every fixed positive level almost surely: the no-hit event
lies in every finite-horizon barrier event, and the half-normal bound vanishes at
square integer horizons. Positive drift has its previously proved hitting
assertion. Both literal first-passage lifetimes have positive duration and no
overshoot.

The first-passage convention is treated explicitly. The infimum of an empty
hitting set is zero, so almost sure hitting is established before the capped and
uncapped preterminal tests are identified.

Exhausting bounded lifetime intervals gives an equality of the full lifetime
measures: the positive-drift law is the stopped-likelihood tilt of the actual
zero-drift law. This is a measure identity, rather than a conditional density
assumption. The scalar zero-drift lifetime tail is also evaluated as the literal
half-normal integral.

Differentiating that integral and proving the multi-time lifetime-marked
ceiling-grid law are separate remaining steps in the first-hit reversal.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace DOZZ.Proofs

/-- Every actual deterministic Brownian terminal likelihood has integral one. -/
theorem brownian_lintegral_gaussianLikelihood_one (P : Measure BrownianPath)
    (hB : IsPreBrownianReal (fun t p => p t) P) (a : ℝ) (T : ℝ≥0) :
    (∫⁻ p, brownianGaussianLikelihood a T (p T) ∂P) = 1 := by
  have hi : Integrable (fun p => Real.exp (a*p T-a^2*(T : ℝ)/2)) P := by
    simpa only [Function.comp_def] using (hB.hasLaw_eval T).integrable_comp
      (integrable_real_brownianGaussianLikelihood a T)
  change (∫⁻ p, ENNReal.ofReal (Real.exp (a*p T-a^2*(T : ℝ)/2)) ∂P) = _
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun p => (Real.exp_pos _).le)),
    brownian_exponential_expectation_one hB T a,ENNReal.ofReal_one]

/-- Gaussian likelihood is jointly measurable in the elapsed time and the actual Brownian path. -/
theorem measurable_brownian_remainingLikelihood (a : ℝ) (T : ℝ≥0) :
    Measurable (fun z : ℝ≥0 × BrownianPath => brownianGaussianLikelihood a (T-z.1) (z.2 (T-z.1))) := by
  unfold brownianGaussianLikelihood
  apply Measurable.ennreal_ofReal
  apply Measurable.exp
  have hv : Measurable (fun z : ℝ≥0 × BrownianPath => z.2 (T-z.1)) :=
    measurable_brownianPath_evaluation.comp ((measurable_const.sub measurable_fst).prodMk measurable_snd)
  have ht : Measurable (fun z : ℝ≥0 × BrownianPath => ((T-z.1 : ℝ≥0) : ℝ)) := by fun_prop
  exact (measurable_const.mul hv).sub ((measurable_const.mul ht).div_const 2)

/-- A bounded stopped clock may select the remaining Gaussian likelihood without changing any nonnegative clock test. -/
theorem brownianPath_bounded_restart_remainingLikelihood (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (τ : BrownianPath → ℝ≥0)
    (hτ : IsStoppingTime (brownianRawFiltration (fun t (p : BrownianPath) => p t)
      (fun t => ContinuousMap.measurable_eval t)) (fun p => (τ p : WithTop ℝ≥0)))
    (T : ℝ≥0) (hτT : ∀ p, τ p ≤ T) (a : ℝ) (F : ℝ≥0 → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, F (τ p)*brownianGaussianLikelihood a (T-τ p) (brownianShiftPath (τ p) p (T-τ p)) ∂P) =
      ∫⁻ p, F (τ p) ∂P := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hmτ := measurable_finite_brownian_stoppingTime _ τ hτ
  have hmV : Measurable (fun p => brownianShiftPath (τ p) p) :=
    continuous_brownianShiftPath.measurable.comp (hmτ.prodMk measurable_id)
  let G : ℝ≥0 × BrownianPath → ℝ≥0∞ := fun z => F z.1*brownianGaussianLikelihood a (T-z.1) (z.2 (T-z.1))
  have hG : Measurable G := (hF.comp measurable_fst).mul (measurable_brownian_remainingLikelihood a T)
  have hj := brownianPath_bounded_restart_joint_map P hB τ hτ T hτT τ
    (measurable_finite_stoppingTime_stopped _ τ hτ)
  calc
    _ = ∫⁻ z, G z ∂P.map (fun p => (τ p,brownianShiftPath (τ p) p)) :=
      (lintegral_map hG (hmτ.prodMk hmV)).symm
    _ = ∫⁻ z, G z ∂(P.map τ).prod P := by rw [hj]
    _ = ∫⁻ t, ∫⁻ p, G (t,p) ∂P ∂P.map τ := lintegral_prod G hG.aemeasurable
    _ = ∫⁻ t, F t ∂P.map τ := by
      apply lintegral_congr
      intro t
      change (∫⁻ p, F t*brownianGaussianLikelihood a (T-t) (p (T-t)) ∂P) = F t
      rw [lintegral_const_mul (F t)
        (show Measurable (fun p : BrownianPath => brownianGaussianLikelihood a (T-t) (p (T-t))) from
          (measurable_brownianGaussianLikelihood a (T-t)).comp (ContinuousMap.measurable_eval (T-t))),
        brownian_lintegral_gaussianLikelihood_one P hB.toIsPreBrownianReal a (T-t),mul_one]
    _ = _ := lintegral_map hF hmτ
/-- Independent Gaussian durations factor the literal scalar terminal likelihood. -/
theorem brownianGaussianLikelihood_add (a : ℝ) (s d : ℝ≥0) (x y : ℝ) :
    brownianGaussianLikelihood a (s+d) (x+y) = brownianGaussianLikelihood a s x*brownianGaussianLikelihood a d y := by
  have he : a*(x+y)-a^2*((s : ℝ)+(d : ℝ))/2 = (a*x-a^2*(s : ℝ)/2)+(a*y-a^2*(d : ℝ)/2) := by ring_nf
  simp only [brownianGaussianLikelihood,NNReal.coe_add,he,Real.exp_add,
    ENNReal.ofReal_mul (Real.exp_pos _).le]

/-- On a preterminal hit, the terminal likelihood factors into the stopped hit likelihood and the remaining Gaussian likelihood. -/
theorem brownianPath_firstHit_likelihood_factor (a β : ℝ) (T : ℝ≥0) (p : BrownianPath)
    (hp0 : p 0 < β) (hh : cappedBrownianFirstPassage β T p < T) :
    brownianGaussianLikelihood a T (p T) =
      brownianGaussianLikelihood a (cappedBrownianFirstPassage β T p) β*
        brownianGaussianLikelihood a (T-cappedBrownianFirstPassage β T p)
          (brownianShiftPath (cappedBrownianFirstPassage β T p) p (T-cappedBrownianFirstPassage β T p)) := by
  let τ := cappedBrownianFirstPassage β T p
  have hτT := cappedBrownianFirstPassage_le β T p
  have hv : p τ = β := cappedBrownianFirstPassage_value β T p hp0 hh
  have he : β+brownianShiftPath τ p (T-τ) = p T := by
    change β+(p (τ+(T-τ))-p τ) = p T
    rw [add_tsub_cancel_of_le hτT,hv]
    ring_nf
  rw [← he,← brownianGaussianLikelihood_add,
    add_tsub_cancel_of_le hτT]

/-- First-hit conditioning retains exactly the stopped scalar likelihood on every preterminal lifetime test. -/
theorem brownianPath_firstHit_likelihood_lintegral (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a β : ℝ) (hβ : 0 < β) (T : ℝ≥0)
    (F : ℝ≥0 → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p in {p | cappedBrownianFirstPassage β T p < T},
      F (cappedBrownianFirstPassage β T p)*brownianGaussianLikelihood a T (p T) ∂P) =
      ∫⁻ p in {p | cappedBrownianFirstPassage β T p < T},
        F (cappedBrownianFirstPassage β T p)*brownianGaussianLikelihood a (cappedBrownianFirstPassage β T p) β ∂P := by
  classical
  let τ := cappedBrownianFirstPassage β T
  have hτ := cappedBrownianFirstPassage_isStoppingTime β T
  have hmτ := measurable_finite_brownian_stoppingTime _ τ hτ
  let H : Set BrownianPath := {p | τ p < T}
  have hH : MeasurableSet H := measurableSet_lt hmτ measurable_const
  let F' : ℝ≥0 → ℝ≥0∞ := (Iio T).indicator (fun t => F t*brownianGaussianLikelihood a t β)
  have hmL : Measurable (fun t : ℝ≥0 => brownianGaussianLikelihood a t β) := by
    unfold brownianGaussianLikelihood
    fun_prop
  have hF' : Measurable F' := (hF.mul hmL).indicator measurableSet_Iio
  have hi := brownianPath_bounded_restart_remainingLikelihood P hB τ hτ T
    (cappedBrownianFirstPassage_le β T) a F' hF'
  have hl : H.indicator (fun p => F (τ p)*brownianGaussianLikelihood a T (p T)) =ᵐ[P]
      (fun p => F' (τ p)*brownianGaussianLikelihood a (T-τ p) (brownianShiftPath (τ p) p (T-τ p))) := by
    filter_upwards [hB.eval_zero_ae_eq_zero] with p hp
    by_cases hh : τ p < T
    · have hf := brownianPath_firstHit_likelihood_factor a β T p (hp ▸ hβ) hh
      simp only [H,F',Set.indicator_apply,mem_ofPred_eq,mem_Iio,ite_eq_left hh]
      rw [hf,mul_assoc]
    · simp only [H,F',Set.indicator_apply,mem_ofPred_eq,mem_Iio,ite_eq_right hh,zero_mul]
  have hr : (fun p => F' (τ p)) = H.indicator (fun p => F (τ p)*brownianGaussianLikelihood a (τ p) β) := by
    funext p
    simp only [F',H,Set.indicator_apply,mem_Iio,mem_ofPred_eq]
  rw [← lintegral_indicator hH,← lintegral_indicator hH]
  exact (lintegral_congr_ae hl).trans (hi.trans (by rw [hr]))
/-- Capping a path at the same terminal horizon preserves the literal capped first-hit time. -/
theorem cappedBrownianFirstPassage_stop (β : ℝ) (T : ℝ≥0) (p : BrownianPath) :
    cappedBrownianFirstPassage β T (stopBrownianPath p T) = cappedBrownianFirstPassage β T p := by
  have he : {u : ℝ≥0 | u ≤ T ∧ β ≤ stopBrownianPath p T u} = {u : ℝ≥0 | u ≤ T ∧ β ≤ p u} := by
    ext u
    change (u ≤ T ∧ β ≤ p (min u T)) ↔ (u ≤ T ∧ β ≤ p u)
    by_cases hu : u ≤ T
    · rw [min_eq_left hu]
    · simp only [hu,false_and]
  simp only [cappedBrownianFirstPassage,he]

/-- Finite-horizon change of drift transports every preterminal capped first-hit lifetime test. -/
theorem brownianPath_drift_firstHit_likelihood_lintegral (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a β : ℝ) (hβ : 0 < β)
    (T : ℝ≥0) (F : ℝ≥0 → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p in {p | cappedBrownianFirstPassage β T (driftedBrownianPath a p) < T},
      F (cappedBrownianFirstPassage β T (driftedBrownianPath a p)) ∂P) =
      ∫⁻ p in {p | cappedBrownianFirstPassage β T p < T},
        F (cappedBrownianFirstPassage β T p)*brownianGaussianLikelihood a (cappedBrownianFirstPassage β T p) β ∂P := by
  classical
  let τ := cappedBrownianFirstPassage β T
  have hmτ := measurable_finite_brownian_stoppingTime _ τ (cappedBrownianFirstPassage_isStoppingTime β T)
  let H : Set BrownianPath := {p | τ p < T}
  have hH : MeasurableSet H := measurableSet_lt hmτ measurable_const
  let G : BrownianPath → ℝ≥0∞ := H.indicator (fun p => F (τ p))
  have hG : Measurable G := (hF.comp hmτ).indicator hH
  have he := brownianFiniteTilt_stoppedPath_lintegral_all P hB.toIsPreBrownianReal a T G hG
  have hl : (fun p => G (stopBrownianPath (driftedBrownianPath a p) T)) =
      ((fun p => τ (driftedBrownianPath a p)) ⁻¹' Iio T).indicator (fun p => F (τ (driftedBrownianPath a p))) := by
    funext p
    simp only [G,H,Set.indicator_apply,mem_ofPred_eq,mem_preimage,mem_Iio,
      cappedBrownianFirstPassage_stop,τ]
  have hr : (fun p => brownianGaussianLikelihood a T (p T)*G (stopBrownianPath p T)) =
      H.indicator (fun p => F (τ p)*brownianGaussianLikelihood a T (p T)) := by
    funext p
    by_cases hp : τ p < T
    · simp only [G,H,Set.indicator_apply,mem_ofPred_eq,cappedBrownianFirstPassage_stop,τ,ite_eq_left hp]
      exact mul_comm _ _
    · simp only [G,H,Set.indicator_apply,mem_ofPred_eq,cappedBrownianFirstPassage_stop,τ,ite_eq_right hp,mul_zero]
  have hmD : Measurable (fun p => τ (driftedBrownianPath a p)) := hmτ.comp
    (continuous_driftedBrownianPath.measurable.comp (measurable_const.prodMk measurable_id))
  have hHD : MeasurableSet ((fun p => τ (driftedBrownianPath a p)) ⁻¹' Iio T) := measurableSet_Iio.preimage hmD
  rw [hl,hr,lintegral_indicator hHD,lintegral_indicator hH] at he
  exact he.trans (brownianPath_firstHit_likelihood_lintegral P hB a β hβ T F hF)
/-- A zero-drift Brownian path reaches every positive fixed upper level almost surely. -/
theorem brownianPath_zeroDrift_hits_ae (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (β : ℝ) (hβ : 0 < β) :
    ∀ᵐ p ∂P, ∃ u : ℝ≥0, β ≤ p u := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  let E : Set BrownianPath := {p | ¬∃ u : ℝ≥0, β ≤ p u}
  have hle (n : ℕ) : P E ≤ ENNReal.ofReal (Real.sqrt (2/Real.pi)*β/((n : ℝ)+1)) := by
    let t : ℝ := ((n : ℝ)+1)^2
    have ht : 0 < t := by dsimp [t]; positivity
    have he := (brownian_zeroDrift_barrier_bound P (fun t p => p t) hB β t hβ ht).2
    have hsub : E ⊆ {p : BrownianPath | ∀ u : ℝ≥0, (u : ℝ) ≤ t → p u ≤ β} := by
      intro p hp u hu
      exact (not_le.mp (fun h => hp ⟨u,h⟩)).le
    have hs : Real.sqrt t = (n : ℝ)+1 := by
      dsimp [t]
      rw [Real.sqrt_sq_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)+1)]
    rw [hs] at he
    exact (measure_mono hsub).trans he
  have hh : Tendsto (fun n : ℕ => Real.sqrt (2/Real.pi)*β/((n : ℝ)+1)) atTop (𝓝 0) := by
    simpa only [mul_zero,mul_one_div] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul
      (Real.sqrt (2/Real.pi)*β)
  have hr : (P E).toReal ≤ 0 := ge_of_tendsto' hh (fun n =>
    ENNReal.toReal_le_of_le_ofReal (by positivity) (hle n))
  have hz : P E = 0 := ((ENNReal.toReal_eq_zero_iff (P E)).mp
    (le_antisymm hr ENNReal.toReal_nonneg)).resolve_right (measure_ne_top _ _)
  rw [ae_iff]
  exact hz

/-- The zero-drift first-passage lifetime is positive and reaches its level exactly. -/
theorem brownianPath_zeroDrift_firstHit_ae (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (β : ℝ) (hβ : 0 < β) :
    ∀ᵐ p ∂P, 0 < firstPassageTime p β ∧ p (firstPassageTime p β) = β := by
  filter_upwards [hB.eval_zero_ae_eq_zero,brownianPath_zeroDrift_hits_ae P hB β hβ] with p hp hh
  exact ⟨firstPassageTime_pos_of_hit p β (hp ▸ hβ) hh,firstPassageTime_value_of_hit p β (hp ▸ hβ) hh⟩
/-- For a path reaching the level, the uncapped and capped first-hit tests agree before the cap. -/
theorem firstPassageTime_capped_indicator (p : BrownianPath) (β : ℝ)
    (hh : ∃ u : ℝ≥0, β ≤ p u) (T : ℝ≥0) (F : ℝ≥0 → ℝ≥0∞) :
    (Iio T).indicator F (firstPassageTime p β) = (Iio T).indicator F (cappedBrownianFirstPassage β T p) := by
  classical
  let σ := firstPassageTime p β
  let τ := cappedBrownianFirstPassage β T p
  have ht : τ < T ↔ σ < T := by
    constructor
    · intro h
      have hm := cappedBrownianFirstPassage_mem β T p
      have hc : β ≤ p τ := by
        rcases hm with h | he
        · exact h.2
        · exact (h.ne he).elim
      have he := firstPassageTime_eq_capped_of_hit p β T ⟨τ,(cappedBrownianFirstPassage_le β T p),hc⟩
      simpa only [σ,τ,he] using h
    · intro h
      have he := firstPassageTime_eq_capped_of_hit p β T ⟨σ,h.le,firstPassageTime_mem p β hh⟩
      simpa only [σ,τ,← he] using h
  change (Iio T).indicator F σ = (Iio T).indicator F τ
  by_cases hs : σ < T
  · have hc := ht.mpr hs
    have he := firstPassageTime_eq_capped_of_hit p β T ⟨σ,hs.le,firstPassageTime_mem p β hh⟩
    simp only [Set.indicator_apply,mem_Iio,ite_eq_left hs,ite_eq_left hc]
    exact congrArg F he
  · have hc : ¬τ < T := fun h => hs (ht.mp h)
    simp only [Set.indicator_apply,mem_Iio,ite_eq_right hs,ite_eq_right hc]

/-- Positive and zero drift have the exact stopped-likelihood relation on every bounded lifetime interval. -/
theorem brownianPath_firstHit_lifetime_tilt_preterminal (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β)
    (T : ℝ≥0) (F : ℝ≥0 → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p, (Iio T).indicator F (firstPassageTime (driftedBrownianPath a p) β) ∂P) =
      ∫⁻ p, (Iio T).indicator (fun t => F t*brownianGaussianLikelihood a t β) (firstPassageTime p β) ∂P := by
  classical
  have hmτ := measurable_finite_brownian_stoppingTime _ _ (cappedBrownianFirstPassage_isStoppingTime β T)
  have hmD : Measurable (fun p => cappedBrownianFirstPassage β T (driftedBrownianPath a p)) := hmτ.comp
    (continuous_driftedBrownianPath.measurable.comp (measurable_const.prodMk measurable_id))
  have he := brownianPath_drift_firstHit_likelihood_lintegral P hB a β hβ T F hF
  have hl : (fun p => (Iio T).indicator F (firstPassageTime (driftedBrownianPath a p) β)) =ᵐ[P]
      (fun p => (Iio T).indicator F (cappedBrownianFirstPassage β T (driftedBrownianPath a p))) := by
    filter_upwards [brownianPath_positiveDrift_hits_ae P hB a β ha] with p hp
    exact firstPassageTime_capped_indicator _ β hp T F
  have hr : (fun p => (Iio T).indicator (fun t => F t*brownianGaussianLikelihood a t β) (firstPassageTime p β)) =ᵐ[P]
      (fun p => (Iio T).indicator (fun t => F t*brownianGaussianLikelihood a t β) (cappedBrownianFirstPassage β T p)) := by
    filter_upwards [brownianPath_zeroDrift_hits_ae P hB β hβ] with p hp
    exact firstPassageTime_capped_indicator _ β hp T _
  rw [lintegral_congr_ae hl,lintegral_congr_ae hr]
  have hL : (fun p => (Iio T).indicator F (cappedBrownianFirstPassage β T (driftedBrownianPath a p))) =
      {p : BrownianPath | cappedBrownianFirstPassage β T (driftedBrownianPath a p) < T}.indicator
        (fun p => F (cappedBrownianFirstPassage β T (driftedBrownianPath a p))) := by
    funext p
    simp only [Set.indicator_apply,mem_Iio,mem_ofPred_eq]
  have hR : (fun p => (Iio T).indicator (fun t => F t*brownianGaussianLikelihood a t β) (cappedBrownianFirstPassage β T p)) =
      {p : BrownianPath | cappedBrownianFirstPassage β T p < T}.indicator
        (fun p => F (cappedBrownianFirstPassage β T p)*brownianGaussianLikelihood a (cappedBrownianFirstPassage β T p) β) := by
    funext p
    simp only [Set.indicator_apply,mem_Iio,mem_ofPred_eq]
  rw [hL,hR,lintegral_indicator (measurableSet_lt hmD measurable_const),
    lintegral_indicator (measurableSet_lt hmτ measurable_const)]
  exact he
/-- The full positive-drift first-hit lifetime law is the stopped-likelihood tilt of the zero-drift lifetime law. -/
theorem brownianPath_firstHit_lifetime_map_tilt (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) :
    P.map (fun p => firstPassageTime (driftedBrownianPath a p) β) =
      (P.map (fun p => firstPassageTime p β)).withDensity (fun t => brownianGaussianLikelihood a t β) := by
  classical
  let σ := fun p : BrownianPath => firstPassageTime (driftedBrownianPath a p) β
  let τ := fun p : BrownianPath => firstPassageTime p β
  have hmσ : Measurable σ := (measurable_firstPassageTime β).comp
    (continuous_driftedBrownianPath.measurable.comp (measurable_const.prodMk measurable_id))
  have hmτ : Measurable τ := measurable_firstPassageTime β
  have hmW : Measurable (fun t : ℝ≥0 => brownianGaussianLikelihood a t β) := by
    unfold brownianGaussianLikelihood
    fun_prop
  apply Measure.ext
  intro S hS
  have he (T : ℝ≥0) : P.map σ (S ∩ Iio T) =
      ((P.map τ).withDensity (fun t => brownianGaussianLikelihood a t β)) (S ∩ Iio T) := by
    let F : ℝ≥0 → ℝ≥0∞ := S.indicator (fun _ => 1)
    have hF : Measurable F := measurable_const.indicator hS
    have h1 : Measurable ((Iio T).indicator F) := hF.indicator measurableSet_Iio
    have h2 : Measurable ((Iio T).indicator (fun t => F t*brownianGaussianLikelihood a t β)) :=
      (hF.mul hmW).indicator measurableSet_Iio
    have ht := brownianPath_firstHit_lifetime_tilt_preterminal P hB a β ha hβ T F hF
    have hleft : (Iio T).indicator F = (S ∩ Iio T).indicator (fun _ => 1) := by
      funext t
      by_cases hst : t ∈ S <;> by_cases htt : t < T <;>
        simp only [F,Set.indicator_apply,mem_Iio,mem_inter_iff,hst,htt,ite_true,ite_false,and_true,and_false]
    have hright : (Iio T).indicator (fun t => F t*brownianGaussianLikelihood a t β) =
        (S ∩ Iio T).indicator (fun t => brownianGaussianLikelihood a t β) := by
      funext t
      by_cases hst : t ∈ S <;> by_cases htt : t < T <;>
        simp only [F,Set.indicator_apply,mem_Iio,mem_inter_iff,hst,htt,ite_true,ite_false,
          and_true,and_false,one_mul,zero_mul]
    have ht' : (∫⁻ t, (Iio T).indicator F t ∂P.map σ) =
        ∫⁻ t, (Iio T).indicator (fun t => F t*brownianGaussianLikelihood a t β) t ∂P.map τ := by
      rw [lintegral_map h1 hmσ,lintegral_map h2 hmτ]
      exact ht
    rw [hleft,hright,lintegral_indicator (hS.inter measurableSet_Iio),
      lintegral_indicator (hS.inter measurableSet_Iio),lintegral_one,← withDensity_apply _ (hS.inter measurableSet_Iio)] at ht'
    simpa only [Measure.restrict_apply MeasurableSet.univ,univ_inter] using ht'
  have hmono : Monotone (fun n : ℕ => S ∩ Iio ((n : ℝ≥0)+1)) := by
    intro n m hnm
    have hnm' : (n : ℝ≥0)+1 ≤ (m : ℝ≥0)+1 := by exact_mod_cast Nat.add_le_add_right hnm 1
    exact inter_subset_inter_right S (Iio_subset_Iio hnm')
  have hu : (⋃ n : ℕ, S ∩ Iio ((n : ℝ≥0)+1)) = S := by
    ext t
    simp only [mem_iUnion,mem_inter_iff,mem_Iio]
    constructor
    · rintro ⟨n,ht,_⟩
      exact ht
    · intro ht
      obtain ⟨n,hn⟩ := exists_nat_gt (t : ℝ)
      have hn' : t < (n : ℝ≥0) := by exact_mod_cast hn
      exact ⟨n,ht,hn'.trans (lt_add_one _)⟩
  rw [← hu,hmono.measure_iUnion,hmono.measure_iUnion]
  congr 1
  funext n
  exact he ((n : ℝ≥0)+1)
/-- The zero-drift first-hit lifetime tail equals the closed finite-horizon barrier probability. -/
theorem brownianPath_zeroDrift_firstHit_tail_eq_barrier (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (β : ℝ) (hβ : 0 < β)
    (T : ℝ≥0) (hT : T ≠ 0) :
    P {p | T < firstPassageTime p β} = P {p : BrownianPath | ∀ u : ℝ≥0, u ≤ T → p u ≤ β} := by
  have hn : ∀ᵐ p ∂P, (⨆ u : Iic T, p u) ≠ β := by
    rw [ae_iff]
    simpa only [not_not] using brownianPath_runningMaximum_atom_zero P hB β hβ T hT
  apply measure_congr
  filter_upwards [brownianPath_zeroDrift_hits_ae P hB β hβ,hn] with p hp hn
  apply propext
  rw [← not_le,firstPassageTime_le_iff]
  have hfalse : (¬∃ u : ℝ≥0, β ≤ p u) = False := propext (iff_false_intro (not_not_intro hp))
  rw [hfalse,false_or]
  constructor
  · intro h u hu
    by_contra hb
    exact h ⟨u,hu,(lt_of_not_ge hb).le⟩
  · intro h hh
    obtain ⟨u,hu,hβu⟩ := hh
    have hm : (⨆ u : Iic T, p u) ≤ β := (brownianPath_barrier_iff_runningMaximum p T β).mp h
    have hl := hβu.trans (le_ciSup (brownianPath_Iic_bddAbove p T) ⟨u,hu⟩)
    exact hn (le_antisymm hm hl)

/-- The exact Gaussian interval expression for the actual zero-drift first-hit lifetime tail. -/
theorem brownianPath_zeroDrift_firstHit_tail_gaussian (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (β : ℝ) (hβ : 0 < β)
    (T : ℝ≥0) (hT : T ≠ 0) :
    P {p | T < firstPassageTime p β} = gaussianReal 0 T (Icc (-β) β) := by
  rw [brownianPath_zeroDrift_firstHit_tail_eq_barrier P hB β hβ T hT,
    brownianPath_barrier_probability_interval P hB β hβ T hT]
  exact (hB.hasLaw_eval T).measure_eq measurableSet_Icc

/-- The first-hit lifetime tail is the literal half-normal integral to be differentiated in the density calculation. -/
theorem brownianPath_zeroDrift_firstHit_tail_integral (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (β : ℝ) (hβ : 0 < β)
    (T : ℝ≥0) (hT : T ≠ 0) :
    P {p | T < firstPassageTime p β} = ENNReal.ofReal (Real.sqrt (2/Real.pi)*
      ∫ x in Icc (0 : ℝ) (β/Real.sqrt (T : ℝ)), Real.exp (-x^2/2)) := by
  rw [brownianPath_zeroDrift_firstHit_tail_gaussian P hB β hβ T hT]
  exact gaussianReal_barrier_integral T hT β hβ.le

end DOZZ.Proofs

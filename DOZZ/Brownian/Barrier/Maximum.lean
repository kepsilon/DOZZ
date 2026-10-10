/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Brownian.Barrier.PositiveDrift

/-!
# Drifted maxima and positive first-hit lifetimes

The finite-horizon killed endpoint formula gives an exact signed difference
of drifted Gaussian endpoint probabilities. Its reflected term has coefficient
`exp (2 * a * β)` and the opposite terminal drift.

For negative drift this term supplies the matching lower bound for the maximum.
The omitted Gaussian term is bounded by one; the remaining terminal lower tail
has an explicit Gaussian exponential bound. Letting integer horizons tend to
infinity recovers the sharp exponential maximum tail.

At level zero, positive levels decreasing to zero give probability one. Transport
through the actual continuous-path Brownian law yields the statement
`DOZZ.negativeDriftBrownian_maximum_tail` on an arbitrary sample space, without
an extra measurability premise.

Positive drift reaches every fixed real upper level almost surely: the no-hit
event is contained in every terminal lower tail, whose probability tends to zero.
A nonempty hitting set and continuity give no overshoot and positive lifetime
when the initial value is strictly below the level.

Finite-horizon drifted maximum atoms vanish by Gaussian tilting and absolute
continuity. Thus the literal first-hit lifetime tail agrees with the closed
barrier event, and inherits its exact Gaussian endpoint expression.

These lifetime assertions use the first-passage convention directly. They never
infer a hit from the infimum of an empty hitting set. The almost sure hitting
assertion removes that exceptional convention before the finite sublevel
equivalence is used.

The reversed marked-path law and Williams decomposition are separate results.
This module supplies their actual hitting and lifetime inputs; it makes no Markov
assertion at a last-exit time.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace DOZZ.Proofs

/-- A scalar terminal likelihood converts Gaussian set integrals to drifted Gaussian mass. -/
theorem gaussianReal_likelihood_setIntegral (a : ℝ) (T : ℝ≥0) (hT : T ≠ 0)
    (S : Set ℝ) (hS : MeasurableSet S) :
    (∫ x in S, Real.exp (a*x-a^2*(T : ℝ)/2) ∂gaussianReal 0 T) =
      (gaussianReal (a*(T : ℝ)) T).real S := by
  have he : gaussianReal (a*(T : ℝ)) T S =
      ENNReal.ofReal (∫ x in S, Real.exp (a*x-a^2*(T : ℝ)/2) ∂gaussianReal 0 T) := by
    rw [← gaussianReal_withDensity_brownianGaussianLikelihood a T hT,
      withDensity_apply _ hS]
    change (∫⁻ x in S, ENNReal.ofReal (Real.exp (a*x-a^2*(T : ℝ)/2)) ∂gaussianReal 0 T) = _
    exact (ofReal_integral_eq_lintegral_ofReal
      (integrable_real_brownianGaussianLikelihood a T).integrableOn
      (ae_of_all _ (fun x => (Real.exp_pos _).le))).symm
  rw [Measure.real,he,ENNReal.toReal_ofReal (integral_nonneg (fun x => (Real.exp_pos _).le))]

/-- A reflected endpoint likelihood carries the exponential height factor and the opposite drift. -/
theorem gaussianReal_reflected_likelihood_setIntegral (a β : ℝ) (T : ℝ≥0) (hT : T ≠ 0)
    (S : Set ℝ) (hS : MeasurableSet S) :
    (∫ x in S, Real.exp (a*(2*β-x)-a^2*(T : ℝ)/2) ∂gaussianReal 0 T) =
      Real.exp (2*a*β)*(gaussianReal ((-a)*(T : ℝ)) T).real S := by
  have he : (fun x : ℝ => Real.exp (a*(2*β-x)-a^2*(T : ℝ)/2)) =
      fun x => Real.exp (2*a*β)*Real.exp ((-a)*x-(-a)^2*(T : ℝ)/2) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    ring_nf
  rw [he,integral_const_mul,gaussianReal_likelihood_setIntegral (-a) T hT S hS]

/-- The exact signed Gaussian endpoint difference for survival is nonnegative. -/
theorem brownianPath_drift_barrier_endpoint_difference_nonneg (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a β : ℝ) (hβ : 0 < β)
    (T : ℝ≥0) (hT : T ≠ 0) :
    0 ≤ (gaussianReal (a*(T : ℝ)) T).real (Iio β) -
      Real.exp (2*a*β)*(gaussianReal ((-a)*(T : ℝ)) T).real (Ioi β) := by
  let F : ℝ → ℝ := fun x => Real.exp (a*x-a^2*(T : ℝ)/2)
  have hmF : Measurable F := by dsimp [F]; fun_prop
  have hi : Integrable (fun p => F (p T)) P := by
    simpa only [Function.comp_def] using (hB.hasLaw_eval T).integrable_comp
      (integrable_real_brownianGaussianLikelihood a T)
  have hn : 0 ≤ ∫ p in {p : BrownianPath | ∀ u : ℝ≥0, u ≤ T → p u ≤ β}, F (p T) ∂P :=
    integral_nonneg (fun p => (Real.exp_pos _).le)
  rw [brownianPath_barrier_endpoint_integral P hB β hβ T hT F hmF hi] at hn
  change 0 ≤ (∫ p in {p | p T ∈ Iio β}, F (p T) ∂P) -
    (∫ p in {p | p T ∈ Ioi β}, F (2*β-p T) ∂P) at hn
  rw [brownianPath_endpoint_setIntegral P hB.toIsPreBrownianReal T (Iio β) measurableSet_Iio F hmF,
    brownianPath_endpoint_setIntegral P hB.toIsPreBrownianReal T (Ioi β) measurableSet_Ioi
      (fun x => F (2*β-x)) (hmF.comp (measurable_const.sub measurable_id))] at hn
  simpa only [F,gaussianReal_likelihood_setIntegral a T hT (Iio β) measurableSet_Iio,
    gaussianReal_reflected_likelihood_setIntegral a β T hT (Ioi β) measurableSet_Ioi] using hn

/-- The exact real probability of a finite-horizon drifted maximum exceeding a positive level. -/
theorem brownianPath_drift_finiteMaximum_real (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a β : ℝ) (hβ : 0 < β)
    (T : ℝ≥0) (hT : T ≠ 0) :
    P.real {p | ∃ u ≤ T, β < p u+a*(u : ℝ)} =
      1-(gaussianReal (a*(T : ℝ)) T).real (Iio β) +
        Real.exp (2*a*β)*(gaussianReal ((-a)*(T : ℝ)) T).real (Ioi β) := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  let A : Set BrownianPath := {p | ∀ u : ℝ≥0, u ≤ T → p u+a*(u : ℝ) ≤ β}
  have hmDrift : Measurable (brownianDriftPath a) :=
    continuous_brownianDriftPath.measurable.comp (measurable_const.prodMk measurable_id)
  have hA : MeasurableSet A := ((brownianRawFiltration _ (fun t => ContinuousMap.measurable_eval t)).le T _
    (measurableSet_brownianPath_barrier T β)).preimage hmDrift
  have hc : {p : BrownianPath | ∃ u ≤ T, β < p u+a*(u : ℝ)} = Aᶜ := by
    ext p
    simp only [A,mem_compl_iff,mem_ofPred_eq,not_forall,not_le,exists_prop]
  rw [hc,measureReal_compl hA,probReal_univ]
  have he := brownianPath_drift_barrier_endpoint_integral P hB a β hβ T hT
  rw [gaussianReal_likelihood_setIntegral a T hT (Iio β) measurableSet_Iio,
    gaussianReal_reflected_likelihood_setIntegral a β T hT (Ioi β) measurableSet_Ioi] at he
  have hr : P.real A = (gaussianReal (a*(T : ℝ)) T).real (Iio β) -
      Real.exp (2*a*β)*(gaussianReal ((-a)*(T : ℝ)) T).real (Ioi β) := by
    rw [Measure.real,show P A = _ from he,ENNReal.toReal_ofReal
      (brownianPath_drift_barrier_endpoint_difference_nonneg P hB a β hβ T hT)]
  rw [hr]
  ring_nf
/-- The positive-drift Gaussian terminal lower tail has an explicit exponentially decaying bound. -/
theorem brownian_gaussian_positiveDrift_lowerTail_le (P : Measure BrownianPath)
    (hB : IsPreBrownianReal (fun t p => p t) P) (ν β : ℝ) (hν : 0 ≤ ν) (T : ℝ≥0) :
    gaussianReal (ν*(T : ℝ)) T (Iic β) ≤ ENNReal.ofReal (Real.exp (ν*β-ν^2*(T : ℝ)/2)) := by
  have hl := gaussianReal_add_const (hB.hasLaw_eval T) (ν*(T : ℝ))
  have he : gaussianReal (ν*(T : ℝ)) T (Iic β) = P {p : BrownianPath | p T+ν*(T : ℝ) ≤ β} := by
    have hl' : P.map (fun p : BrownianPath => p T+ν*(T : ℝ)) = gaussianReal (ν*(T : ℝ)) T := by
      simpa only [zero_add] using hl.map_eq
    rw [← hl',Measure.map_apply
      (show Measurable (fun p : BrownianPath => p T+ν*(T : ℝ)) from
        (ContinuousMap.measurable_eval T).add measurable_const) measurableSet_Iic]
    rfl
  rw [he]
  have hb := brownian_terminal_event_bound hB T ν (ν*β-ν^2*(T : ℝ))
    {p : BrownianPath | p T+ν*(T : ℝ) ≤ β} (fun p hp => by
      have hm := mul_le_mul_of_nonneg_left hp hν
      nlinarith [hm])
  convert hb using 1
  congr 2
  ring_nf

/-- The reflected Gaussian term gives a quantitative matching lower bound for finite maxima. -/
theorem brownianPath_negativeDrift_finiteMaximum_real_ge (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν β : ℝ) (hν : 0 ≤ ν) (hβ : 0 < β)
    (T : ℝ≥0) (hT : T ≠ 0) :
    Real.exp (-2*ν*β)*(1-Real.exp (ν*β-ν^2*(T : ℝ)/2)) ≤
      P.real {p | ∃ u ≤ T, β < p u-ν*(u : ℝ)} := by
  have he := brownianPath_drift_finiteMaximum_real P hB (-ν) β hβ T hT
  simp only [neg_mul,← sub_eq_add_neg,neg_neg] at he
  rw [he]
  have hCDF := ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le
    (brownian_gaussian_positiveDrift_lowerTail_le P hB.toIsPreBrownianReal ν β hν T)
  have hc : (gaussianReal (ν*(T : ℝ)) T).real (Ioi β) =
      1-(gaussianReal (ν*(T : ℝ)) T).real (Iic β) := by
    simpa only [compl_Iic] using
      (probReal_compl_eq_one_sub (μ := gaussianReal (ν*(T : ℝ)) T) measurableSet_Iic)
  rw [hc]
  have hi : (gaussianReal (-(ν*(T : ℝ))) T).real (Iio β) ≤ 1 := measureReal_le_one
  have hexp : 2*(-ν)*β = -2*ν*β := by ring_nf
  rw [hexp]
  change (gaussianReal (ν*(T : ℝ)) T).real (Iic β) ≤ Real.exp (ν*β-ν^2*(T : ℝ)/2) at hCDF
  have hm := mul_le_mul_of_nonneg_left hCDF (Real.exp_pos (-2*ν*β)).le
  nlinarith [hm]
/-- The Gaussian error in the reflected finite-horizon lower bound vanishes at integer horizons. -/
theorem tendsto_brownian_negativeDrift_tail_error (ν β : ℝ) (hν : 0 < ν) :
    Tendsto (fun n : ℕ => Real.exp (ν*β-ν^2*((n : ℝ)+1)/2)) atTop (𝓝 0) := by
  have hp : 0 < ν^2/2 := by positivity
  have hh : Tendsto (fun n : ℕ => Real.exp (-((ν^2/2)*(n : ℝ)))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Tendsto.const_mul_atTop hp tendsto_natCast_atTop_atTop)
  have he : (fun n : ℕ => Real.exp (ν*β-ν^2*((n : ℝ)+1)/2)) =
      fun n : ℕ => Real.exp (ν*β-ν^2/2)*Real.exp (-((ν^2/2)*(n : ℝ))) := by
    funext n
    rw [← Real.exp_add]
    congr 1
    ring_nf
  rw [he]
  simpa only [mul_zero] using hh.const_mul (Real.exp (ν*β-ν^2/2))

/-- The all-time negative-drift maximum has the sharp exponential tail at positive levels. -/
theorem brownianPath_negativeDrift_maximum_tail_pos (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν x : ℝ) (hν : 0 < ν) (hx : 0 < x) :
    P {p | ∃ t : ℝ≥0, x < p t-ν*(t : ℝ)} = ENNReal.ofReal (Real.exp (-2*ν*x)) := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  apply le_antisymm (brownianPath_negativeDrift_maximum_le P hB ν x hx)
  rw [ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
  have hh : Tendsto (fun n : ℕ => Real.exp (-2*ν*x)*(1-Real.exp (ν*x-ν^2*((n : ℝ)+1)/2)))
      atTop (𝓝 (Real.exp (-2*ν*x))) := by
    simpa only [sub_zero,mul_one] using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_brownian_negativeDrift_tail_error ν x hν)).const_mul
        (Real.exp (-2*ν*x))
  apply le_of_tendsto' hh
  intro n
  let T : ℝ≥0 := (n : ℝ≥0)+1
  have hT : T ≠ 0 := by dsimp [T]; positivity
  have hfinite := brownianPath_negativeDrift_finiteMaximum_real_ge P hB ν x hν.le hx T hT
  have hsub : {p : BrownianPath | ∃ u ≤ T, x < p u-ν*(u : ℝ)} ⊆ {p | ∃ u : ℝ≥0, x < p u-ν*(u : ℝ)} := by
    rintro p ⟨u,_,hu⟩
    exact ⟨u,hu⟩
  have hf : Real.exp (-2*ν*x)*(1-Real.exp (ν*x-ν^2*((n : ℝ)+1)/2)) ≤
      P.real {p : BrownianPath | ∃ u ≤ T, x < p u-ν*(u : ℝ)} := by
    simpa only [T,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one] using hfinite
  exact hf.trans (measureReal_mono hsub (measure_ne_top _ _))

/-- The all-time maximum is strictly positive almost surely, even with a negative drift. -/
theorem brownianPath_negativeDrift_maximum_tail_zero (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν : ℝ) (hν : 0 < ν) :
    P {p | ∃ t : ℝ≥0, 0 < p t-ν*(t : ℝ)} = 1 := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  apply le_antisymm prob_le_one
  rw [← ENNReal.ofReal_one,ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)]
  have hh : Tendsto (fun n : ℕ => Real.exp (-2*ν*(1/((n : ℝ)+1)))) atTop (𝓝 1) := by
    have hz : Tendsto (fun n : ℕ => -2*ν*(1/((n : ℝ)+1))) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (-2*ν)
    simpa only [Real.exp_zero,Function.comp_def] using (Real.continuous_exp.tendsto 0).comp hz
  apply le_of_tendsto' hh
  intro n
  have hx : 0 < 1/((n : ℝ)+1) := by positivity
  have he := brownianPath_negativeDrift_maximum_tail_pos P hB ν _ hν hx
  have hm : P.real {p | ∃ t : ℝ≥0, 1/((n : ℝ)+1) < p t-ν*(t : ℝ)} =
      Real.exp (-2*ν*(1/((n : ℝ)+1))) := by
    rw [Measure.real,he,ENNReal.toReal_ofReal (Real.exp_pos _).le]
  rw [← hm]
  apply measureReal_mono (μ := P) _ (measure_ne_top _ _)
  rintro p ⟨t,ht⟩
  exact ⟨t,hx.trans ht⟩

/-- The exact negative-drift maximum tail on the actual canonical continuous-path carrier. -/
theorem brownianPath_negativeDrift_maximum_tail (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν x : ℝ) (hν : 0 < ν) (hx : 0 ≤ x) :
    P {p | ∃ t : ℝ≥0, x < p t-ν*(t : ℝ)} = ENNReal.ofReal (Real.exp (-2*ν*x)) := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h,brownianPath_negativeDrift_maximum_tail_zero P hB ν hν]
    simp only [mul_zero,Real.exp_zero,ENNReal.ofReal_one]
  · exact brownianPath_negativeDrift_maximum_tail_pos P hB ν x hν h

/-- Proof of `DOZZ.negativeDriftBrownian_maximum_tail`. -/
theorem negativeDriftBrownian_maximum_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (hB : ProbabilityTheory.IsBrownianReal B P) (ν x : ℝ)
    (hν : 0 < ν) (hx : 0 ≤ x) :
    P {ω | ∃ t : ℝ≥0, x < B t ω - ν * t} = ENNReal.ofReal (Real.exp (-2 * ν * x)) := by
  let X := brownianContinuousPath B
  have hm : AEMeasurable X P := aemeasurable_brownianContinuousPath hB
  have hS : MeasurableSet {p : BrownianPath | ∃ t : ℝ≥0, x < p t-ν*(t : ℝ)} := by
    simpa only [sub_eq_add_neg,neg_mul] using measurableSet_brownianPath_drift_crossing (-ν) x
  have he : P {ω | ∃ t : ℝ≥0, x < B t ω-ν*(t : ℝ)} =
      (P.map X) {p : BrownianPath | ∃ t : ℝ≥0, x < p t-ν*(t : ℝ)} := by
    rw [Measure.map_apply_of_aemeasurable hm hS]
    apply measure_congr
    filter_upwards [brownianContinuousPath_eval_ae hB] with ω hω
    apply propext
    simp only [mem_preimage,mem_ofPred_eq,X,hω]
  rw [he]
  exact brownianPath_negativeDrift_maximum_tail _ (brownianContinuousPath_isBrownian hB) ν x hν hx
/-- A positive-drift Brownian path reaches every fixed real upper level almost surely. -/
theorem brownianPath_positiveDrift_hits_ae (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν c : ℝ) (hν : 0 < ν) :
    ∀ᵐ p ∂P, ∃ u : ℝ≥0, c ≤ driftedBrownianPath ν p u := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  let E : Set BrownianPath := {p | ¬∃ u : ℝ≥0, c ≤ driftedBrownianPath ν p u}
  have hle (n : ℕ) : P E ≤ ENNReal.ofReal (Real.exp (ν*c-ν^2*((n : ℝ)+1)/2)) := by
    let T : ℝ≥0 := (n : ℝ≥0)+1
    have hl := brownian_gaussian_positiveDrift_lowerTail_le P hB.toIsPreBrownianReal ν c hν.le T
    have hsub : E ⊆ {p : BrownianPath | p T+ν*(T : ℝ) ≤ c} := by
      intro p hp
      change ¬∃ u : ℝ≥0, c ≤ p u+ν*(u : ℝ) at hp
      exact (not_le.mp (fun h => hp ⟨T,h⟩)).le
    have hlaw := gaussianReal_add_const (hB.hasLaw_eval T) (ν*(T : ℝ))
    have he : gaussianReal (ν*(T : ℝ)) T (Iic c) = P {p : BrownianPath | p T+ν*(T : ℝ) ≤ c} := by
      have hmap : P.map (fun p : BrownianPath => p T+ν*(T : ℝ)) = gaussianReal (ν*(T : ℝ)) T := by
        simpa only [zero_add] using hlaw.map_eq
      rw [← hmap,Measure.map_apply
        (show Measurable (fun p : BrownianPath => p T+ν*(T : ℝ)) from
          (ContinuousMap.measurable_eval T).add measurable_const) measurableSet_Iic]
      rfl
    rw [he] at hl
    simpa only [T,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one] using (measure_mono hsub).trans hl
  have hr : (P E).toReal ≤ 0 := ge_of_tendsto' (tendsto_brownian_negativeDrift_tail_error ν c hν)
    (fun n => ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le (hle n))
  have hz : P E = 0 := by
    exact ((ENNReal.toReal_eq_zero_iff (P E)).mp (le_antisymm hr ENNReal.toReal_nonneg)).resolve_right
      (measure_ne_top _ _)
  rw [ae_iff]
  exact hz

/-- For a continuous path which starts below a level, a nonempty hitting set has no overshoot. -/
theorem firstPassageTime_value_of_hit (p : BrownianPath) (c : ℝ) (hp0 : p 0 < c)
    (hh : ∃ u : ℝ≥0, c ≤ p u) : p (firstPassageTime p c) = c := by
  obtain ⟨u,hcu⟩ := hh
  let T : ℝ≥0 := u+1
  have huT : u < T := by dsimp [T]; exact lt_add_one u
  have ht : firstPassageTime p c ≤ u := csInf_le (s := {u : ℝ≥0 | c ≤ p u}) (OrderBot.bddBelow _) hcu
  have he := firstPassageTime_eq_capped_of_hit p c T ⟨u,huT.le,hcu⟩
  rw [he] at ht ⊢
  exact cappedBrownianFirstPassage_value c T p hp0 (ht.trans_lt huT)

/-- The literal first-hit lifetime is positive whenever the path starts strictly below the level. -/
theorem firstPassageTime_pos_of_hit (p : BrownianPath) (c : ℝ) (hp0 : p 0 < c)
    (hh : ∃ u : ℝ≥0, c ≤ p u) : 0 < firstPassageTime p c := by
  apply pos_iff_ne_zero.mpr
  intro he
  have hv := firstPassageTime_value_of_hit p c hp0 hh
  rw [he] at hv
  exact hp0.ne hv

/-- Positive-drift first hits have positive lifetime and hit their level exactly, almost surely. -/
theorem brownianPath_positiveDrift_firstHit_ae (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν c : ℝ) (hν : 0 < ν) (hc : 0 < c) :
    ∀ᵐ p ∂P, 0 < firstPassageTime (driftedBrownianPath ν p) c ∧
      driftedBrownianPath ν p (firstPassageTime (driftedBrownianPath ν p) c) = c := by
  filter_upwards [hB.eval_zero_ae_eq_zero,brownianPath_positiveDrift_hits_ae P hB ν c hν] with p hp hh
  have hp0 : driftedBrownianPath ν p 0 < c := by
    change p 0+ν*(0 : ℝ≥0) < c
    simpa only [NNReal.coe_zero,mul_zero,add_zero,hp] using hc
  exact ⟨firstPassageTime_pos_of_hit _ c hp0 hh,firstPassageTime_value_of_hit _ c hp0 hh⟩
/-- Stopping at the terminal horizon preserves the entire compact running maximum. -/
theorem brownianPath_runningMaximum_stop (p : BrownianPath) (T : ℝ≥0) :
    (⨆ u : Iic T, stopBrownianPath p T u) = ⨆ u : Iic T, p u := by
  congr 1
  funext u
  change p (min u.1 T) = p u.1
  rw [min_eq_left (α := ℝ≥0) u.2]

/-- Every finite-horizon drifted running maximum has no atom at a positive level. -/
theorem brownianPath_drift_runningMaximum_atom_zero (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a β : ℝ) (hβ : 0 < β)
    (T : ℝ≥0) (hT : T ≠ 0) :
    P {p | (⨆ u : Iic T, driftedBrownianPath a p u) = β} = 0 := by
  let E : Set BrownianPath := {p | (⨆ u : Iic T, p u) = β}
  have hmM : Measurable (fun p : BrownianPath => ⨆ u : Iic T, p u) :=
    (measurable_brownianPath_runningMaximum T).mono
      ((brownianRawFiltration _ (fun t => ContinuousMap.measurable_eval t)).le T) le_rfl
  have hE : MeasurableSet E := measurableSet_eq_fun hmM measurable_const
  have hmStop := measurable_stopBrownianPath_fixed T
  have hmDrift : Measurable (driftedBrownianPath a) :=
    continuous_driftedBrownianPath.measurable.comp (measurable_const.prodMk measurable_id)
  have he : P {p | (⨆ u : Iic T, driftedBrownianPath a p u) = β} = brownianFiniteTilt P a T E := by
    calc
      _ = (P.map (fun p => stopBrownianPath (driftedBrownianPath a p) T)) E := by
        rw [Measure.map_apply (show Measurable (fun p => stopBrownianPath (driftedBrownianPath a p) T) from hmStop.comp hmDrift) hE]
        congr 1
        ext p
        simp only [E,mem_preimage,mem_ofPred_eq,brownianPath_runningMaximum_stop]
      _ = ((brownianFiniteTilt P a T).map (fun p => stopBrownianPath p T)) E := by
        rw [brownianFiniteTilt_stoppedPath_map P hB.toIsPreBrownianReal a T hT]
      _ = brownianFiniteTilt P a T E := by
        rw [Measure.map_apply hmStop hE]
        congr 1
        ext p
        simp only [E,mem_preimage,mem_ofPred_eq,brownianPath_runningMaximum_stop]
  rw [he]
  exact brownianFiniteTilt_absolutelyContinuous P a T (brownianPath_runningMaximum_atom_zero P hB β hβ T hT)

/-- The positive-drift lifetime tail equals the literal finite-horizon survival event. -/
theorem brownianPath_positiveDrift_firstHit_tail_eq_barrier (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν c : ℝ) (hν : 0 < ν) (hc : 0 < c)
    (T : ℝ≥0) (hT : T ≠ 0) :
    P {p | T < firstPassageTime (driftedBrownianPath ν p) c} =
      P {p | ∀ u : ℝ≥0, u ≤ T → p u+ν*(u : ℝ) ≤ c} := by
  have hn : ∀ᵐ p ∂P, (⨆ u : Iic T, driftedBrownianPath ν p u) ≠ c := by
    rw [ae_iff]
    simpa only [not_not] using brownianPath_drift_runningMaximum_atom_zero P hB ν c hc T hT
  apply measure_congr
  filter_upwards [brownianPath_positiveDrift_hits_ae P hB ν c hν,hn] with p hp hn
  apply propext
  rw [← not_le,firstPassageTime_le_iff]
  have hfalse : (¬∃ u : ℝ≥0, c ≤ driftedBrownianPath ν p u) = False := propext (iff_false_intro (not_not_intro hp))
  rw [hfalse,false_or]
  constructor
  · intro h u hu
    by_contra hb
    exact h ⟨u,hu,(lt_of_not_ge hb).le⟩
  · intro h hh
    obtain ⟨u,hu,hcu⟩ := hh
    have hm : (⨆ u : Iic T, driftedBrownianPath ν p u) ≤ c :=
      (brownianPath_barrier_iff_runningMaximum _ T c).mp h
    have hl := hcu.trans (le_ciSup (brownianPath_Iic_bddAbove (driftedBrownianPath ν p) T) ⟨u,hu⟩)
    exact hn (le_antisymm hm hl)



end DOZZ.Proofs

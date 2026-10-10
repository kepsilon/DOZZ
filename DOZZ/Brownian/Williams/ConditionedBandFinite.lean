/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Brownian.Williams.ThinBand
public import DOZZ.Brownian.Barrier.FirstHitFiniteDensity
/-!
# Actual finite laws of the upper-conditioned Brownian future

Infinite positive-half-line survival splits at deterministic times. The
actual surviving state and full future have the killed-state restart law,
and iteration identifies every finite coordinate law with killed densities
and the final harmonic survival factor. Normalizing telescopes those factors
into the literal Doob transition product, whose mass is one.

Reflection identifies this construction with the actual negative-drift
Brownian future conditioned below a positive upper edge, preserving every
finite sample on the original continuous-path carrier. This is the actual
finite law needed by the Williams entrance limit; no conditioned avoidance
or last-exit premise is imported or assumed.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace DOZZ.Proofs

/-- Actual infinite positive-half-line survival for Brownian motion started at a real state. -/
def brownianForeverSurvival (a x : ℝ) : Set BrownianPath :=
  {p | ∀ t : ℝ≥0, 0 ≤ x+p t+a*(t : ℝ)}

/-- Infinite survival is exactly countable finite-horizon exhaustion. -/
theorem brownianForeverSurvival_eq_iInter (a x : ℝ) :
    brownianForeverSurvival a x = ⋂ n : ℕ, brownianLowerSurvival a x (n : ℝ≥0) := by
  ext p
  simp only [brownianForeverSurvival,brownianLowerSurvival,mem_ofPred_eq,mem_iInter]
  constructor
  · intro h n t ht
    exact h t
  · intro h t
    obtain ⟨n,hn⟩ := exists_nat_ge (t : ℝ)
    exact h n t (by exact_mod_cast hn)

/-- Infinite survival is jointly measurable in its starting state and original Brownian path. -/
theorem measurableSet_brownianForeverSurvival_joint (a : ℝ) :
    MeasurableSet {z : ℝ × BrownianPath | z.2 ∈ brownianForeverSurvival a z.1} := by
  have he : {z : ℝ × BrownianPath | z.2 ∈ brownianForeverSurvival a z.1} =
      ⋂ n : ℕ, {z : ℝ × BrownianPath | z.2 ∈ brownianLowerSurvival a z.1 (n : ℝ≥0)} := by
    ext z
    simp only [brownianForeverSurvival_eq_iInter,mem_iInter,mem_ofPred_eq]
  rw [he]
  exact MeasurableSet.iInter (fun n => measurableSet_brownianLowerSurvival_joint a n)

/-- A fixed starting-state infinite survival event is measurable. -/
theorem measurableSet_brownianForeverSurvival (a x : ℝ) : MeasurableSet (brownianForeverSurvival a x) :=
  (measurableSet_brownianForeverSurvival_joint a).preimage (measurable_const.prodMk measurable_id)

/-- The actual infinite survival mass equals the harmonic function at every nonnegative state. -/
theorem brownianPath_foreverSurvival_measure (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν x : ℝ) (hν : 0 < ν) (hx : 0 ≤ x) :
    P (brownianForeverSurvival ν x) = ENNReal.ofReal (conditionedH ν x) := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  let E : Set BrownianPath := {p | ∃ t : ℝ≥0, x < -p t-ν*(t : ℝ)}
  have he : brownianForeverSurvival ν x = Eᶜ := by
    ext p
    simp only [brownianForeverSurvival,E,mem_compl_iff,mem_ofPred_eq,not_exists]
    apply forall_congr'
    intro t
    rw [not_lt]
    constructor <;> intro h <;> linarith only [h]
  have hE : MeasurableSet E := by
    have hh := (measurableSet_brownianForeverSurvival ν x).compl
    rwa [he,compl_compl] at hh
  rw [he,prob_compl_eq_one_sub hE,
    negativeDriftBrownian_maximum_tail P (fun t p => -p t) hB.neg ν x hν hx,
    conditionedH,ite_eq_right hν.ne',ENNReal.ofReal_sub 1 (Real.exp_pos _).le,ENNReal.ofReal_one]

/-- Infinite survival splits at a deterministic time into its surviving past and actual shifted future. -/
theorem brownianForeverSurvival_restart (a x : ℝ) (s : ℝ≥0) (p : BrownianPath) :
    p ∈ brownianForeverSurvival a x ↔ p ∈ brownianLowerSurvival a x s ∧
      brownianShiftPath s p ∈ brownianForeverSurvival a (x+p s+a*(s : ℝ)) := by
  constructor
  · intro h
    refine ⟨fun t ht => h t,fun t => ?_⟩
    have ht := h (s+t)
    rw [NNReal.coe_add] at ht
    change 0 ≤ (x+p s+a*(s : ℝ))+(p (s+t)-p s)+a*(t : ℝ)
    linarith only [ht]
  · rintro ⟨hp,hq⟩ t
    by_cases ht : t ≤ s
    · exact hp t ht
    · have hst : s ≤ t := (lt_of_not_ge ht).le
      have hh := hq (t-s)
      change 0 ≤ (x+p s+a*(s : ℝ))+(p (s+(t-s))-p s)+a*((t-s : ℝ≥0) : ℝ) at hh
      rw [add_tsub_cancel_of_le hst,NNReal.coe_sub hst] at hh
      linarith only [hh]


/-- Infinite-survival state and full-future tests have the actual killed-state restart law. -/
theorem brownianPath_foreverSurvival_state_future_lintegral (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (a x : ℝ) (hx : 0 < x)
    (s : ℝ≥0) (hs : s ≠ 0) (F : ℝ × BrownianPath → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p in brownianForeverSurvival a x, F (x+p s+a*(s : ℝ),brownianShiftPath s p) ∂P) =
      ∫⁻ y, ENNReal.ofReal (brownianKilledTransitionPDF a s x y)*
        ∫⁻ q in brownianForeverSurvival a y, F (y,q) ∂P := by
  classical
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  let J : ℝ × BrownianPath → ℝ≥0∞ :=
    {z : ℝ × BrownianPath | z.2 ∈ brownianForeverSurvival a z.1}.indicator F
  have hJ : Measurable J := hF.indicator (measurableSet_brownianForeverSurvival_joint a)
  have he := brownianPath_surviving_restart_lintegral P hB a x s J hJ
  have hl : (brownianLowerSurvival a x s).indicator
      (fun p => J (x+p s+a*(s : ℝ),brownianShiftPath s p)) =
      (brownianForeverSurvival a x).indicator (fun p => F (x+p s+a*(s : ℝ),brownianShiftPath s p)) := by
    funext p
    have hh := brownianForeverSurvival_restart a x s p
    simp only [J,Set.indicator_apply,mem_ofPred_eq]
    by_cases hp : p ∈ brownianLowerSurvival a x s
    · by_cases hq : brownianShiftPath s p ∈ brownianForeverSurvival a (x+p s+a*(s : ℝ))
      · simp only [ite_eq_left hp,ite_eq_left hq,ite_eq_left (hh.mpr ⟨hp,hq⟩)]
      · simp only [ite_eq_left hp,ite_eq_right hq,ite_eq_right (fun h => hq (hh.mp h).2)]
    · simp only [ite_eq_right hp,ite_eq_right (fun h => hp (hh.mp h).1)]
  rw [← lintegral_indicator (measurableSet_brownianLowerSurvival a x s),hl,
    lintegral_indicator (measurableSet_brownianForeverSurvival a x)] at he
  have hL : Measurable (fun y : ℝ => ∫⁻ q, J (y,q) ∂P) :=
    Measurable.lintegral_prod_right (f := fun y q => J (y,q)) hJ
  refine he.trans ((brownianPath_lowerKilled_endpoint_lintegral P hB a x hx s hs _ hL).trans ?_)
  apply lintegral_congr
  intro y
  congr 1
  have hj : (fun q => J (y,q)) = (brownianForeverSurvival a y).indicator (fun q => F (y,q)) := by
    funext q
    simp only [J,Set.indicator_apply,mem_ofPred_eq]
  rw [hj,lintegral_indicator (measurableSet_brownianForeverSurvival a y)]

/-- Positive coordinates sampled at the already constructed elapsed-time schedule. -/
noncomputable def brownianPositiveSamples (a : ℝ) (n : ℕ) (ds : Fin n → ℝ≥0)
    (x : ℝ) (p : BrownianPath) : Fin n → ℝ :=
  fun i => x+p (brownianFirstHitTimes n ds i)+a*(brownianFirstHitTimes n ds i : ℝ)

/-- Positive sampled coordinates are jointly measurable in their start and actual path. -/
theorem measurable_brownianPositiveSamples (a : ℝ) (n : ℕ) (ds : Fin n → ℝ≥0) :
    Measurable (fun z : ℝ × BrownianPath => brownianPositiveSamples a n ds z.1 z.2) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (measurable_fst.add ((ContinuousMap.measurable_eval _).comp measurable_snd)).add measurable_const

/-- Positive finite coordinates split into their first state and the actual shifted future coordinates. -/
theorem brownianPositiveSamples_cons (a : ℝ) (n : ℕ) (ds : Fin (n+1) → ℝ≥0)
    (x : ℝ) (p : BrownianPath) :
    brownianPositiveSamples a (n+1) ds x p = Fin.cons (x+p (ds 0)+a*(ds 0 : ℝ))
      (brownianPositiveSamples a n (Fin.tail ds) (x+p (ds 0)+a*(ds 0 : ℝ)) (brownianShiftPath (ds 0) p)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [brownianPositiveSamples,brownianFirstHitTimes,Fin.cons_zero]
  · simp only [brownianPositiveSamples,brownianFirstHitTimes,Fin.cons_succ]
    change x+p (ds 0+brownianFirstHitTimes n (Fin.tail ds) j)+
        a*((ds 0+brownianFirstHitTimes n (Fin.tail ds) j : ℝ≥0) : ℝ) =
      (x+p (ds 0)+a*(ds 0 : ℝ))+
        (p (ds 0+brownianFirstHitTimes n (Fin.tail ds) j)-p (ds 0))+
          a*(brownianFirstHitTimes n (Fin.tail ds) j : ℝ)
    rw [NNReal.coe_add]
    ring

/-- The actual finite survival law is its successive killed integrals and final harmonic mass. -/
noncomputable def brownianForeverFiniteIntegral (a : ℝ) :
    (n : ℕ) → (Fin n → ℝ≥0) → ℝ → ((Fin n → ℝ) → ℝ≥0∞) → ℝ≥0∞
  | 0, _, x, F => ENNReal.ofReal (conditionedH a x)*F (fun i : Fin 0 => Fin.elim0 i)
  | n+1, ds, x, F => ∫⁻ y : ℝ,
      ENNReal.ofReal (brownianKilledTransitionPDF a (ds 0) x y)*
        brownianForeverFiniteIntegral a n (Fin.tail ds) y (fun ys => F (Fin.cons y ys))


/-- All actual finite positive coordinates under infinite survival have the successive killed/harmonic law. -/
theorem brownianPath_foreverSurvival_finite_lintegral (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν : ℝ) (hν : 0 < ν)
    (n : ℕ) (ds : Fin n → ℝ≥0) (hds : ∀ i, 0 < ds i)
    (x : ℝ) (hx : 0 < x) (F : (Fin n → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p in brownianForeverSurvival ν x, F (brownianPositiveSamples ν n ds x p) ∂P) =
      brownianForeverFiniteIntegral ν n ds x F := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  induction n generalizing x with
  | zero =>
      have he : (fun p : BrownianPath => F (brownianPositiveSamples ν 0 ds x p)) =
          fun _ => F (fun i : Fin 0 => Fin.elim0 i) := by
        funext p
        congr 1
        exact Subsingleton.elim _ _
      rw [he,setLIntegral_const,brownianPath_foreverSurvival_measure P hB ν x hν hx.le]
      exact mul_comm _ _
  | succ n ih =>
      let J : ℝ × BrownianPath → ℝ≥0∞ :=
        fun z => F (Fin.cons z.1 (brownianPositiveSamples ν n (Fin.tail ds) z.1 z.2))
      have hJ : Measurable J := hF.comp ((measurable_fin_cons_real n).comp
        (measurable_fst.prodMk (measurable_brownianPositiveSamples ν n (Fin.tail ds))))
      have he := brownianPath_foreverSurvival_state_future_lintegral P hB ν x hx (ds 0) (hds 0).ne' J hJ
      have hleft : (fun p => F (brownianPositiveSamples ν (n+1) ds x p)) =
          fun p => J (x+p (ds 0)+ν*(ds 0 : ℝ),brownianShiftPath (ds 0) p) := by
        funext p
        rw [brownianPositiveSamples_cons]
      rw [hleft]
      refine he.trans ?_
      apply lintegral_congr
      intro y
      by_cases hy : 0 < y
      · have hFy : Measurable (fun ys : Fin n → ℝ => F (Fin.cons y ys)) :=
          hF.comp ((measurable_fin_cons_real n).comp (measurable_const.prodMk measurable_id))
        change ENNReal.ofReal (brownianKilledTransitionPDF ν (ds 0) x y)*
            (∫⁻ q in brownianForeverSurvival ν y, F (Fin.cons y (brownianPositiveSamples ν n (Fin.tail ds) y q)) ∂P) = _
        rw [ih (Fin.tail ds) (fun i => hds i.succ) y hy _ hFy]
      · simp only [brownianKilledTransitionPDF,hx,hy,and_false,ite_false,
          ENNReal.ofReal_zero,zero_mul]

/-- The explicit finite killed density, with its final infinite-survival harmonic factor. -/
noncomputable def brownianForeverFinitePDF (a : ℝ) :
    (n : ℕ) → (Fin n → ℝ≥0) → ℝ → (Fin n → ℝ) → ℝ≥0∞
  | 0, _, x, _ => ENNReal.ofReal (conditionedH a x)
  | n+1, ds, x, ys => ENNReal.ofReal (brownianKilledTransitionPDF a (ds 0) x (ys 0))*
      brownianForeverFinitePDF a n (Fin.tail ds) (ys 0) (Fin.tail ys)

/-- The explicit finite survival density is jointly measurable in its start and all states. -/
theorem measurable_brownianForeverFinitePDF (a : ℝ) (n : ℕ) (ds : Fin n → ℝ≥0) :
    Measurable (fun z : ℝ × (Fin n → ℝ) => brownianForeverFinitePDF a n ds z.1 z.2) := by
  induction n with
  | zero =>
      have hH : Measurable (conditionedH a) := by unfold conditionedH; split_ifs <;> fun_prop
      exact hH.ennreal_ofReal.comp measurable_fst
  | succ n ih =>
      have hy : Measurable (fun z : ℝ × (Fin (n+1) → ℝ) => z.2 0) :=
        (measurable_pi_apply 0).comp measurable_snd
      exact (((measurable_brownianKilledTransitionPDF a (ds 0)).comp
        (measurable_fst.prodMk hy)).ennreal_ofReal).mul
          ((ih (Fin.tail ds)).comp (hy.prodMk ((measurable_fin_tail_real n).comp measurable_snd)))

/-- The finite iterated killed/harmonic integral is exactly its product-volume density integral. -/
theorem brownianForeverFiniteIntegral_eq_density (a : ℝ) (n : ℕ) (ds : Fin n → ℝ≥0) (x : ℝ)
    (F : (Fin n → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    brownianForeverFiniteIntegral a n ds x F = ∫⁻ ys, brownianForeverFinitePDF a n ds x ys*F ys := by
  induction n generalizing x with
  | zero =>
      rw [lintegral_unique]
      have hv : (volume : Measure (Fin 0 → ℝ)) univ = 1 := Measure.pi_empty_univ (fun _ : Fin 0 => (volume : Measure ℝ))
      rw [hv,mul_one]
      apply congrArg (fun ys : Fin 0 → ℝ => ENNReal.ofReal (conditionedH a x)*F ys)
      exact Subsingleton.elim _ _
  | succ n ih =>
      have hm (y : ℝ) : Measurable (fun ys : Fin n → ℝ => brownianForeverFinitePDF a n (Fin.tail ds) y ys) :=
        (measurable_brownianForeverFinitePDF a n (Fin.tail ds)).comp (measurable_const.prodMk measurable_id)
      have hFy (y : ℝ) : Measurable (fun ys : Fin n → ℝ => F (Fin.cons y ys)) :=
        hF.comp ((measurable_fin_cons_real n).comp (measurable_const.prodMk measurable_id))
      have hD : Measurable (fun ys : Fin (n+1) → ℝ => brownianForeverFinitePDF a (n+1) ds x ys*F ys) :=
        ((measurable_brownianForeverFinitePDF a (n+1) ds).comp
          (measurable_const.prodMk measurable_id)).mul hF
      rw [brownian_lintegral_fin_cons n _ hD]
      change (∫⁻ y : ℝ, ENNReal.ofReal (brownianKilledTransitionPDF a (ds 0) x y)*
          brownianForeverFiniteIntegral a n (Fin.tail ds) y (fun ys => F (Fin.cons y ys))) = _
      apply lintegral_congr
      intro y
      rw [ih (Fin.tail ds) y _ (hFy y)]
      have hp : Measurable (fun ys : Fin n → ℝ =>
          brownianForeverFinitePDF a n (Fin.tail ds) y ys*F (Fin.cons y ys)) := (hm y).mul (hFy y)
      rw [← lintegral_const_mul _ hp]
      apply lintegral_congr
      intro ys
      simp only [brownianForeverFinitePDF,Fin.cons_zero,Fin.tail_cons]
      exact (mul_assoc _ _ _).symm


/-- The actual finite survival density has exactly the total harmonic survival mass. -/
theorem lintegral_brownianForeverFinitePDF (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν : ℝ) (hν : 0 < ν)
    (n : ℕ) (ds : Fin n → ℝ≥0) (hds : ∀ i, 0 < ds i) (x : ℝ) (hx : 0 < x) :
    (∫⁻ ys, brownianForeverFinitePDF ν n ds x ys) = ENNReal.ofReal (conditionedH ν x) := by
  have he := brownianPath_foreverSurvival_finite_lintegral P hB ν hν n ds hds x hx (fun _ => 1) measurable_const
  rw [brownianForeverFiniteIntegral_eq_density ν n ds x (fun _ => 1) measurable_const] at he
  simp only [mul_one,lintegral_one,Measure.restrict_apply MeasurableSet.univ,univ_inter] at he
  exact he.symm.trans (brownianPath_foreverSurvival_measure P hB ν x hν hx.le)

private theorem harmonic_positive (ν x : ℝ) (hν : 0 < ν) (hx : 0 < x) :
    0 < conditionedH ν x := by
  rw [conditionedH,ite_eq_right hν.ne']
  exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith only [hν,hx]))

/-- The Doob kernel is exactly the positive-drift killed kernel times its harmonic ratio. -/
theorem conditionedPositiveTransitionDensity_eq_killed (ν : ℝ) (hν : 0 < ν)
    (T : ℝ≥0) (hT : 0 < T) (x y : ℝ) (hx : 0 < x) :
    conditionedPositiveTransitionDensity ν T x y =
      brownianKilledTransitionPDF ν T x y*conditionedH ν y/conditionedH ν x := by
  by_cases hy : 0 < y
  · have hTR : 0 < (T : ℝ) := hT
    simp only [conditionedPositiveTransitionDensity,hν.le,hTR,hx,hy,and_self,ite_true,
      brownianKilledTransitionPDF,brownianHeatDensity,gaussianPDFReal,sub_zero]
    ring
  · simp only [conditionedPositiveTransitionDensity,hy,and_false,ite_false,
      brownianKilledTransitionPDF,zero_mul,zero_div]

/-- The exact killed-to-Doob harmonic cancellation retains every finite transition factor. -/
theorem brownianKilledTransitionPDF_harmonic_cancel (ν : ℝ) (hν : 0 < ν)
    (T : ℝ≥0) (hT : 0 < T) (x y : ℝ) (hx : 0 < x) :
    ENNReal.ofReal (brownianKilledTransitionPDF ν T x y)*ENNReal.ofReal (conditionedH ν y) =
      ENNReal.ofReal (conditionedH ν x)*ENNReal.ofReal (conditionedPositiveTransitionDensity ν T x y) := by
  have hHx := harmonic_positive ν x hν hx
  rw [conditionedPositiveTransitionDensity_eq_killed ν hν T hT x y hx,
    ENNReal.ofReal_div_of_pos hHx,
    ENNReal.ofReal_mul (brownianKilledTransitionPDF_nonneg ν T hT.ne' x y),div_eq_mul_inv]
  calc
    _ = (ENNReal.ofReal (conditionedH ν x)*(ENNReal.ofReal (conditionedH ν x))⁻¹)*
        (ENNReal.ofReal (brownianKilledTransitionPDF ν T x y)*ENNReal.ofReal (conditionedH ν y)) := by
      rw [ENNReal.mul_inv_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hHx)) ENNReal.ofReal_ne_top,one_mul]
    _ = _ := by ring

/-- The finite positive-start Doob transition density on the explicit elapsed schedule. -/
noncomputable def brownianDoobFinitePDF (ν : ℝ) :
    (n : ℕ) → (Fin n → ℝ≥0) → ℝ → (Fin n → ℝ) → ℝ≥0∞
  | 0, _, _, _ => 1
  | n+1, ds, x, ys => ENNReal.ofReal (conditionedPositiveTransitionDensity ν (ds 0) x (ys 0))*
      brownianDoobFinitePDF ν n (Fin.tail ds) (ys 0) (Fin.tail ys)

/-- The normalized actual finite survival density is exactly the Doob transition product. -/
theorem brownianForeverFinitePDF_eq_harmonic_mul_doob (ν : ℝ) (hν : 0 < ν)
    (n : ℕ) (ds : Fin n → ℝ≥0) (hds : ∀ i, 0 < ds i) (x : ℝ) (hx : 0 < x) (ys : Fin n → ℝ) :
    brownianForeverFinitePDF ν n ds x ys = ENNReal.ofReal (conditionedH ν x)*brownianDoobFinitePDF ν n ds x ys := by
  induction n generalizing x with
  | zero => exact (mul_one _).symm
  | succ n ih =>
      change ENNReal.ofReal (brownianKilledTransitionPDF ν (ds 0) x (ys 0))*
          brownianForeverFinitePDF ν n (Fin.tail ds) (ys 0) (Fin.tail ys) =
        ENNReal.ofReal (conditionedH ν x)*
          (ENNReal.ofReal (conditionedPositiveTransitionDensity ν (ds 0) x (ys 0))*
            brownianDoobFinitePDF ν n (Fin.tail ds) (ys 0) (Fin.tail ys))
      by_cases hy : 0 < ys 0
      · rw [ih (Fin.tail ds) (fun i => hds i.succ) (ys 0) hy (Fin.tail ys),← mul_assoc,
          brownianKilledTransitionPDF_harmonic_cancel ν hν (ds 0) (hds 0) x (ys 0) hx,mul_assoc]
      · simp only [brownianKilledTransitionPDF,conditionedPositiveTransitionDensity,hx,hy,and_false,
          ite_false,ENNReal.ofReal_zero,mul_zero,zero_mul]

/-- The normalized actual finite Doob density has mass one. -/
theorem lintegral_brownianDoobFinitePDF_one (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν : ℝ) (hν : 0 < ν)
    (n : ℕ) (ds : Fin n → ℝ≥0) (hds : ∀ i, 0 < ds i) (x : ℝ) (hx : 0 < x) :
    (∫⁻ ys, brownianDoobFinitePDF ν n ds x ys) = 1 := by
  have hh := lintegral_brownianForeverFinitePDF P hB ν hν n ds hds x hx
  have hHx := harmonic_positive ν x hν hx
  have hn : ENNReal.ofReal (conditionedH ν x) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hHx)
  have he (ys : Fin n → ℝ) : brownianDoobFinitePDF ν n ds x ys =
      (ENNReal.ofReal (conditionedH ν x))⁻¹*brownianForeverFinitePDF ν n ds x ys := by
    rw [brownianForeverFinitePDF_eq_harmonic_mul_doob ν hν n ds hds x hx ys,← mul_assoc,
      ENNReal.inv_mul_cancel hn ENNReal.ofReal_ne_top,one_mul]
  simp_rw [he]
  have hm : Measurable (brownianForeverFinitePDF ν n ds x) :=
    (measurable_brownianForeverFinitePDF ν n ds).comp (measurable_const.prodMk measurable_id)
  rw [lintegral_const_mul _ hm,hh,ENNReal.inv_mul_cancel hn ENNReal.ofReal_ne_top]

/-- Every normalized finite Doob density is measurable, directly from its actual killed density. -/
theorem measurable_brownianDoobFinitePDF (ν : ℝ) (hν : 0 < ν)
    (n : ℕ) (ds : Fin n → ℝ≥0) (hds : ∀ i, 0 < ds i) (x : ℝ) (hx : 0 < x) :
    Measurable (brownianDoobFinitePDF ν n ds x) := by
  have hHx := harmonic_positive ν x hν hx
  have hm : Measurable (brownianForeverFinitePDF ν n ds x) :=
    (measurable_brownianForeverFinitePDF ν n ds).comp (measurable_const.prodMk measurable_id)
  convert (measurable_const (a := (ENNReal.ofReal (conditionedH ν x))⁻¹)).mul hm using 1
  funext ys
  change brownianDoobFinitePDF ν n ds x ys =
    (ENNReal.ofReal (conditionedH ν x))⁻¹*brownianForeverFinitePDF ν n ds x ys
  rw [brownianForeverFinitePDF_eq_harmonic_mul_doob ν hν n ds hds x hx ys,← mul_assoc,
    ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hHx)) ENNReal.ofReal_ne_top,one_mul]

/-- Reflecting whole-path upper conditioning gives the actual infinite positive-survival tests. -/
theorem brownianPath_below_finite_reflect_lintegral (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν x : ℝ) (hν : 0 < ν)
    (n : ℕ) (ds : Fin n → ℝ≥0) (F : (Fin n → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p in {p | ∀ t : ℝ≥0, driftedBrownianPath (-ν) p t < x},
      F (fun i => x-driftedBrownianPath (-ν) p (brownianFirstHitTimes n ds i)) ∂P) =
      ∫⁻ p in brownianForeverSurvival ν x, F (brownianPositiveSamples ν n ds x p) ∂P := by
  classical
  let _ := noAtoms_brownianMaximumReferenceLaw ν
  have hM := aemeasurable_driftedBrownianMaximum P hB ν hν
  have hne : ∀ᵐ p ∂P, driftedBrownianMaximum ν p ≠ x := by
    apply ae_of_ae_map (p := fun z : ℝ => z ≠ x) hM
    rw [brownianPath_globalMaximum_map P hB ν hν]
    exact Measure.ae_ne _ x
  have ha : ∀ᵐ p ∂P, (-p ∈ brownianForeverSurvival ν x) ↔
      ∀ t : ℝ≥0, driftedBrownianPath (-ν) p t < x := by
    filter_upwards [brownianPath_negativeDrift_maximum_attained_ae P hB ν hν,hne] with p hp hn
    have hw : (-p ∈ brownianForeverSurvival ν x) ↔ driftedBrownianMaximum ν p ≤ x := by
      constructor
      · intro h
        apply csSup_le (range_nonempty _)
        rintro y ⟨t,rfl⟩
        have ht := h t
        change 0 ≤ x+(-p t)+ν*(t : ℝ) at ht
        linarith only [ht]
      · intro h t
        have ht := le_csSup hp.1 (mem_range_self t)
        change p t-ν*(t : ℝ) ≤ driftedBrownianMaximum ν p at ht
        change 0 ≤ x+(-p t)+ν*(t : ℝ)
        linarith only [ht,h]
    have hs : (∀ t : ℝ≥0, driftedBrownianPath (-ν) p t < x) ↔ driftedBrownianMaximum ν p < x := by
      constructor
      · intro h
        obtain ⟨t,ht⟩ := hp.2
        have hh := h t
        change p t+(-ν)*(t : ℝ) < x at hh
        have hh' : p t-ν*(t : ℝ) < x := by simpa only [neg_mul,← sub_eq_add_neg] using hh
        rwa [ht] at hh'
      · intro h t
        have ht := le_csSup hp.1 (mem_range_self t)
        change p t-ν*(t : ℝ) ≤ driftedBrownianMaximum ν p at ht
        change p t+(-ν)*(t : ℝ) < x
        simpa only [neg_mul,← sub_eq_add_neg] using ht.trans_lt h
    rw [hw,hs]
    exact le_iff_lt_or_eq.trans (or_iff_left hn)
  let J : BrownianPath → ℝ≥0∞ := (brownianForeverSurvival ν x).indicator
    (fun p => F (brownianPositiveSamples ν n ds x p))
  have hmJ : Measurable J :=
    (hF.comp ((measurable_brownianPositiveSamples ν n ds).comp
      (measurable_const.prodMk measurable_id))).indicator (measurableSet_brownianForeverSurvival ν x)
  have ht := lintegral_map hmJ (measurable_neg : Measurable (fun p : BrownianPath => -p)) (μ := P)
  rw [brownianPath_neg_map P hB] at ht
  let E : Set BrownianPath := {p | ∀ t : ℝ≥0, driftedBrownianPath (-ν) p t < x}
  have hE : MeasurableSet E := (measurableSet_brownianPath_below x).preimage
    (continuous_driftedBrownianPath.measurable.comp (measurable_const.prodMk measurable_id))
  have he : (fun p => J (-p)) =ᵐ[P] E.indicator
      (fun p => F (fun i => x-driftedBrownianPath (-ν) p (brownianFirstHitTimes n ds i))) := by
    filter_upwards [ha] with p hp
    have hcoords : brownianPositiveSamples ν n ds x (-p) =
        fun i => x-driftedBrownianPath (-ν) p (brownianFirstHitTimes n ds i) := by
      funext i
      change x+(-p (brownianFirstHitTimes n ds i))+ν*(brownianFirstHitTimes n ds i : ℝ) =
        x-(p (brownianFirstHitTimes n ds i)+(-ν)*(brownianFirstHitTimes n ds i : ℝ))
      ring
    simp only [J,E,Set.indicator_apply,mem_ofPred_eq,hcoords,hp]
  rw [lintegral_congr_ae he,lintegral_indicator hE] at ht
  have hr : (∫⁻ p, J p ∂P) =
      ∫⁻ p in brownianForeverSurvival ν x, F (brownianPositiveSamples ν n ds x p) ∂P :=
    lintegral_indicator (measurableSet_brownianForeverSurvival ν x) _
  exact ht.symm.trans hr

/-- The normalized actual upper-conditioned finite law is exactly the positive-start Doob product. -/
theorem brownianBelowConditionedLaw_finite_positive_density_map (P : Measure BrownianPath)
    (hB : IsBrownianReal (fun t p => p t) P) (ν x : ℝ) (hν : 0 < ν) (hx : 0 < x)
    (n : ℕ) (ds : Fin n → ℝ≥0) (hds : ∀ i, 0 < ds i) :
    (brownianBelowConditionedLaw P ν x).map
      (fun q i => x-q (brownianFirstHitTimes n ds i)) =
      volume.withDensity (brownianDoobFinitePDF ν n ds x) := by
  have hm : Measurable (fun q : BrownianPath => fun i => x-q (brownianFirstHitTimes n ds i)) := by
    apply measurable_pi_iff.mpr
    intro i
    exact measurable_const.sub (ContinuousMap.measurable_eval _)
  have hD := measurable_brownianDoobFinitePDF ν hν n ds hds x hx
  apply Measure.ext_of_lintegral
  intro F hF
  have hFm : Measurable (fun q : BrownianPath => F (fun i => x-q (brownianFirstHitTimes n ds i))) := hF.comp hm
  rw [lintegral_map hF hm,lintegral_brownianBelowConditionedLaw P ν x _ hFm,
    brownianPath_below_finite_reflect_lintegral P hB ν x hν n ds F hF,
    brownianPath_foreverSurvival_finite_lintegral P hB ν hν n ds hds x hx F hF,
    brownianForeverFiniteIntegral_eq_density ν n ds x F hF]
  have hprod : Measurable (fun ys : Fin n → ℝ => brownianForeverFinitePDF ν n ds x ys*F ys) :=
    ((measurable_brownianForeverFinitePDF ν n ds).comp (measurable_const.prodMk measurable_id)).mul hF
  rw [← lintegral_const_mul _ hprod,lintegral_withDensity_eq_lintegral_mul _ hD hF]
  apply lintegral_congr
  intro ys
  rw [brownianForeverFinitePDF_eq_harmonic_mul_doob ν hν n ds hds x hx ys]
  rw [← mul_assoc,← mul_assoc,ENNReal.inv_mul_cancel
    (ne_of_gt (ENNReal.ofReal_pos.mpr (harmonic_positive ν x hν hx))) ENNReal.ofReal_ne_top,one_mul]
  rfl

end DOZZ.Proofs

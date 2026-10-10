/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitDyadicMixture
public import DOZZ.Brownian.LastExitFinite
public import DOZZ.Brownian.LastExitPostPathMeasurability
public import DOZZ.Brownian.WienerExists
public import DOZZ.Brownian.ConditionedFDDUniqueness
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Finite rational projections of the post-last-exit path

The dyadic cell mixture converges on every measurable finite rational projection. The selected
continuous paths themselves converge pointwise in path space, so the limiting post-last-exit path
has the same finite rational projection law as the entrance density.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

private theorem tendsto_map_of_ae_pointwise
    {Ω E : Type*} [MeasurableSpace Ω] [TopologicalSpace E] [MeasurableSpace E]
    [BorelSpace E] (Q : ProbabilityMeasure Ω) (f : ℕ → Ω → E) (g : Ω → E)
    (hf : ∀ n, Measurable (f n)) (hg : Measurable g)
    (hlim : ∀ᵐ ω ∂(Q : Measure Ω),
      Tendsto (fun n => f n ω) atTop (𝓝 (g ω))) :
    Tendsto (fun n => Q.map (f n)) atTop (𝓝 (Q.map g)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro test
  have hmap (n : ℕ) :
      (∫ x, test x ∂(Q.map (f n) : Measure E)) =
        ∫ ω, test (f n ω) ∂(Q : Measure Ω) :=
    integral_map (hf n).aemeasurable test.continuous.measurable.aestronglyMeasurable
  have hmapg :
      (∫ x, test x ∂(Q.map g : Measure E)) =
        ∫ ω, test (g ω) ∂(Q : Measure Ω) :=
    integral_map hg.aemeasurable test.continuous.measurable.aestronglyMeasurable
  simp_rw [hmap, hmapg]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖test‖)
  · intro n
    exact (test.continuous.measurable.comp (hf n)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact ae_of_all _ fun ω => test.norm_coe_le_norm (f n ω)
  · exact hlim.mono fun ω hω => test.continuous.continuousAt.tendsto.comp hω

/-- The dyadic path approximation converges continuously to the literal recentered post-last-exit
path, for every input continuous path. -/
theorem dyadicLastExitPathApproximation_tendsto
    (p : BrownianPath) (c : ℝ) :
    Tendsto (fun n => dyadicLastExitPathApproximation n c p) atTop
      (𝓝 (negativeConditionedPostLastExitPath c p)) := by
  let τ := negativeLastExitTime p c
  have htimeReal : Tendsto
      (fun n : ℕ => (dyadicLastExitCeilingTime n τ : ℝ)) atTop (𝓝 (τ : ℝ)) := by
    simpa [τ] using dyadicLastExitCeilingTime_coe_tendsto τ
  have htime : Tendsto (fun n : ℕ => dyadicLastExitCeilingTime n τ) atTop (𝓝 τ) :=
    NNReal.tendsto_coe.mp htimeReal
  have hpair : Tendsto
      (fun n : ℕ => (dyadicLastExitCeilingTime n τ, p)) atTop (𝓝 (τ, p)) :=
    htime.prodMk_nhds tendsto_const_nhds
  have hcont : Tendsto
      (fun n : ℕ => shiftPathAddConstant c (dyadicLastExitCeilingTime n τ, p))
      atTop (𝓝 (shiftPathAddConstant c (τ, p))) :=
    (continuous_shiftPathAddConstant c).continuousAt.tendsto.comp hpair
  have heq : shiftPathAddConstant c (τ, p) = negativeConditionedPostLastExitPath c p := by
    ext s
    rfl
  simpa [dyadicLastExitPathApproximation, τ, heq] using hcont

/-- Every measurable finite projection at positive rational offsets of the post-last-exit path
has the conditioned entrance law. -/
theorem negativeConditionedPostLastExit_positiveRationalProjection
    {ν c : ℝ} {P B Q : Measure BrownianPath} [SFinite B]
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (hB : IsBrownianReal (fun t p => p t) B)
    (hQ : IsNegativeConditionedBrownianLaw ν Q)
    (hν : 0 < ν) (hc : 0 < c)
    (n : ℕ) (offsets : Fin n → ℚ)
    (hoff : ∀ i, 0 < (offsets i : ℝ)) (hmono : StrictMono offsets) :
    (P.map (fun p i => -(negativeConditionedPostLastExitPath c p
        (Real.toNNReal (offsets i : ℝ))))) =
      volume.withDensity (brownianEntranceFinitePDF ν n
        (brownianFirstHitElapsed n (fun i => Real.toNNReal (offsets i)))) := by
  classical
  let := hP.2.1
  let ts : Fin n → ℝ≥0 := fun i => Real.toNNReal (offsets i)
  let ds : Fin n → ℝ≥0 := brownianFirstHitElapsed n ts
  have hts0 : ∀ i, 0 < ts i := fun i => Real.toNNReal_pos.mpr (hoff i)
  have htsmono : StrictMono ts := by
    intro i j hij
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (hoff i).le,
      Real.coe_toNNReal _ (hoff j).le]
    exact_mod_cast hmono hij
  have hds : ∀ i, 0 < ds i :=
    fun i => brownianFirstHitElapsed_pos n ts hts0 htsmono i
  have htime (i : Fin n) :
      (⟨(offsets i : ℝ), (hoff i).le⟩ : ℝ≥0) = ts i := by
    apply Subtype.ext
    simp [ts, Real.coe_toNNReal _ (hoff i).le]
  let M : Measure (Fin n → ℝ) := volume.withDensity (brownianEntranceFinitePDF ν n ds)
  have hMprob : IsProbabilityMeasure M := by
    refine ⟨?_⟩
    change (volume.withDensity (brownianEntranceFinitePDF ν n ds)) Set.univ = 1
    rw [withDensity_apply _ MeasurableSet.univ]
    simpa only [setLIntegral_univ] using
      lintegral_brownianEntranceFinitePDF_one Q ν hν hQ n ds hds
  let μ : ProbabilityMeasure (Fin n → ℝ) := ⟨M, hMprob⟩
  let f : BrownianPath → Fin n → ℝ := fun p i =>
    -(negativeConditionedPostLastExitPath c p (ts i))
  let fdyad : ℕ → BrownianPath → Fin n → ℝ := fun k p i =>
    dyadicPositiveLastExitRationalEvals k c p (offsets i)
  have hfdyad : ∀ k, Measurable (fdyad k) := by
    intro k
    apply measurable_pi_iff.mpr
    intro i
    exact (measurable_pi_apply (offsets i)).comp
      (measurable_dyadicPositiveLastExitRationalEvals k c)
  have hf : Measurable f := by
    apply measurable_pi_iff.mpr
    intro i
    exact ((ContinuousMap.measurable_eval (ts i)).comp
      (measurable_negativeConditionedPostLastExitPath c)).neg
  let μdyad : ℕ → ProbabilityMeasure (Fin n → ℝ) := fun k =>
    ProbabilityMeasure.map (⟨P, hP.2.1⟩ : ProbabilityMeasure BrownianPath)
      (fdyad k)
  let μpost : ProbabilityMeasure (Fin n → ℝ) :=
    ProbabilityMeasure.map (⟨P, hP.2.1⟩ : ProbabilityMeasure BrownianPath) f
  have hpoint : ∀ p, Tendsto (fun k => fdyad k p) atTop (𝓝 (f p)) := by
    intro p
    have hpath := dyadicLastExitPathApproximation_tendsto p c
    apply tendsto_pi_nhds.mpr
    intro i
    have heval : (fun k => fdyad k p i) =
        fun k => -(dyadicLastExitPathApproximation k c p (ts i)) := by
      funext k
      simp only [fdyad, dyadicPositiveLastExitRationalEvals,
        brownianPathRationalEvals, max_eq_left (hoff i).le]
      rw [htime i]
    rw [heval]
    exact (continuous_eval_const (ts i)).neg.continuousAt.tendsto.comp hpath
  have hpathLaw : Tendsto μdyad atTop (𝓝 μpost) :=
    tendsto_map_of_ae_pointwise ⟨P, hP.2.1⟩ fdyad f hfdyad hf
      (Filter.Eventually.of_forall hpoint)
  have hmix := negativeConditionedDyadicLastExit_finiteProjection_tendsto_entrance
    hP hB hν hQ ⟨c, hc.le⟩ hc n offsets hoff hmono
  have hprobEvent (A : Set (Fin n → ℝ)) (hA : MeasurableSet A) :
      Tendsto (fun k => μdyad k A) atTop (𝓝 (μ A)) := by
    have hpre (k : ℕ) : fdyad k ⁻¹' A =
        dyadicPositiveLastExitRationalEvent k c
          {y | (fun i => y (offsets i)) ∈ A} := by
      ext p
      rfl
    have hreal : Tendsto
        (fun k => ((μdyad k : Measure (Fin n → ℝ)) A).toReal)
        atTop (𝓝 ((M A).toReal)) := by
      have heq (k : ℕ) :
          ((μdyad k : Measure (Fin n → ℝ)) A).toReal =
            P.real (dyadicPositiveLastExitRationalEvent k c
              {y | (fun i => y (offsets i)) ∈ A}) := by
        have happly : (μdyad k : Measure (Fin n → ℝ)) A = P (fdyad k ⁻¹' A) := by
          change (P.map (fdyad k)) A = _
          rw [Measure.map_apply (hfdyad k) hA]
        rw [happly, hpre]
        rfl
      simpa [M, ds] using Tendsto.congr'
        (Filter.Eventually.of_forall fun k => (heq k).symm) (hmix A hA)
    have hfinite : ∀ k, (μdyad k : Measure (Fin n → ℝ)) A ≠ ∞ :=
      fun k => measure_ne_top _ _
    have hmeasure : Tendsto (fun k => (μdyad k : Measure (Fin n → ℝ)) A)
        atTop (𝓝 (M A)) :=
      (ENNReal.tendsto_toReal_iff hfinite (measure_ne_top M A)).mp hreal
    have hnn := (ENNReal.tendsto_toNNReal_iff (measure_ne_top M A) hfinite).2 hmeasure
    change Tendsto (fun k => ((μdyad k : Measure (Fin n → ℝ)) A).toNNReal)
      atTop (𝓝 ((M A).toNNReal))
    exact hnn
  have hweak : Tendsto μdyad atTop (𝓝 μ) := by
    apply IsPiSystem.tendsto_probabilityMeasure_of_tendsto_of_mem
      (S := {U : Set (Fin n → ℝ) | @IsOpen (Fin n → ℝ) inferInstance U})
    · intro U hU V hV hne
      change IsOpen U at hU
      change IsOpen V at hV
      exact hU.inter hV
    · intro U hU
      change IsOpen U at hU
      exact hU.measurableSet
    · intro U hU x hx
      change IsOpen U at hU
      exact ⟨U, hU, hU.mem_nhds hx, Subset.rfl⟩
    · intro U hU
      change IsOpen U at hU
      exact hprobEvent U hU.measurableSet
  have hμeq : μpost = μ := tendsto_nhds_unique hpathLaw hweak
  have hdsEq : ds = brownianFirstHitElapsed n
      (fun i => Real.toNNReal (offsets i)) := rfl
  have hμeq' : (μpost : Measure (Fin n → ℝ)) = (μ : Measure (Fin n → ℝ)) :=
    congrArg (fun R : ProbabilityMeasure (Fin n → ℝ) => (R : Measure (Fin n → ℝ))) hμeq
  change (ProbabilityMeasure.map (⟨P, hP.2.1⟩ : ProbabilityMeasure BrownianPath) f).toMeasure = M at hμeq'
  change P.map f = M at hμeq'
  simpa [f, ts, M, ds, hdsEq] using hμeq'

/-- The finite positive rational projections of any conditioned path law are the same
entrance-density measures used by the dyadic mixture. -/
theorem negativeConditionedLaw_positiveRationalProjection
    {ν : ℝ} {P : Measure BrownianPath}
    (hP : IsNegativeConditionedBrownianLaw ν P) (hν : 0 < ν)
    {n : ℕ} (hn : 0 < n) (offsets : Fin n → ℚ)
    (hoff : ∀ i, 0 < (offsets i : ℝ)) (hmono : StrictMono offsets) :
    (P.map (fun p i => -(p (Real.toNNReal (offsets i : ℝ))))) =
      volume.withDensity (brownianEntranceFinitePDF ν n
        (brownianFirstHitElapsed n (fun i => Real.toNNReal (offsets i : ℝ)))) := by
  classical
  let ts : Fin n → ℝ≥0 := fun i => Real.toNNReal (offsets i : ℝ)
  let ds : Fin n → ℝ≥0 := brownianFirstHitElapsed n ts
  have hts0 : ∀ i, 0 < ts i := fun i => Real.toNNReal_pos.mpr (hoff i)
  have htsmono : StrictMono ts := by
    intro i j hij
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ (hoff i).le,
      Real.coe_toNNReal _ (hoff j).le]
    exact_mod_cast hmono hij
  have hds : ∀ i, 0 < ds i :=
    fun i => brownianFirstHitElapsed_pos n ts hts0 htsmono i
  have htimes : brownianFirstHitTimes n ds = ts := by
    cases n with
    | zero => simp at hn
    | succ m => exact brownianFirstHitTimes_elapsed m ts htsmono.monotone
  have hfd := negativeConditionedLaw_positiveFDD hP n hn ts hts0 htsmono
  have hpdf (x : Fin n → ℝ) :
      brownianEntranceFinitePDF ν n ds x =
        ENNReal.ofReal (max 0 (conditionedPositiveFDDDensity ν
          (List.ofFn fun i => (ts i : ℝ)) (List.ofFn fun i => x i))) := by
    rw [brownianEntranceFinitePDF_eq_conditionedPositiveFDDDensity ν hν n ds hds x, htimes]
    rw [ENNReal.ofReal_max]
    have hnonneg := conditionedPositiveFDDDensity_nonneg hP.1
      (List.ofFn fun i => (ts i : ℝ)) (List.ofFn fun i => x i) (by simp)
    simp
  have hmeas : Measurable (brownianEntranceFinitePDF ν n ds) :=
    measurable_brownianEntranceFinitePDF ν hν n ds hds
  have hmeasure : volume.withDensity (brownianEntranceFinitePDF ν n ds) =
      volume.withDensity (fun x => ENNReal.ofReal (max 0
        (conditionedPositiveFDDDensity ν (List.ofFn fun i => (ts i : ℝ))
          (List.ofFn fun i => x i)))) := by
    rw [show brownianEntranceFinitePDF ν n ds = fun x =>
        ENNReal.ofReal (max 0 (conditionedPositiveFDDDensity ν
          (List.ofFn fun i => (ts i : ℝ)) (List.ofFn fun i => x i))) from funext hpdf]
  rw [hfd, hmeasure]

private def postLastExitPositiveRationalEvals (p : BrownianPath) :
    {q : ℚ // 0 < (q : ℝ)} → ℝ := fun q =>
  -(p ⟨(q.val : ℝ), q.property.le⟩)

private def postLastExitRationalEvalRect
    (I : Finset {q : ℚ // 0 < (q : ℝ)})
    (S : {q : ℚ // 0 < (q : ℝ)} → Set ℝ) : Set BrownianPath :=
  {p | ∀ q ∈ I, postLastExitPositiveRationalEvals p q ∈ S q}

private def postLastExitRationalEvalRectangles : Set (Set BrownianPath) :=
  {A | ∃ I S, (∀ q, MeasurableSet (S q)) ∧
    A = postLastExitRationalEvalRect I S}

private theorem measurable_postLastExitPositiveRationalEvals :
    Measurable postLastExitPositiveRationalEvals := by
  apply measurable_pi_iff.mpr
  intro q
  let t : ℝ≥0 := ⟨(q.val : ℝ), q.property.le⟩
  exact (ContinuousMap.measurable_eval t).neg

private theorem postLastExitRationalEvalRectangles_piSystem :
    IsPiSystem postLastExitRationalEvalRectangles := by
  intro A hA B hB hne
  rcases hA with ⟨I, S, hS, rfl⟩
  rcases hB with ⟨J, T, hT, rfl⟩
  let U : {q : ℚ // 0 < (q : ℝ)} → Set ℝ := fun q =>
    (if q ∈ I then S q else Set.univ) ∩ (if q ∈ J then T q else Set.univ)
  refine ⟨I ∪ J, U, ?_, ?_⟩
  · intro q
    dsimp [U]
    split_ifs <;> simp [hS, hT]
  · ext p
    simp only [postLastExitRationalEvalRect, Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · intro h q hq
      rcases Finset.mem_union.mp hq with hq | hq
      · have hleft : postLastExitPositiveRationalEvals p q ∈ S q := h.1 q hq
        have hright : postLastExitPositiveRationalEvals p q ∈
            (if q ∈ J then T q else Set.univ) := by
          by_cases hj : q ∈ J
          · simpa [hj] using h.2 q hj
          · simp [hj]
        exact ⟨by simpa [hq] using hleft, hright⟩
      · have hleft : postLastExitPositiveRationalEvals p q ∈
            (if q ∈ I then S q else Set.univ) := by
          by_cases hi : q ∈ I
          · simpa [hi] using h.1 q hi
          · simp [hi]
        have hright : postLastExitPositiveRationalEvals p q ∈ T q := h.2 q hq
        exact ⟨hleft, by simpa [hq] using hright⟩
    · intro h
      constructor
      · intro q hq
        have hq' := h q (Finset.mem_union.mpr (Or.inl hq))
        simpa [U, hq] using hq'.1
      · intro q hq
        have hq' := h q (Finset.mem_union.mpr (Or.inr hq))
        simpa [U, hq] using hq'.2

/-- Rational evaluations on positive times generate the Borel sigma algebra of continuous path
space. Every real evaluation is a pointwise limit of evaluations at rational times from above. -/
private theorem postLastExitRationalEvalRectangles_generate_measurableSpace :
    (inferInstance : MeasurableSpace BrownianPath) =
      MeasurableSpace.generateFrom postLastExitRationalEvalRectangles := by
  let mRat := MeasurableSpace.generateFrom postLastExitRationalEvalRectangles
  have hcoord (q : {q : ℚ // 0 < (q : ℝ)}) : Measurable[mRat]
      (fun p : BrownianPath => postLastExitPositiveRationalEvals p q) := by
    intro s hs
    let S : {q : ℚ // 0 < (q : ℝ)} → Set ℝ := fun r =>
      if r = q then s else Set.univ
    have hS : ∀ r, MeasurableSet (S r) := by
      intro r
      by_cases hr : r = q
      · simp [S, hr, hs]
      · simp [S, hr]
    have hrect : postLastExitRationalEvalRect {q} S =
        {p | postLastExitPositiveRationalEvals p q ∈ s} := by
      ext p
      simp [postLastExitRationalEvalRect, S]
    have hbasic : postLastExitRationalEvalRect {q} S ∈
        postLastExitRationalEvalRectangles := ⟨{q}, S, hS, rfl⟩
    change MeasurableSet {p | postLastExitPositiveRationalEvals p q ∈ s}
    rw [← hrect]
    exact MeasurableSpace.measurableSet_generateFrom hbasic
  have hEval (t : ℝ≥0) : Measurable[mRat] (fun p : BrownianPath => p t) := by
    let qfun : ℕ → ℚ := (Real.exists_seq_rat_strictAnti_tendsto (t : ℝ)).choose
    have hqfun : StrictAnti qfun ∧ (∀ n, (t : ℝ) < (qfun n : ℝ)) ∧
        Tendsto (fun n => (qfun n : ℝ)) atTop (𝓝 (t : ℝ)) :=
      (Real.exists_seq_rat_strictAnti_tendsto (t : ℝ)).choose_spec
    have hzeroLe : (0 : ℝ) ≤ (t : ℝ) := by exact_mod_cast t.property
    let rfun : ℕ → ℝ≥0 := fun n => ⟨(qfun n : ℝ),
      (lt_of_le_of_lt hzeroLe (hqfun.2.1 n)).le⟩
    have hrfunReal : Tendsto (fun n => (rfun n : ℝ)) atTop (𝓝 (t : ℝ)) := hqfun.2.2
    have hrfun : Tendsto rfun atTop (𝓝 t) := NNReal.tendsto_coe.mp hrfunReal
    let rfunQ : ℕ → {q : ℚ // 0 < (q : ℝ)} := fun n =>
      ⟨qfun n, lt_of_le_of_lt hzeroLe (hqfun.2.1 n)⟩
    have happrox : ∀ n, Measurable[mRat] (fun p : BrownianPath => p (rfun n)) := by
      intro n
      have hcoord' := hcoord (rfunQ n)
      have heq : (fun p : BrownianPath => p (rfun n)) =
          fun p => -postLastExitPositiveRationalEvals p (rfunQ n) := by
        funext p
        simp [postLastExitPositiveRationalEvals, rfun, rfunQ]
      rw [heq]
      exact hcoord'.neg
    have hlimit : ∀ p : BrownianPath,
        Tendsto (fun n => p (rfun n)) atTop (𝓝 (p t)) := by
      intro p
      exact p.continuous.continuousAt.tendsto.comp hrfun
    have hlimitFun : Tendsto
        (fun n => fun p : BrownianPath => p (rfun n))
        atTop (𝓝 fun p : BrownianPath => p t) := tendsto_pi_nhds.mpr hlimit
    exact measurable_of_tendsto_metrizable happrox hlimitFun
  have hfull_le : ContinuousMap.measurableSpace ≤ mRat := by
    rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval]
    exact iSup_le fun t => (hEval t).comap_le
  have hRat_le : mRat ≤ ContinuousMap.measurableSpace := by
    apply MeasurableSpace.generateFrom_le
    intro A hA
    rcases hA with ⟨I, S, hS, rfl⟩
    change MeasurableSet[ContinuousMap.measurableSpace] (postLastExitRationalEvalRect I S)
    have hset : {p | ∀ q ∈ I, postLastExitPositiveRationalEvals p q ∈ S q} =
        ⋂ q, ⋂ (_ : q ∈ I), {p | postLastExitPositiveRationalEvals p q ∈ S q} := by
      ext p
      simp
    change MeasurableSet[ContinuousMap.measurableSpace]
      {p | ∀ q ∈ I, postLastExitPositiveRationalEvals p q ∈ S q}
    rw [hset]
    apply MeasurableSet.iInter
    intro q
    apply MeasurableSet.iInter
    intro hq
    exact (hS q).preimage
      ((measurable_pi_apply q).comp measurable_postLastExitPositiveRationalEvals)
  exact le_antisymm hfull_le hRat_le

private theorem postLastExitRationalEvalRect_measure_eq
    {ν c : ℝ} {P : Measure BrownianPath}
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (hν : 0 < ν) (hc : 0 < c)
    (I : Finset {q : ℚ // 0 < (q : ℝ)}) (hI : I.Nonempty)
    (S : {q : ℚ // 0 < (q : ℝ)} → Set ℝ) (hS : ∀ q, MeasurableSet (S q)) :
    (P.map (negativeConditionedPostLastExitPath c))
        (postLastExitRationalEvalRect I S) = P (postLastExitRationalEvalRect I S) := by
  classical
  let n := I.card
  have hn : 0 < n := Finset.card_pos.mpr hI
  let e : Fin n ≃o I := I.orderIsoOfFin rfl
  let qidx : Fin n → {q : ℚ // 0 < (q : ℝ)} := fun i => (e i).val
  let offsets : Fin n → ℚ := fun i => (qidx i).val
  have hoff : ∀ i, 0 < (offsets i : ℝ) := fun i => (qidx i).property
  have hmono : StrictMono offsets := by
    intro i j hij
    exact_mod_cast e.strictMono hij
  let fpost : BrownianPath → Fin n → ℝ := fun p i =>
    -(negativeConditionedPostLastExitPath c p
      (Real.toNNReal (offsets i : ℝ)))
  let forig : BrownianPath → Fin n → ℝ := fun p i =>
    -(p (Real.toNNReal (offsets i : ℝ)))
  let rpost : BrownianPath → Fin n → ℝ := fun p i =>
    postLastExitPositiveRationalEvals
      (negativeConditionedPostLastExitPath c p) (qidx i)
  let rorig : BrownianPath → Fin n → ℝ := fun p i =>
    postLastExitPositiveRationalEvals p (qidx i)
  have hB := wienerPathMeasure_isBrownian
  let : IsProbabilityMeasure wienerPathMeasure := isProbabilityMeasure_wienerPathMeasure
  let : IsFiniteMeasure wienerPathMeasure := ⟨by
    rw [measure_univ]
    exact ENNReal.one_lt_top⟩
  let : SFinite wienerPathMeasure := by
    refine ⟨fun k => if k = 0 then wienerPathMeasure else 0, ?_, ?_⟩
    · intro k
      change IsFiniteMeasure (if k = 0 then wienerPathMeasure else 0)
      by_cases hk : k = 0
      · rw [ite_eq_left hk]
        exact ‹IsFiniteMeasure wienerPathMeasure›
      · rw [ite_eq_right hk]
        infer_instance
    · ext s hs
      rw [Measure.sum_apply _ hs, tsum_eq_single 0 (by
        intro k hk
        simp [hk])]
      simp
  have hpost := negativeConditionedPostLastExit_positiveRationalProjection
    hP hB hP hν hc n offsets hoff hmono
  have horig := negativeConditionedLaw_positiveRationalProjection
    hP hν hn offsets hoff hmono
  have htime (i : Fin n) :
      Real.toNNReal (offsets i : ℝ) =
        (⟨((qidx i).val : ℚ), (qidx i).property.le⟩ : ℝ≥0) := by
    apply Subtype.ext
    simp [offsets, Real.coe_toNNReal _ (hoff i).le]
  have hfunpost : fpost = rpost := by
    funext p i
    dsimp [fpost, rpost, postLastExitPositiveRationalEvals]
    exact congrArg (fun t : ℝ≥0 => -(negativeConditionedPostLastExitPath c p t))
      (htime i)
  have hfunorig : forig = rorig := by
    funext p i
    dsimp [forig, rorig, postLastExitPositiveRationalEvals]
    exact congrArg (fun t : ℝ≥0 => -(p t)) (htime i)
  have hpost' : P.map rpost =
      volume.withDensity (brownianEntranceFinitePDF ν n
        (brownianFirstHitElapsed n (fun i => Real.toNNReal (offsets i)))) := by
    rw [← hfunpost]
    exact hpost
  have horig' : P.map rorig =
      volume.withDensity (brownianEntranceFinitePDF ν n
        (brownianFirstHitElapsed n (fun i => Real.toNNReal (offsets i)))) := by
    rw [← hfunorig]
    exact horig
  have hproj : P.map rpost = P.map rorig := hpost'.trans horig'.symm
  let A : Set (Fin n → ℝ) := {x | ∀ i, x i ∈ S (qidx i)}
  have hA : MeasurableSet A := by
    change MeasurableSet {x : Fin n → ℝ | ∀ i, x i ∈ S (qidx i)}
    rw [show {x : Fin n → ℝ | ∀ i, x i ∈ S (qidx i)} =
        ⋂ i, {x : Fin n → ℝ | x i ∈ S (qidx i)} by ext x; simp]
    exact MeasurableSet.iInter fun i =>
      (hS (qidx i)).preimage (measurable_pi_apply i)
  have hrpost : Measurable rpost := by
    apply measurable_pi_iff.mpr
    intro i
    exact ((ContinuousMap.measurable_eval _).comp
      (measurable_negativeConditionedPostLastExitPath c)).neg
  have hrorig : Measurable rorig := by
    apply measurable_pi_iff.mpr
    intro i
    exact (ContinuousMap.measurable_eval _).neg
  have hprepost : rpost ⁻¹' A =
      (negativeConditionedPostLastExitPath c) ⁻¹' postLastExitRationalEvalRect I S := by
    ext p
    simp only [Set.mem_preimage, A, rpost, postLastExitRationalEvalRect,
      Set.mem_ofPred_eq]
    constructor
    · intro hp q hq
      let i : Fin n := e.symm ⟨q, hq⟩
      have hqi : qidx i = q := congrArg Subtype.val (e.apply_symm_apply ⟨q, hq⟩)
      simpa [hqi] using hp i
    · intro hp i
      exact hp (qidx i) (e i).property
  have hpreorig : rorig ⁻¹' A = postLastExitRationalEvalRect I S := by
    ext p
    simp only [Set.mem_preimage, A, rorig, postLastExitRationalEvalRect,
      Set.mem_ofPred_eq]
    constructor
    · intro hp q hq
      let i : Fin n := e.symm ⟨q, hq⟩
      have hqi : qidx i = q := congrArg Subtype.val (e.apply_symm_apply ⟨q, hq⟩)
      simpa [hqi] using hp i
    · intro hp i
      exact hp (qidx i) (e i).property
  have hRect : MeasurableSet (postLastExitRationalEvalRect I S) := by
    change MeasurableSet[ContinuousMap.measurableSpace]
      {p | ∀ q ∈ I, postLastExitPositiveRationalEvals p q ∈ S q}
    have hset : {p | ∀ q ∈ I, postLastExitPositiveRationalEvals p q ∈ S q} =
        ⋂ q, ⋂ (_ : q ∈ I), {p | postLastExitPositiveRationalEvals p q ∈ S q} := by
      ext p
      simp
    rw [hset]
    apply MeasurableSet.iInter
    intro q
    apply MeasurableSet.iInter
    intro hq
    let t : ℝ≥0 := ⟨(q.val : ℝ), q.property.le⟩
    exact (hS q).preimage
      ((ContinuousMap.measurable_eval t).neg)
  calc
    (P.map (negativeConditionedPostLastExitPath c))
        (postLastExitRationalEvalRect I S) = P
          ((negativeConditionedPostLastExitPath c) ⁻¹' postLastExitRationalEvalRect I S) :=
            Measure.map_apply (measurable_negativeConditionedPostLastExitPath c) hRect
    _ = P (rpost ⁻¹' A) := by rw [← hprepost]
    _ = (P.map rpost) A := (Measure.map_apply hrpost hA).symm
    _ = (P.map rorig) A := by rw [hproj]
    _ = P (postLastExitRationalEvalRect I S) := by
          rw [Measure.map_apply hrorig hA, hpreorig]

/-- The post-last-exit recentering preserves the full conditioned path law. This proves
`DOZZ.negativeConditioned_postLastExit_law` by equality on positive rational evaluation
rectangles. -/
theorem negativeConditioned_postLastExit_law
    (ν c : ℝ) (hν : 0 < ν) (hc : 0 < c)
    (P : Measure BrownianPath) (hP : IsNegativeConditionedBrownianLaw ν P) :
    AEMeasurable (negativeConditionedPostLastExitPath c) P ∧
      P.map (negativeConditionedPostLastExitPath c) = P := by
  classical
  have hmap : AEMeasurable (negativeConditionedPostLastExitPath c) P :=
    aemeasurable_negativeConditionedPostLastExitPath c P
  refine ⟨hmap, ?_⟩
  let : IsProbabilityMeasure (P.map (negativeConditionedPostLastExitPath c)) :=
    (Measure.isProbabilityMeasure_map_iff hmap).mpr hP.2.1
  let : IsProbabilityMeasure P := hP.2.1
  have hrect : ∀ A ∈ postLastExitRationalEvalRectangles,
      (P.map (negativeConditionedPostLastExitPath c)) A = P A := by
    intro A hA
    rcases hA with ⟨I, S, hS, rfl⟩
    by_cases hI : I = ∅
    · simp [postLastExitRationalEvalRect, hI]
    · exact postLastExitRationalEvalRect_measure_eq hP hν hc I
        (Finset.nonempty_iff_ne_empty.mpr hI) S hS
  have hgen := postLastExitRationalEvalRectangles_generate_measurableSpace
  have hpi := postLastExitRationalEvalRectangles_piSystem
  have huniv :
      (P.map (negativeConditionedPostLastExitPath c)) Set.univ = P Set.univ := by
    simp
  refine MeasureTheory.ext_of_generate_finite postLastExitRationalEvalRectangles
    hgen hpi hrect huniv

end DOZZ.Proofs

end

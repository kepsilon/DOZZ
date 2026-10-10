/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitConditionalAvoidance
public import DOZZ.Brownian.LastExitStateNoAtoms

/-!
# Full deterministic-time avoidance identity

The shifted-kernel identity is first applied above the barrier. Below the barrier, continuity
makes strict future avoidance impossible. Atomlessness of the deterministic entrance state removes
the endpoint equality case, yielding the full a.e. conditional identity.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

private theorem conditionedPositiveFutureAvoidance_implies_state_ge
    (t c : ℝ≥0) (p : BrownianPath)
    (hp : p ∈ conditionedPositiveFutureRationalAvoidance t c) :
    (c : ℝ) ≤ conditionedPositiveStateAt t p := by
  by_contra hnot
  have hxc : conditionedPositiveStateAt t p < (c : ℝ) := lt_of_not_ge hnot
  let F : ℝ → ℝ := fun s => conditionedPositiveFuturePath t p
    ⟨max s 0, le_max_right s 0⟩
  have htime : Continuous (fun s : ℝ =>
      (⟨max s 0, le_max_right s 0⟩ : ℝ≥0)) := by
    exact (continuous_max.comp (continuous_id.prodMk continuous_const)).subtype_mk
      (fun s => le_max_right s 0)
  have hF : Continuous F := (conditionedPositiveFuturePath t p).continuous.comp htime
  have hFzero : F 0 = conditionedPositiveStateAt t p := by
    have hs0 : (⟨max (0 : ℝ) 0, le_max_right 0 0⟩ : ℝ≥0) = 0 := by
      apply Subtype.ext
      simp
    change -(p (t + ⟨max (0 : ℝ) 0, le_max_right 0 0⟩)) = -(p t)
    rw [hs0]
    exact congrArg (fun s : ℝ≥0 => -(p s)) (add_zero t)
  have hopen : IsOpen (F ⁻¹' Set.Iio (c : ℝ)) := isOpen_Iio.preimage hF
  have hmem : (0 : ℝ) ∈ F ⁻¹' Set.Iio (c : ℝ) := by
    rw [Set.mem_preimage, hFzero]
    exact hxc
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hmem)
  obtain ⟨q, hq0, hqδ⟩ := exists_rat_btwn (show (0 : ℝ) < δ by positivity)
  have hdist : dist (q : ℝ) 0 < δ := by
    change ‖(q : ℝ) - 0‖ < δ
    rw [sub_zero, Real.norm_eq_abs, abs_of_pos hq0]
    exact hqδ
  have hFq : F (q : ℝ) < (c : ℝ) :=
    hball (Metric.mem_ball.mpr hdist)
  have heval : conditionedPositiveFutureRationalEvals t p q = F (q : ℝ) := by
    simp [F, conditionedPositiveFutureRationalEvals,
      conditionedPositiveFuturePath, max_eq_left hq0.le]
  have hpall : ∀ r : ℚ, 0 < (r : ℝ) → (c : ℝ) <
      conditionedPositiveFutureRationalEvals t p r := by
    intro r hr
    have hrp := (Set.mem_iInter.mp hp) r
    simpa [conditionedPositiveFutureAvoidanceCoordinate, hr] using hrp
  have hpq := hpall q hq0
  rw [heval] at hpq
  exact (not_lt_of_ge (le_of_lt hFq)) hpq

/-- On paths whose state is below `c`, the conditional expectation of strict future avoidance
with any shifted rational-future event is zero. The support statement follows from continuity at
the deterministic time and the density of positive rationals immediately to its right. -/
theorem conditionedPositiveHistory_condExp_rationalFuture_avoidance_shift_on_below
    {P : Measure BrownianPath} [IsFiniteMeasure P]
    (t : ℝ≥0)
    (c : ℝ≥0) (C : Set (ℚ → ℝ)) (hC : MeasurableSet C) :
    ∀ᵐ p ∂P, conditionedPositiveStateAt t p < (c : ℝ) →
      P[(conditionedPositiveFutureRationalAvoidance t c).indicator
        (fun p => lastExitShiftedFutureTest (c : ℝ) C
          (conditionedPositiveFutureRationalEvals t p)) |
        conditionedPositiveNaturalFiltration t] p = 0 := by
  classical
  let eval : BrownianPath → (ℚ → ℝ) := conditionedPositiveFutureRationalEvals t
  let shift := lastExitRationalShift (c : ℝ)
  let test : (ℚ → ℝ) → ℝ := lastExitShiftedFutureTest (c : ℝ) C
  let shiftedEval : BrownianPath → (ℚ → ℝ) := fun p => shift (eval p)
  let avoid : Set BrownianPath := conditionedPositiveFutureRationalAvoidance t c
  let E : Set BrownianPath := {p | (c : ℝ) ≤ conditionedPositiveStateAt t p}
  let f : BrownianPath → ℝ := fun p => avoid.indicator
    (fun p => test (eval p)) p
  let g : BrownianPath → ℝ := E.indicator (fun _ => 1)
  have hshift : Measurable shift := by
    apply measurable_pi_iff.mpr
    intro r
    exact (measurable_pi_apply r).sub measurable_const
  have heval : Measurable eval := measurable_conditionedPositiveFutureRationalEvals t
  have hpath : MeasurableSet (shiftedEval ⁻¹' C) := hC.preimage (hshift.comp heval)
  have havoid : MeasurableSet avoid := by
    change MeasurableSet (⋂ q : ℚ,
      conditionedPositiveFutureAvoidanceCoordinate t c q)
    apply MeasurableSet.iInter
    intro q
    by_cases hq : 0 < (q : ℝ)
    · simp only [conditionedPositiveFutureAvoidanceCoordinate, hq]
      exact measurableSet_lt measurable_const
        ((measurable_pi_apply q).comp heval)
    · simp [conditionedPositiveFutureAvoidanceCoordinate, hq]
  have hA : MeasurableSet (avoid ∩ shiftedEval ⁻¹' C) := havoid.inter hpath
  have hf_eq : f = (avoid ∩ shiftedEval ⁻¹' C).indicator (fun _ => (1 : ℝ)) := by
    funext p
    by_cases hp : p ∈ avoid
    · by_cases hq : shiftedEval p ∈ C
      · simp [f, test, lastExitShiftedFutureTest, avoid, hp, hq,
          shiftedEval, shift, eval]
      · simp [f, test, lastExitShiftedFutureTest, avoid, hp, hq,
          shiftedEval, shift, eval]
    · simp [f, avoid, hp]
  have hfInt : Integrable f P := by
    rw [hf_eq]
    exact (integrable_const (1 : ℝ)).indicator hA
  have hEmeas : MeasurableSet E :=
    measurableSet_le measurable_const
      ((measurable_conditionedPositiveStateAt t).comp measurable_id)
  have hgInt : Integrable g P := by
    exact (integrable_const (1 : ℝ)).indicator hEmeas
  have hstateFil : Measurable[conditionedPositiveNaturalFiltration t]
      (conditionedPositiveStateAt t) := by
    apply Measurable.of_comap_le
    change MeasurableSpace.comap (conditionedPositiveProcessValue t) inferInstance ≤
      conditionedPositiveNaturalFiltration t
    exact le_iSup_of_le t (le_iSup_of_le le_rfl le_rfl)
  have hEfil : MeasurableSet[conditionedPositiveNaturalFiltration t] E :=
    measurableSet_le measurable_const hstateFil
  have hgFil : StronglyMeasurable[conditionedPositiveNaturalFiltration t] g := by
    exact (measurable_const.indicator hEfil).stronglyMeasurable
  have hfg : f ≤ᵐ[P] g := by
    apply Filter.Eventually.of_forall
    intro p
    by_cases hp : p ∈ avoid
    · have hpE : p ∈ E := by
        exact conditionedPositiveFutureAvoidance_implies_state_ge t c p hp
      change avoid.indicator (fun q => test (eval q)) p ≤
        E.indicator (fun _ => (1 : ℝ)) p
      by_cases hq : shiftedEval p ∈ C
      · have htest : test (eval p) = 1 := by
          simp [test, lastExitShiftedFutureTest, shiftedEval, shift, eval, hq]
        rw [Set.indicator_of_mem hp, Set.indicator_of_mem hpE, htest]
      · have htest : test (eval p) = 0 := by
          simp [test, lastExitShiftedFutureTest, shiftedEval, shift, eval, hq]
        rw [Set.indicator_of_mem hp, Set.indicator_of_mem hpE, htest]
        norm_num
    · by_cases hpE : p ∈ E
      · simp [f, g, avoid, E, hp, hpE]
      · simp [f, g, avoid, E, hp, hpE]
  have hcondMono := condExp_mono (m := conditionedPositiveNaturalFiltration t)
    hfInt hgInt hfg
  have hfilLe : conditionedPositiveNaturalFiltration t ≤ ContinuousMap.measurableSpace := by
    refine iSup_le fun s => iSup_le fun _ => ?_
    exact (measurable_conditionedPositiveProcessValue s).comap_le
  have hgCE := condExp_of_stronglyMeasurable (μ := P) hfilLe hgFil hgInt
  have hgCEae : P[g | conditionedPositiveNaturalFiltration t] =ᵐ[P] g := by
    filter_upwards [] with p
    exact congrFun hgCE p
  have hcondLe : P[f | conditionedPositiveNaturalFiltration t] ≤ᵐ[P] g := by
    exact hcondMono.trans_eq hgCEae
  have hfNonneg : 0 ≤ᵐ[P] f := by
    apply Filter.Eventually.of_forall
    intro p
    by_cases hp : p ∈ avoid
    · have htest0 : 0 ≤ test (eval p) := by
        by_cases hq : shiftedEval p ∈ C
        · simp [test, lastExitShiftedFutureTest, shiftedEval, shift, eval, hq]
        · simp [test, lastExitShiftedFutureTest, shiftedEval, shift, eval, hq]
      change 0 ≤ avoid.indicator (fun q => test (eval q)) p
      rw [Set.indicator_of_mem hp]
      exact htest0
    · change 0 ≤ avoid.indicator (fun q => test (eval q)) p
      simp [Set.indicator_of_notMem hp]
  have hcondNonneg := condExp_nonneg (m := conditionedPositiveNaturalFiltration t)
    hfNonneg
  filter_upwards [hcondLe, hcondNonneg] with p hle hnonneg
  intro hbelow
  have hpE : p ∉ E := by
    simp [E, not_le.mpr hbelow]
  have hg0 : g p = 0 := by simp [g, E, hpE]
  have hle0 : P[f | conditionedPositiveNaturalFiltration t] p ≤ 0 := by
    simpa [hg0] using hle
  exact le_antisymm hle0 hnonneg

/-- Full a.e. deterministic-time avoidance identity for arbitrary measurable events of the
recentered rational future. The endpoint equality branch is null because the one-time entrance
density is atomless. -/
theorem conditionedPositiveHistory_condExp_rationalFuture_avoidance_shift
    {ν : ℝ} {P : Measure BrownianPath} [IsFiniteMeasure P]
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (B : Measure BrownianPath) [SFinite B]
    (hB : IsBrownianReal (fun t p => p t) B)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (hν : 0 < ν)
    (c : ℝ≥0) (hc : 0 < (c : ℝ))
    (C : Set (ℚ → ℝ)) (hC : MeasurableSet C) :
    ∀ᵐ p ∂P,
      P[(conditionedPositiveFutureRationalAvoidance t c).indicator
        (fun p => lastExitShiftedFutureTest (c : ℝ) C
          (conditionedPositiveFutureRationalEvals t p)) |
        conditionedPositiveNaturalFiltration t] p =
        lastExitAvoidanceFactor ν (c : ℝ) (conditionedPositiveStateAt t p) *
          (brownianUpperConditionedReferenceFutureKernel B ν hν
            (conditionedPositiveStateAt t p - c)).real C := by
  have hneq := ae_conditionedPositiveStateAt_ne hP t ht (c : ℝ)
  have habove := conditionedPositiveHistory_condExp_rationalFuture_avoidance_shift_on_above
    hP B hB t ht hν c hc C hC
  have hbelow := conditionedPositiveHistory_condExp_rationalFuture_avoidance_shift_on_below
    (P := P) t c C hC
  filter_upwards [hneq, habove, hbelow] with p hpneq hpabove hpbelow
  by_cases hcx : (c : ℝ) < conditionedPositiveStateAt t p
  · exact hpabove hcx
  · have hle : conditionedPositiveStateAt t p ≤ (c : ℝ) := le_of_not_gt hcx
    have hlt : conditionedPositiveStateAt t p < (c : ℝ) := lt_of_le_of_ne hle hpneq
    rw [hpbelow hlt]
    simp [lastExitAvoidanceFactor, hcx]

/-- The conditional probability of avoiding the level after a deterministic time is exactly the
Doob harmonic ratio from the current state. This is the empty-test case of the full rational-future
identity. -/
theorem conditionedPositiveHistory_condExp_rationalFuture_avoidance_probability
    {ν : ℝ} {P : Measure BrownianPath} [IsFiniteMeasure P]
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (B : Measure BrownianPath) [SFinite B]
    (hB : IsBrownianReal (fun t p => p t) B)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (hν : 0 < ν)
    (c : ℝ≥0) (hc : 0 < (c : ℝ)) :
    ∀ᵐ p ∂P,
      P[(conditionedPositiveFutureRationalAvoidance t c).indicator
        (fun _ => (1 : ℝ)) | conditionedPositiveNaturalFiltration t] p =
        lastExitAvoidanceFactor ν (c : ℝ) (conditionedPositiveStateAt t p) := by
  have hshift := conditionedPositiveHistory_condExp_rationalFuture_avoidance_shift
    hP B hB t ht hν c hc Set.univ MeasurableSet.univ
  have hmass (x : ℝ) :
      lastExitAvoidanceFactor ν (c : ℝ) x *
        (brownianUpperConditionedReferenceFutureKernel B ν hν (x - c)).real
          Set.univ = lastExitAvoidanceFactor ν (c : ℝ) x := by
    by_cases hcx : (c : ℝ) < x
    · have hx : 0 < x - (c : ℝ) := sub_pos.mpr hcx
      have : IsProbabilityMeasure
          (brownianBelowConditionedLaw B ν (x - (c : ℝ))) :=
        isProbabilityMeasure_brownianBelowConditionedLaw B hB ν (x - (c : ℝ)) hν hx
      have : IsProbabilityMeasure
          (brownianUpperConditionedReferenceFutureKernel B ν hν (x - (c : ℝ))) := by
        rw [brownianUpperConditionedReferenceFutureKernel_apply_conditioned
          B ν (x - (c : ℝ)) hν hx]
        infer_instance
      have hreal :
          (brownianUpperConditionedReferenceFutureKernel B ν hν
            (x - (c : ℝ))).real Set.univ = 1 := by
        rw [measureReal_def]
        simp
      rw [hreal, mul_one]
    · simp [lastExitAvoidanceFactor, hcx]
  filter_upwards [hshift] with p hp
  simpa [lastExitShiftedFutureTest, hmass] using hp

end DOZZ.Proofs

end

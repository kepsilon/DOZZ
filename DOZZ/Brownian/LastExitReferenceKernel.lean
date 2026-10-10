/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedFutureKernelMarkov
public import DOZZ.Brownian.LastExitBrownianReferenceShift
public import Mathlib.Probability.Kernel.Composition.ParallelComp
public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.Probability.Kernel.WithDensity

/-!
# Brownian reference kernel for the conditioned future

For a positive starting state, the Brownian path conditioned to stay below that state gives the
same positive Doob transition chain as the deterministic-time future of the entrance process.
This module packages the reference construction as a kernel, so finite-cylinder identities can
be transferred to the conditional future kernel.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Rational evaluations of the positive path obtained by reflecting a drifted Brownian path
below its starting state. Nonpositive coordinates are assigned the initial state. -/
def brownianUpperConditionedPositiveRationalEvals (x : ℝ) (q : BrownianPath) : ℚ → ℝ :=
  fun r => brownianUpperConditionedPositivePath x q
    ⟨max (r : ℝ) 0, le_max_right _ _⟩

theorem measurable_brownianUpperConditionedPositiveRationalEvals :
    Measurable (fun z : ℝ × BrownianPath =>
      brownianUpperConditionedPositiveRationalEvals z.1 z.2) := by
  apply measurable_pi_iff.mpr
  intro r
  change Measurable (fun z : ℝ × BrownianPath =>
    z.1 - z.2 ⟨max (r : ℝ) 0, le_max_right _ _⟩)
  exact measurable_fst.sub
    ((ContinuousMap.measurable_eval _).comp measurable_snd)

theorem measurable_conditionedH_ref (ν : ℝ) : Measurable (conditionedH ν) := by
  unfold conditionedH
  split_ifs <;> fun_prop

/-- The joint raw-path density defining the upper-conditioned Brownian reference law. -/
noncomputable def brownianUpperConditionedRawDensity (ν : ℝ) (x : ℝ)
    (q : BrownianPath) : ℝ≥0∞ :=
  if _hx : 0 < x then
    (ENNReal.ofReal (conditionedH ν x))⁻¹ *
      ({q : BrownianPath | ∀ s : ℝ≥0,
        driftedBrownianPath (-ν) q s < x}.indicator (fun _ => 1) q)
  else 0

private theorem conditionedH_pos_ref {ν x : ℝ} (hν : 0 < ν) (hx : 0 < x) :
    0 < conditionedH ν x := by
  rw [conditionedH, ite_eq_right hν.ne']
  apply sub_pos.mpr
  apply Real.exp_lt_one_iff.mpr
  nlinarith

theorem measurable_brownianUpperConditionedRawDensity (ν : ℝ) :
    Measurable (Function.uncurry (brownianUpperConditionedRawDensity ν)) := by
  let D : ℝ × BrownianPath → ℝ × BrownianPath := fun z =>
    (z.1, driftedBrownianPath (-ν) z.2)
  have hD : Measurable D := by
    exact measurable_fst.prodMk
      (continuous_driftedBrownianPath.measurable.comp
        ((measurable_const (a := -ν)).prodMk measurable_snd))
  have hsurv : MeasurableSet {z : ℝ × BrownianPath |
      ∀ s : ℝ≥0, driftedBrownianPath (-ν) z.2 s < z.1} := by
    let H : Set (ℝ × BrownianPath) := {z | ∃ s : ℝ≥0, z.1 ≤ z.2 s}
    have hh : MeasurableSet (D ⁻¹' H) := by
      exact measurableSet_brownianPath_joint_hit.preimage hD
    have heq : {z : ℝ × BrownianPath |
        ∀ s : ℝ≥0, driftedBrownianPath (-ν) z.2 s < z.1} =
        (D ⁻¹' H)ᶜ := by
      ext z
      simp [D, H, not_le]
    rw [heq]
    exact MeasurableSet.compl hh
  have hweight : Measurable (fun z : ℝ × BrownianPath =>
      if 0 < z.1 then (ENNReal.ofReal (conditionedH ν z.1))⁻¹ else 0) := by
    have hm : Measurable (fun z : ℝ × BrownianPath =>
        (ENNReal.ofReal (conditionedH ν z.1))⁻¹) :=
      (ENNReal.measurable_ofReal.comp
        ((measurable_conditionedH_ref ν).comp measurable_fst)).inv
    exact Measurable.ite (measurableSet_lt measurable_const measurable_fst) hm
      measurable_const
  let w : ℝ × BrownianPath → ℝ≥0∞ := fun z =>
    if 0 < z.1 then (ENNReal.ofReal (conditionedH ν z.1))⁻¹ else 0
  let S : Set (ℝ × BrownianPath) :=
    {z | ∀ s : ℝ≥0, driftedBrownianPath (-ν) z.2 s < z.1}
  have heq : Function.uncurry (brownianUpperConditionedRawDensity ν) =
      fun z => w z * S.indicator (fun _ => 1) z := by
    funext z
    change (if hx : 0 < z.1 then
      (ENNReal.ofReal (conditionedH ν z.1))⁻¹ *
        ({q : BrownianPath | ∀ s : ℝ≥0,
          driftedBrownianPath (-ν) q s < z.1}.indicator (fun _ => 1) z.2)
      else 0) = _
    by_cases hx : 0 < z.1
    · have hI : ({q : BrownianPath | ∀ s : ℝ≥0,
          driftedBrownianPath (-ν) q s < z.1}.indicator
            (fun _ => (1 : ℝ≥0∞)) z.2) =
          S.indicator (fun _ => (1 : ℝ≥0∞)) z := by
        by_cases hq : ∀ s : ℝ≥0, driftedBrownianPath (-ν) z.2 s < z.1
        · have hqPath : z.2 ∈ {q : BrownianPath | ∀ s : ℝ≥0,
              driftedBrownianPath (-ν) q s < z.1} := hq
          have hqPair : z ∈ S := by simpa [S] using hq
          simp [Set.indicator_of_mem hqPath, Set.indicator_of_mem hqPair]
        · have hqPath : z.2 ∉ {q : BrownianPath | ∀ s : ℝ≥0,
              driftedBrownianPath (-ν) q s < z.1} := fun h => hq h
          have hqPair : z ∉ S := by simpa [S] using hq
          simp [Set.indicator_of_notMem hqPath, Set.indicator_of_notMem hqPair]
      simp only [dite_eq_left hx]
      rw [hI]
      simp [w, S, hx]
    · simp [w, S, hx]
  rw [heq]
  exact hweight.mul (measurable_const.indicator hsurv)

/-- The raw Brownian path law conditioned below its positive upper state, before applying the
drift map. -/
noncomputable def brownianUpperConditionedRawKernel (B : Measure BrownianPath) [SFinite B]
    (ν : ℝ) (hν : 0 < ν) :
    Kernel ℝ BrownianPath := by
  have _ := hν
  exact (Kernel.const ℝ B).withDensity (brownianUpperConditionedRawDensity ν)

instance isSFiniteKernel_brownianUpperConditionedRawKernel
    (B : Measure BrownianPath) [SFinite B] (ν : ℝ) (hν : 0 < ν) :
    IsSFiniteKernel (brownianUpperConditionedRawKernel B ν hν) := by
  unfold brownianUpperConditionedRawKernel
  apply Kernel.IsSFiniteKernel.withDensity
  intro x q
  unfold brownianUpperConditionedRawDensity
  split_ifs with hx
  · have hH := conditionedH_pos_ref hν hx
    have hzero : ENNReal.ofReal (conditionedH ν x) ≠ 0 :=
      ne_of_gt (ENNReal.ofReal_pos.mpr hH)
    have hweight : (ENNReal.ofReal (conditionedH ν x))⁻¹ < ⊤ :=
      ENNReal.inv_lt_top.mpr (ENNReal.ofReal_pos.mpr hH)
    have hindicator : ({q : BrownianPath | ∀ s : ℝ≥0,
        driftedBrownianPath (-ν) q s < x}.indicator (fun _ => (1 : ℝ≥0∞)) q) ≤ 1 := by
      by_cases hq : q ∈ {q : BrownianPath | ∀ s : ℝ≥0,
          driftedBrownianPath (-ν) q s < x}
      · simp [Set.indicator_of_mem hq]
      · simp [Set.indicator_of_notMem hq]
    have hbound :
        (ENNReal.ofReal (conditionedH ν x))⁻¹ *
            ({q : BrownianPath | ∀ s : ℝ≥0,
              driftedBrownianPath (-ν) q s < x}.indicator
                (fun _ => (1 : ℝ≥0∞)) q) < ⊤ := by
      calc
        (ENNReal.ofReal (conditionedH ν x))⁻¹ *
          ({q : BrownianPath | ∀ s : ℝ≥0,
            driftedBrownianPath (-ν) q s < x}.indicator
              (fun _ => (1 : ℝ≥0∞)) q) ≤
          (ENNReal.ofReal (conditionedH ν x))⁻¹ * 1 := by
            gcongr
        _ = (ENNReal.ofReal (conditionedH ν x))⁻¹ := by simp
        _ < ⊤ := hweight
    exact ne_of_lt hbound
  · simp

/-- Keep the starting state alongside its raw Brownian sample. -/
noncomputable def brownianUpperConditionedRawPairKernel (B : Measure BrownianPath)
    [SFinite B] (ν : ℝ) (hν : 0 < ν) : Kernel ℝ (ℝ × BrownianPath) :=
    (Kernel.parallelComp (Kernel.id : Kernel ℝ ℝ)
      (brownianUpperConditionedRawKernel B ν hν)) ∘ₖ
    Kernel.deterministic (fun x : ℝ => (x, x)) (by fun_prop)

instance isSFiniteKernel_brownianUpperConditionedRawPairKernel
    (B : Measure BrownianPath) [SFinite B] (ν : ℝ) (hν : 0 < ν) :
    IsSFiniteKernel (brownianUpperConditionedRawPairKernel B ν hν) := by
  unfold brownianUpperConditionedRawPairKernel
  infer_instance

theorem brownianUpperConditionedRawPairKernel_apply
    (B : Measure BrownianPath) [SFinite B] (ν : ℝ) (hν : 0 < ν) (x : ℝ) :
    brownianUpperConditionedRawPairKernel B ν hν x =
      (Measure.dirac x).prod (brownianUpperConditionedRawKernel B ν hν x) := by
  rw [brownianUpperConditionedRawPairKernel,
    Kernel.comp_deterministic_eq_comap _ (by fun_prop)]
  simp [Kernel.comap_apply, Kernel.parallelComp_apply, Kernel.id_apply]

/-- Conditional future kernel obtained by the actual Brownian upper-conditioning construction. -/
theorem measurable_brownianUpperConditionedReferenceFutureMap (ν : ℝ) :
    Measurable (fun z : ℝ × BrownianPath =>
      brownianUpperConditionedPositiveRationalEvals z.1
        (driftedBrownianPath (-ν) z.2)) := by
  exact measurable_brownianUpperConditionedPositiveRationalEvals.comp
    (measurable_fst.prodMk
      (continuous_driftedBrownianPath.measurable.comp
        ((measurable_const (a := -ν)).prodMk measurable_snd)))

noncomputable def brownianUpperConditionedReferenceFutureKernel
    (B : Measure BrownianPath) [SFinite B] (ν : ℝ) (hν : 0 < ν) :
    Kernel ℝ (ℚ → ℝ) :=
  (Kernel.deterministic
    (fun z : ℝ × BrownianPath =>
      brownianUpperConditionedPositiveRationalEvals z.1
        (driftedBrownianPath (-ν) z.2))
    (measurable_brownianUpperConditionedReferenceFutureMap ν)) ∘ₖ
      brownianUpperConditionedRawPairKernel B ν hν

instance isSFiniteKernel_brownianUpperConditionedReferenceFutureKernel
    (B : Measure BrownianPath) [SFinite B] (ν : ℝ) (hν : 0 < ν) :
    IsSFiniteKernel (brownianUpperConditionedReferenceFutureKernel B ν hν) := by
  unfold brownianUpperConditionedReferenceFutureKernel
  infer_instance

theorem brownianUpperConditionedReferenceFutureKernel_apply
    (B : Measure BrownianPath) [SFinite B] (ν : ℝ) (hν : 0 < ν) (x : ℝ) :
    brownianUpperConditionedReferenceFutureKernel B ν hν x =
      (brownianUpperConditionedRawKernel B ν hν x).map
        (fun q => brownianUpperConditionedPositiveRationalEvals x
          (driftedBrownianPath (-ν) q)) := by
  rw [brownianUpperConditionedReferenceFutureKernel,
    Kernel.deterministic_comp_eq_map
      (measurable_brownianUpperConditionedReferenceFutureMap ν),
    Kernel.map_apply _
      (measurable_brownianUpperConditionedReferenceFutureMap ν)]
  rw [brownianUpperConditionedRawPairKernel_apply,
    Measure.dirac_prod]
  rw [Measure.map_map
    (measurable_brownianUpperConditionedReferenceFutureMap ν)
    measurable_prodMk_left]
  congr 1

theorem brownianUpperConditionedRawKernel_map_drifted
    (B : Measure BrownianPath) [SFinite B]
    (ν x : ℝ) (hν : 0 < ν) (hx : 0 < x) :
    (brownianUpperConditionedRawKernel B ν hν x).map
        (driftedBrownianPath (-ν)) = brownianBelowConditionedLaw B ν x := by
  let E : Set BrownianPath := {q | ∀ s : ℝ≥0, driftedBrownianPath (-ν) q s < x}
  have hE : MeasurableSet E := by
    have hmD : Measurable (driftedBrownianPath (-ν)) :=
      continuous_driftedBrownianPath.measurable.comp
        ((measurable_const (a := -ν)).prodMk measurable_id)
    exact (measurableSet_brownianPath_below x).preimage hmD
  have hden : brownianUpperConditionedRawDensity ν x =
      E.indicator (fun _ => (ENNReal.ofReal (conditionedH ν x))⁻¹) := by
    funext q
    by_cases hq : q ∈ E
    · simp [brownianUpperConditionedRawDensity, E, hx, hq]
    · simp [brownianUpperConditionedRawDensity, E, hx, hq]
  have hraw : brownianUpperConditionedRawKernel B ν hν x =
      (ENNReal.ofReal (conditionedH ν x))⁻¹ • B.restrict E := by
    rw [brownianUpperConditionedRawKernel,
      Kernel.withDensity_apply _ (measurable_brownianUpperConditionedRawDensity ν)]
    rw [hden, withDensity_indicator hE, withDensity_const]
    simp [Kernel.const_apply]
  have hmD : Measurable (driftedBrownianPath (-ν)) :=
    continuous_driftedBrownianPath.measurable.comp
      ((measurable_const (a := -ν)).prodMk measurable_id)
  rw [hraw, brownianBelowConditionedLaw, Measure.map_smul _ hmD.aemeasurable]

theorem brownianUpperConditionedReferenceFutureKernel_apply_conditioned
    (B : Measure BrownianPath) [SFinite B]
    (ν x : ℝ) (hν : 0 < ν) (hx : 0 < x) :
    brownianUpperConditionedReferenceFutureKernel B ν hν x =
    (brownianBelowConditionedLaw B ν x).map
        (fun q => brownianUpperConditionedPositiveRationalEvals x q) := by
  have hEval : Measurable (fun q : BrownianPath =>
      brownianUpperConditionedPositiveRationalEvals x q) :=
    measurable_brownianUpperConditionedPositiveRationalEvals.comp
      (measurable_const.prodMk measurable_id)
  have hD : Measurable (driftedBrownianPath (-ν)) :=
    continuous_driftedBrownianPath.measurable.comp
      ((measurable_const (a := -ν)).prodMk measurable_id)
  have hcomp : (fun q : BrownianPath =>
      brownianUpperConditionedPositiveRationalEvals x (driftedBrownianPath (-ν) q)) =
      (fun q => brownianUpperConditionedPositiveRationalEvals x q) ∘
        driftedBrownianPath (-ν) := rfl
  rw [brownianUpperConditionedReferenceFutureKernel_apply,
    hcomp, ← Measure.map_map hEval hD,
    brownianUpperConditionedRawKernel_map_drifted B ν x hν hx]

theorem isFiniteKernel_brownianUpperConditionedReferenceFutureKernel
    (B : Measure BrownianPath) [SFinite B]
    (hB : IsBrownianReal (fun t p => p t) B)
    (ν : ℝ) (hν : 0 < ν) :
    IsFiniteKernel (brownianUpperConditionedReferenceFutureKernel B ν hν) := by
  refine ⟨1, ENNReal.one_lt_top, fun x => ?_⟩
  by_cases hx : 0 < x
  · let : IsProbabilityMeasure (brownianBelowConditionedLaw B ν x) :=
      isProbabilityMeasure_brownianBelowConditionedLaw B hB ν x hν hx
    have hprob : IsProbabilityMeasure
        (brownianUpperConditionedReferenceFutureKernel B ν hν x) := by
      rw [brownianUpperConditionedReferenceFutureKernel_apply_conditioned B ν x hν hx]
      infer_instance
    rw [hprob.measure_univ]
  · have hraw : brownianUpperConditionedRawKernel B ν hν x = 0 := by
      unfold brownianUpperConditionedRawKernel
      ext s hs
      rw [Kernel.withDensity_apply _ (measurable_brownianUpperConditionedRawDensity ν)]
      have hdens : brownianUpperConditionedRawDensity ν x = 0 := by
        funext q
        simp [brownianUpperConditionedRawDensity, hx]
      rw [hdens]
      simp
    have hzero : brownianUpperConditionedReferenceFutureKernel B ν hν x = 0 := by
      rw [brownianUpperConditionedReferenceFutureKernel_apply, hraw]
      simp
    rw [hzero]
    simp

/-- Translating every absolute observation time and the initial clock by the same amount leaves
the positive Doob transition-chain density unchanged. -/
theorem conditionedPositiveTimeChainDensity_translate
    (ν d s : ℝ) {n : ℕ} (x : ℝ) (offsets values : Fin n → ℝ) :
    conditionedPositiveTimeChainDensity ν (d + s) x
        (List.ofFn fun i => d + offsets i) (List.ofFn values) =
      conditionedPositiveTimeChainDensity ν s x
        (List.ofFn offsets) (List.ofFn values) := by
  induction n generalizing s x with
  | zero => simp [conditionedPositiveTimeChainDensity]
  | succ n ih =>
      simp only [List.ofFn_succ, conditionedPositiveTimeChainDensity]
      rw [show (d + offsets 0) - (d + s) = offsets 0 - s by ring]
      have htail :
          conditionedPositiveTimeChainDensity ν (d + offsets 0) (values 0)
            (List.ofFn fun i : Fin n => (d + offsets 0) +
              (offsets i.succ - offsets 0))
            (List.ofFn fun i : Fin n => values i.succ) =
          conditionedPositiveTimeChainDensity ν (offsets 0) (values 0)
            (List.ofFn fun i : Fin n => offsets 0 +
              (offsets i.succ - offsets 0))
            (List.ofFn fun i : Fin n => values i.succ) := by
        simpa only [← add_assoc] using
          (ih (offsets 0) (values 0)
            (fun i => offsets 0 + (offsets i.succ - offsets 0))
            (fun i => values i.succ))
      have htimesL :
          (fun i : Fin n => (d + offsets 0) + (offsets i.succ - offsets 0)) =
            (fun i => d + offsets i.succ) := by
        funext i
        ring
      have htimesR :
          (fun i : Fin n => offsets 0 + (offsets i.succ - offsets 0)) =
            (fun i => offsets i.succ) := by
        funext i
        ring
      rw [htimesL, htimesR] at htail
      rw [htail]

private theorem conditionedPositiveTransitionDensity_nonneg_ref
    {ν t x : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (y : ℝ) :
    0 ≤ conditionedPositiveTransitionDensity ν t x y := by
  by_cases hx : 0 < x
  · exact conditionedPositiveTransitionDensity_nonneg hν ht hx y
  · simp [conditionedPositiveTransitionDensity, hν, ht, not_lt.mpr (le_of_not_gt hx)]

/-- The explicit finite Brownian Doob density is the real transition chain converted to an
`ENNReal` density on a cumulative elapsed schedule. -/
theorem brownianDoobFinitePDF_eq_chain_from_elapsed
    (ν t x : ℝ) (hν : 0 < ν) (n : ℕ) (ds : Fin n → ℝ≥0)
    (hds : ∀ i, 0 < ds i) (y : Fin n → ℝ) :
    ENNReal.ofReal (conditionedPositiveTimeChainDensity ν t x
      (List.ofFn fun i => t + (brownianFirstHitTimes n ds i : ℝ))
      (List.ofFn y)) = brownianDoobFinitePDF ν n ds x y := by
  induction n generalizing t x with
  | zero => simp [conditionedPositiveTimeChainDensity, brownianDoobFinitePDF]
  | succ n ih =>
      rw [List.ofFn_succ, List.ofFn_succ]
      simp only [brownianFirstHitTimes, Fin.cons_zero, Fin.cons_succ,
        NNReal.coe_add, conditionedPositiveTimeChainDensity, add_sub_cancel_left]
      have hstepTime : 0 < (ds 0 : ℝ) := by exact_mod_cast hds 0
      rw [ENNReal.ofReal_mul
        (conditionedPositiveTransitionDensity_nonneg_ref (ν := ν)
          (t := (ds 0 : ℝ)) (x := x) hν.le hstepTime (y 0))]
      change _ * ENNReal.ofReal (conditionedPositiveTimeChainDensity ν
        (t + (ds 0 : ℝ)) (y 0)
        (List.ofFn fun i => t + ((ds 0 : ℝ) +
          (brownianFirstHitTimes n (Fin.tail ds) i : ℝ)))
        (List.ofFn (Fin.tail y))) = _
      simp_rw [← add_assoc]
      rw [ih (t + (ds 0 : ℝ)) (y 0) (Fin.tail ds)
        (fun i => hds i.succ) (Fin.tail y)]
      rfl

/-- Every strictly ordered positive rational projection of the Brownian reference future has the
same finite Doob density as the deterministic-time conditioned future kernel. -/
theorem brownianUpperConditionedReferenceFutureKernel_finite_projection
    (B : Measure BrownianPath) [SFinite B]
    (hB : IsBrownianReal (fun t p => p t) B)
    (ν t x : ℝ) (hν : 0 < ν) (ht : 0 < t) (hx : 0 < x)
    (n : ℕ) (offsets : Fin n → ℚ)
    (hoff : ∀ i, 0 < (offsets i : ℝ)) (hmono : StrictMono offsets)
    (A : Set (Fin n → ℝ)) (hA : MeasurableSet A) :
    (brownianUpperConditionedReferenceFutureKernel B ν hν x).map
        (fun y i => y (offsets i)) A =
      ((Kernel.const ℝ (volume : Measure (Fin n → ℝ))).withDensity
        (fun z y => conditionedPositiveFutureVectorDensity ν
          (fun _ : Fin 1 => t) (fun i => t + (offsets i : ℝ))
          (fun _ => z) y)) x A := by
  have _ := ht
  let ts : Fin n → ℝ≥0 := fun i => Real.toNNReal (offsets i : ℝ)
  have hts0 : ∀ i, 0 < ts i := by
    intro i
    exact Real.toNNReal_pos.mpr (hoff i)
  have htsmono : StrictMono ts := by
    intro i j hij
    rw [← NNReal.coe_lt_coe,
      Real.coe_toNNReal _ (hoff i).le,
      Real.coe_toNNReal _ (hoff j).le]
    exact_mod_cast hmono hij
  let ds : Fin n → ℝ≥0 := brownianFirstHitElapsed n ts
  have hds : ∀ i, 0 < ds i := by
    intro i
    exact brownianFirstHitElapsed_pos n ts hts0 htsmono i
  have htimes : brownianFirstHitTimes n ds = ts := by
    cases n with
    | zero => funext i; exact Fin.elim0 i
    | succ m => exact brownianFirstHitTimes_elapsed m ts htsmono.monotone
  have hEval : Measurable (fun q : BrownianPath =>
      brownianUpperConditionedPositiveRationalEvals x q) := by
    exact measurable_brownianUpperConditionedPositiveRationalEvals.comp
      (measurable_const.prodMk measurable_id)
  have hproject : Measurable (fun y : ℚ → ℝ => fun i => y (offsets i)) := by
    exact measurable_pi_iff.mpr (fun i => measurable_pi_apply (offsets i))
  have htimesMap : (fun q : BrownianPath => fun i => x - q (ts i)) =
      (fun q => fun i => x - q (brownianFirstHitTimes n ds i)) := by
    funext q i
    rw [htimes]
  have hmap := brownianBelowConditionedLaw_finite_positive_density_map B hB ν x hν hx
    n ds hds
  have hcompose : (fun y : ℚ → ℝ => fun i => y (offsets i)) ∘
      (fun q : BrownianPath => brownianUpperConditionedPositiveRationalEvals x q) =
        (fun q i => x - q (ts i)) := by
    funext q i
    have htime :
        (⟨max (offsets i : ℝ) 0, le_max_right _ _⟩ : ℝ≥0) = ts i := by
      apply Subtype.ext
      simp [ts, max_eq_left (hoff i).le,
        Real.coe_toNNReal (offsets i : ℝ) (hoff i).le]
    simp [brownianUpperConditionedPositiveRationalEvals,
      brownianUpperConditionedPositivePath, htime]
  have href :
      ((brownianUpperConditionedReferenceFutureKernel B ν hν x).map
          (fun y i => y (offsets i))) =
        volume.withDensity (brownianDoobFinitePDF ν n ds x) := by
    rw [brownianUpperConditionedReferenceFutureKernel_apply_conditioned B ν x hν hx]
    rw [Measure.map_map hproject hEval]
    rw [hcompose]
    rw [htimesMap, hmap]
  have hdens : ∀ y : Fin n → ℝ,
      brownianDoobFinitePDF ν n ds x y =
        conditionedPositiveFutureVectorDensity ν
          (fun _ : Fin 1 => t) (fun i => t + (offsets i : ℝ))
          (fun _ => x) y := by
    intro y
    have hchain := brownianDoobFinitePDF_eq_chain_from_elapsed ν 0 x hν n ds hds y
    have htranslate := conditionedPositiveTimeChainDensity_translate ν t 0 x
      (fun i => (offsets i : ℝ)) y
    have htimesReal : (fun i : Fin n => (brownianFirstHitTimes n ds i : ℝ)) =
        fun i => (offsets i : ℝ) := by
      funext i
      have := congrFun htimes i
      simpa [ts, Real.coe_toNNReal (offsets i : ℝ) (hoff i).le] using
        congrArg (fun z : ℝ≥0 => (z : ℝ)) this
    have hleft : (List.ofFn fun i : Fin n => (0 : ℝ) +
        (brownianFirstHitTimes n ds i : ℝ)) =
        List.ofFn (fun i => (offsets i : ℝ)) := by
      congr 1
      funext i
      simpa using congrFun htimesReal i
    rw [hleft] at hchain
    have htargetNonneg : 0 ≤ conditionedPositiveTimeChainDensity ν t x
        (List.ofFn fun i : Fin n => t + (offsets i : ℝ)) (List.ofFn y) :=
      conditionedPositiveTimeChainDensity_nonneg hν.le _ _ (by simp)
    change brownianDoobFinitePDF ν n ds x y =
      ENNReal.ofReal (max 0 (conditionedPositiveTimeChainDensity ν t x
        (List.ofFn fun i : Fin n => t + (offsets i : ℝ)) (List.ofFn y)))
    have htimeList : (List.ofFn fun i : Fin n =>
        (brownianFirstHitTimes n ds i : ℝ)) = List.ofFn (fun i => (offsets i : ℝ)) := by
      apply congrArg List.ofFn
      exact htimesReal
    have htranslate' :
        conditionedPositiveTimeChainDensity ν t x
          (List.ofFn fun i : Fin n => t + (offsets i : ℝ)) (List.ofFn y) =
        conditionedPositiveTimeChainDensity ν 0 x
          (List.ofFn fun i : Fin n => (offsets i : ℝ)) (List.ofFn y) := by
      simpa using htranslate
    calc
      brownianDoobFinitePDF ν n ds x y =
        ENNReal.ofReal (conditionedPositiveTimeChainDensity ν 0 x
          (List.ofFn fun i : Fin n => (offsets i : ℝ)) (List.ofFn y)) := hchain.symm
      _ = ENNReal.ofReal (max 0 (conditionedPositiveTimeChainDensity ν t x
          (List.ofFn fun i : Fin n => t + (offsets i : ℝ)) (List.ofFn y))) := by
        rw [← htranslate']
        simp
  have hinput : Measurable (fun z : ℝ × (Fin n → ℝ) =>
      ((fun _ : Fin 1 => z.1), z.2)) := by
    apply Measurable.prodMk
    · exact measurable_pi_iff.mpr (fun _ => measurable_fst)
    · exact measurable_snd
  have hmeasDensity : Measurable (fun z : ℝ × (Fin n → ℝ) =>
      conditionedPositiveFutureVectorDensity ν
        (fun _ : Fin 1 => t) (fun i => t + (offsets i : ℝ))
        (fun _ => z.1) z.2) := by
    exact (measurable_conditionedPositiveFutureVectorDensity ν
      (fun _ : Fin 1 => t) (fun i => t + (offsets i : ℝ))).comp hinput
  have hmeasureEq : volume.withDensity (brownianDoobFinitePDF ν n ds x) =
      volume.withDensity (fun y => conditionedPositiveFutureVectorDensity ν
        (fun _ : Fin 1 => t) (fun i => t + (offsets i : ℝ)) (fun _ => x) y) := by
    congr 1
    funext y
    exact hdens y
  rw [href]
  rw [Kernel.withDensity_apply _ hmeasDensity x, Kernel.const_apply, hmeasureEq]

/-- The conditioned entrance state is strictly positive almost surely at every positive
deterministic time. -/
theorem conditionedPositiveStateAt_pos_ae
    {ν : ℝ} {P : Measure BrownianPath} (hP : IsNegativeConditionedBrownianLaw ν P)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) :
    ∀ᵐ p ∂P, 0 < conditionedPositiveStateAt t p := by
  let times : Fin 1 → ℝ≥0 := fun _ => t
  have htimes : ∀ i, 0 < (times i : ℝ) := fun _ => ht
  have hmono : StrictMono times := by
    intro i j hij
    fin_cases i
    fin_cases j
    exact False.elim (by simp at hij)
  have hfd := negativeConditionedLaw_positiveFDD hP 1 (by norm_num)
    times htimes hmono
  let f : (Fin 1 → ℝ) → ℝ≥0∞ := fun z => ENNReal.ofReal (max 0
    (conditionedPositiveFDDDensity ν [t] [z 0]))
  have hf : Measurable f := by
    exact measurable_conditionedPositiveFDDVectorDensity ν (fun _ => (t : ℝ))
  have hfd' : P.map (fun p : BrownianPath => fun _ : Fin 1 => -(p t)) =
      (volume : Measure (Fin 1 → ℝ)).withDensity f := by
    simpa [f, times] using hfd
  have heval : Measurable (fun z : Fin 1 → ℝ => z 0) := measurable_pi_apply 0
  have hvec : Measurable (fun p : BrownianPath => fun _ : Fin 1 => -(p t)) := by
    apply measurable_pi_iff.mpr
    intro i
    exact (ContinuousMap.measurable_eval t).neg
  have hmap : P.map (conditionedPositiveStateAt t) =
      ((volume : Measure (Fin 1 → ℝ)).withDensity f).map (fun z => z 0) := by
    calc
      P.map (conditionedPositiveStateAt t) =
          (P.map (fun p : BrownianPath => fun _ : Fin 1 => -(p t))).map
            (fun z => z 0) := by
          rw [Measure.map_map heval hvec]
          congr 1
      _ = _ := congrArg (fun μ : Measure (Fin 1 → ℝ) => μ.map (fun z => z 0)) hfd'
  have hnull : (P.map (conditionedPositiveStateAt t)) {x : ℝ | x ≤ 0} = 0 := by
    rw [hmap]
    calc
      (Measure.map (fun z : Fin 1 → ℝ => z 0)
          ((volume : Measure (Fin 1 → ℝ)).withDensity f)) {x : ℝ | x ≤ 0} =
        ((volume : Measure (Fin 1 → ℝ)).withDensity f)
          ((fun z : Fin 1 → ℝ => z 0) ⁻¹' {x : ℝ | x ≤ 0}) :=
        Measure.map_apply heval (measurableSet_le measurable_id measurable_const)
      _ = 0 := by
        have hpre : (fun z : Fin 1 → ℝ => z 0) ⁻¹' {x : ℝ | x ≤ 0} =
            {z : Fin 1 → ℝ | z 0 ≤ 0} := by ext z; rfl
        rw [hpre, withDensity_apply f
          (measurableSet_le (measurable_pi_apply 0) measurable_const)]
        apply setLIntegral_eq_zero
          (measurableSet_le (measurable_pi_apply 0) measurable_const)
        intro z hz
        simp [f, conditionedPositiveFDDDensity, conditionedPositiveEntranceDensity,
          hP.1, ht, not_lt.mpr hz]
  have hAE : ∀ᵐ x ∂P.map (conditionedPositiveStateAt t), 0 < x := by
    rw [ae_iff]
    simpa [not_lt] using hnull
  exact (ae_map_iff (μ := P) (f := conditionedPositiveStateAt t)
    (measurable_conditionedPositiveStateAt t).aemeasurable
    (p := fun x : ℝ => 0 < x)
    (measurableSet_lt measurable_const measurable_id)).1 hAE

/-- The joint endpoint/future law built from the abstract conditional kernel and from the actual
Brownian upper-conditioned reference kernel agree after every finite strictly ordered positive
rational projection. -/
theorem conditionedPositiveFutureKernel_reference_finite_compProd
    {ν : ℝ} {P : Measure BrownianPath} [IsFiniteMeasure P]
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (B : Measure BrownianPath) [SFinite B]
    (hB : IsBrownianReal (fun t p => p t) B)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (hν : 0 < ν)
    (n : ℕ) (offsets : Fin n → ℚ)
    (hoff : ∀ i, 0 < (offsets i : ℝ)) (hmono : StrictMono offsets)
    (hMonoEndpoint : StrictMono (Fin.append (fun _ : Fin 1 => t)
      (fun i => t + (offsets i : ℝ).toNNReal))) :
    let project : (ℚ → ℝ) → Fin n → ℝ := fun y i => y (offsets i)
    let pairProject : (ℝ × (ℚ → ℝ)) → (ℝ × (Fin n → ℝ)) :=
      fun z => (z.1, project z.2)
    (((P.map (conditionedPositiveStateAt t)) ⊗ₘ conditionedPositiveFutureKernel t P).map
      pairProject) =
    (((P.map (conditionedPositiveStateAt t)) ⊗ₘ
      brownianUpperConditionedReferenceFutureKernel B ν hν).map pairProject) := by
  classical
  let project : (ℚ → ℝ) → Fin n → ℝ := fun y i => y (offsets i)
  let pairProject : (ℝ × (ℚ → ℝ)) → (ℝ × (Fin n → ℝ)) :=
    fun z => (z.1, project z.2)
  let μx : Measure ℝ := P.map (conditionedPositiveStateAt t)
  let κA : Kernel ℝ (ℚ → ℝ) := conditionedPositiveFutureKernel t P
  let κR : Kernel ℝ (ℚ → ℝ) := brownianUpperConditionedReferenceFutureKernel B ν hν
  have : IsSFiniteKernel κA := by dsimp [κA]; infer_instance
  have : IsSFiniteKernel κR := by dsimp [κR]; infer_instance
  let κD : Kernel ℝ (Fin n → ℝ) :=
    (Kernel.const ℝ (volume : Measure (Fin n → ℝ))).withDensity
      (fun x y => conditionedPositiveFutureVectorDensity ν
        (fun _ : Fin 1 => (t : ℝ)) (fun i => (t : ℝ) + (offsets i : ℝ))
        (fun _ => x) y)
  have hproject : Measurable project := by
    exact measurable_pi_iff.mpr (fun i => measurable_pi_apply (offsets i))
  have hpairProject : Measurable pairProject :=
    measurable_fst.prodMk (hproject.comp measurable_snd)
  have hstatePos : ∀ᵐ x ∂μx, 0 < x :=
    (ae_map_iff (μ := P) (f := conditionedPositiveStateAt t)
      (measurable_conditionedPositiveStateAt t).aemeasurable
      (p := fun x : ℝ => 0 < x)
      (measurableSet_lt measurable_const measurable_id)).2
      (conditionedPositiveStateAt_pos_ae hP t ht)
  have hrect : ∀ D, MeasurableSet D → ∀ C, MeasurableSet C →
      (((μx ⊗ₘ κA).map pairProject) (D ×ˢ C)) =
        (((μx ⊗ₘ κR).map pairProject) (D ×ˢ C)) := by
    intro D hD C hC
    have hpre : pairProject ⁻¹' (D ×ˢ C) = D ×ˢ (project ⁻¹' C) := by
      ext z
      simp [pairProject]
    have hleft : ((μx ⊗ₘ κA).map pairProject) (D ×ˢ C) =
        ∫⁻ x in D, κA.map project x C ∂μx := by
      rw [Measure.map_apply hpairProject (MeasurableSet.prod hD hC), hpre,
        Measure.compProd_apply_prod hD (hC.preimage hproject)]
      apply setLIntegral_congr_fun hD
      intro x hx
      change κA x (project ⁻¹' C) = κA.map project x C
      rw [Kernel.map_apply' _ hproject x hC]
    have hright : ((μx ⊗ₘ κR).map pairProject) (D ×ˢ C) =
        ∫⁻ x in D, κR.map project x C ∂μx := by
      rw [Measure.map_apply hpairProject (MeasurableSet.prod hD hC), hpre,
        Measure.compProd_apply_prod hD (hC.preimage hproject)]
      apply setLIntegral_congr_fun hD
      intro x hx
      change κR x (project ⁻¹' C) = κR.map project x C
      rw [Kernel.map_apply' _ hproject x hC]
    have hActual := conditionedPositiveFutureKernel_finite_projection_eq_density
      (hP := hP) t ht n offsets hoff hMonoEndpoint C hC
    have hReference (x : ℝ) (hx : 0 < x) :
        κR.map project x C = κD x C := by
      calc
        κR.map project x C =
            Measure.map project (brownianUpperConditionedReferenceFutureKernel B ν hν x) C := by
              rw [Kernel.map_apply _ hproject x]
        _ = κD x C := by
          simpa [κD, project] using
            (brownianUpperConditionedReferenceFutureKernel_finite_projection
          B hB ν t x hν ht hx n offsets hoff hmono C hC)
    have hkernelAE : ∀ᵐ x ∂μx, κA.map project x C = κR.map project x C := by
      filter_upwards [hActual, hstatePos] with x hA hx
      rw [hA, hReference x hx]
    exact hleft.trans ((setLIntegral_congr_fun_ae hD
      (hkernelAE.mono fun _ h _ => h)).trans hright.symm)
  have hfinite : ((μx ⊗ₘ κA).map pairProject) Set.univ < ∞ := by
    exact measure_lt_top _ _
  have huniv : ((μx ⊗ₘ κA).map pairProject) Set.univ =
      ((μx ⊗ₘ κR).map pairProject) Set.univ := by
    simpa using hrect Set.univ MeasurableSet.univ Set.univ MeasurableSet.univ
  have heq := measure_eq_of_prod_rectangles
    ((μx ⊗ₘ κA).map pairProject) ((μx ⊗ₘ κR).map pairProject) hfinite hrect huniv
  simpa [μx, κA, κR, project, pairProject] using heq

theorem brownianBelowConditionedLaw_eval_zero_ae
    (B : Measure BrownianPath) [SFinite B]
    (hB : IsBrownianReal (fun t p => p t) B)
    (ν x : ℝ) (hν : 0 < ν) (hx : 0 < x) :
    ∀ᵐ q ∂brownianBelowConditionedLaw B ν x, q 0 = 0 := by
  let drift : BrownianPath → BrownianPath := driftedBrownianPath (-ν)
  let S : Set BrownianPath := {p | ∀ t : ℝ≥0, drift p t < x}
  have hdrift : Measurable drift :=
    continuous_driftedBrownianPath.measurable.comp
      ((measurable_const (a := -ν)).prodMk measurable_id)
  have hS : MeasurableSet S := by
    exact (measurableSet_brownianPath_below x).preimage hdrift
  have hzeroRestrict : ∀ᵐ p ∂B.restrict S, p 0 = 0 := by
    apply (ae_restrict_iff' hS).2
    filter_upwards [hB.eval_zero_ae_eq_zero] with p hp
    intro _
    exact hp
  have hzeroMap : ∀ᵐ q ∂(B.restrict S).map drift, q 0 = 0 := by
    rw [ae_map_iff hdrift.aemeasurable
      (measurableSet_eq_fun (ContinuousMap.measurable_eval 0) measurable_const)]
    filter_upwards [hzeroRestrict] with p hp
    change drift p 0 = 0
    simp [drift, driftedBrownianPath, hp]
  have hH : 0 < conditionedH ν x := conditionedH_pos_ref hν hx
  have hden : ENNReal.ofReal (conditionedH ν x) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr hH)
  have hcoef : (ENNReal.ofReal (conditionedH ν x))⁻¹ ≠ 0 := by
    simp
  rw [brownianBelowConditionedLaw, MeasureTheory.Measure.ae_ennreal_smul_measure_iff hcoef]
  simpa [drift, S] using hzeroMap

/-- The deterministic-time reference future starts at its prescribed positive state. -/
theorem brownianUpperConditionedReferenceFutureKernel_eval_zero_ae
    (B : Measure BrownianPath) [SFinite B]
    (hB : IsBrownianReal (fun t p => p t) B)
    (ν x : ℝ) (hν : 0 < ν) (hx : 0 < x) :
    ∀ᵐ y ∂brownianUpperConditionedReferenceFutureKernel B ν hν x, y 0 = x := by
  rw [brownianUpperConditionedReferenceFutureKernel_apply_conditioned B ν x hν hx]
  have hEval : Measurable (fun q : BrownianPath =>
      brownianUpperConditionedPositiveRationalEvals x q) :=
    measurable_brownianUpperConditionedPositiveRationalEvals.comp
      (measurable_const.prodMk measurable_id)
  have hzero : MeasurableSet {y : ℚ → ℝ | y 0 = x} :=
    measurableSet_eq_fun (measurable_pi_apply 0) measurable_const
  rw [ae_map_iff hEval.aemeasurable hzero]
  filter_upwards [brownianBelowConditionedLaw_eval_zero_ae B hB ν x hν hx]
    with q hq
  simp only [brownianUpperConditionedPositiveRationalEvals,
    brownianUpperConditionedPositivePath]
  have hz : (⟨max ((0 : ℚ) : ℝ) 0,
      le_max_right ((0 : ℚ) : ℝ) 0⟩ : ℝ≥0) = 0 := by
    apply Subtype.ext
    norm_num
  rw [hz]
  change x - q 0 = x
  rw [hq]
  ring

/-- The reference and abstract conditioned futures have the same full endpoint/future law.
Finite positive-time projections agree by the explicit density calculation; the rational
cylinder pi-system then gives equality on the entire future sequence. Nonpositive coordinates are
read from the endpoint, as both path constructions require. -/
theorem conditionedPositiveFutureKernel_reference_compProd
    {ν : ℝ} {P : Measure BrownianPath} [IsFiniteMeasure P]
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (B : Measure BrownianPath) [SFinite B]
    (hB : IsBrownianReal (fun t p => p t) B)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (hν : 0 < ν) :
    (P.map (conditionedPositiveStateAt t)) ⊗ₘ conditionedPositiveFutureKernel t P =
      (P.map (conditionedPositiveStateAt t)) ⊗ₘ
        brownianUpperConditionedReferenceFutureKernel B ν hν := by
  classical
  let μA : Measure (ℝ × (ℚ → ℝ)) :=
    (P.map (conditionedPositiveStateAt t)) ⊗ₘ conditionedPositiveFutureKernel t P
  let μR : Measure (ℝ × (ℚ → ℝ)) :=
    (P.map (conditionedPositiveStateAt t)) ⊗ₘ
      brownianUpperConditionedReferenceFutureKernel B ν hν
  have hdiagSet : MeasurableSet {z : ℝ × (ℚ → ℝ) |
      ∀ q : ℚ, (q : ℝ) ≤ 0 → z.2 q = z.1} := by
    have hcoord (q : ℚ) : MeasurableSet
        {z : ℝ × (ℚ → ℝ) | (q : ℝ) > 0 ∨ z.2 q = z.1} := by
      by_cases hq : 0 < (q : ℝ)
      · simp [hq]
      · have heq : MeasurableSet {z : ℝ × (ℚ → ℝ) | z.2 q = z.1} :=
          measurableSet_eq_fun ((measurable_pi_apply q).comp measurable_snd) measurable_fst
        simpa [hq] using heq
    have hset : {z : ℝ × (ℚ → ℝ) | ∀ q : ℚ, (q : ℝ) ≤ 0 → z.2 q = z.1} =
        ⋂ q : ℚ, {z : ℝ × (ℚ → ℝ) | (q : ℝ) > 0 ∨ z.2 q = z.1} := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      change (∀ q : ℚ, (q : ℝ) ≤ 0 → z.2 q = z.1) ↔
        (∀ q : ℚ, (q : ℝ) > 0 ∨ z.2 q = z.1)
      constructor
      · intro hz q
        by_cases hq : (q : ℝ) ≤ 0
        · exact Or.inr (hz q hq)
        · exact Or.inl (lt_of_not_ge hq)
      · intro hz q hq
        rcases hz q with hq' | heq
        · exact False.elim (not_lt_of_ge hq hq')
        · exact heq
    rw [hset]
    exact MeasurableSet.iInter hcoord
  have hdiagA : ∀ᵐ z ∂μA, ∀ q : ℚ, (q : ℝ) ≤ 0 → z.2 q = z.1 := by
    change ∀ᵐ z ∂((P.map (conditionedPositiveStateAt t)) ⊗ₘ
      conditionedPositiveFutureKernel t P), _
    rw [conditionedPositiveFutureKernel_compProd]
    rw [ae_map_iff
      ((measurable_conditionedPositiveStateAt t).prodMk
        (measurable_conditionedPositiveFutureRationalEvals t)).aemeasurable hdiagSet]
    filter_upwards with p
    intro q hq
    let s : ℝ≥0 := ⟨max (q : ℝ) 0, le_max_right _ _⟩
    have hs : s = 0 := by
      apply Subtype.ext
      simp [s, max_eq_right hq]
    simp [conditionedPositiveFutureRationalEvals, conditionedPositiveFuturePath,
      conditionedPositiveStateAt, s, hs]
  have hstatePos : ∀ᵐ x ∂P.map (conditionedPositiveStateAt t), 0 < x :=
    (ae_map_iff (μ := P) (f := conditionedPositiveStateAt t)
      (measurable_conditionedPositiveStateAt t).aemeasurable
      (p := fun x : ℝ => 0 < x)
      (measurableSet_lt measurable_const measurable_id)).2
      (conditionedPositiveStateAt_pos_ae hP t ht)
  have hdiagR : ∀ᵐ z ∂μR, ∀ q : ℚ, (q : ℝ) ≤ 0 → z.2 q = z.1 := by
    have hfiber : ∀ᵐ x ∂P.map (conditionedPositiveStateAt t),
        ∀ᵐ y ∂brownianUpperConditionedReferenceFutureKernel B ν hν x,
          ∀ q : ℚ, (q : ℝ) ≤ 0 → y q = x := by
      filter_upwards [hstatePos] with x hx
      rw [brownianUpperConditionedReferenceFutureKernel_apply_conditioned B ν x hν hx]
      have hseqSet : MeasurableSet {y : ℚ → ℝ |
          ∀ q : ℚ, (q : ℝ) ≤ 0 → y q = x} := by
        have hcoord (q : ℚ) : MeasurableSet
            {y : ℚ → ℝ | (q : ℝ) > 0 ∨ y q = x} := by
          by_cases hq : 0 < (q : ℝ)
          · simp [hq]
          · have heq : MeasurableSet {y : ℚ → ℝ | y q = x} :=
              measurableSet_eq_fun (measurable_pi_apply q) measurable_const
            simpa [hq] using heq
        have hset : {y : ℚ → ℝ | ∀ q : ℚ, (q : ℝ) ≤ 0 → y q = x} =
            ⋂ q : ℚ, {y : ℚ → ℝ | (q : ℝ) > 0 ∨ y q = x} := by
          ext y
          simp only [Set.mem_ofPred_eq, Set.mem_iInter]
          constructor
          · intro hy q
            by_cases hq : (q : ℝ) ≤ 0
            · exact Or.inr (hy q hq)
            · exact Or.inl (lt_of_not_ge hq)
          · intro hy q hq
            rcases hy q with hp | heq
            · exact False.elim (not_lt_of_ge hq hp)
            · exact heq
        rw [hset]
        exact MeasurableSet.iInter hcoord
      apply (ae_map_iff
        ((measurable_brownianUpperConditionedPositiveRationalEvals.comp
          (measurable_const.prodMk measurable_id)).aemeasurable)
        hseqSet).2
      filter_upwards [brownianBelowConditionedLaw_eval_zero_ae B hB ν x hν hx]
        with p hp
      intro q hq
      let s : ℝ≥0 := ⟨max (q : ℝ) 0, le_max_right _ _⟩
      have hs : s = 0 := by
        apply Subtype.ext
        simp [s, max_eq_right hq]
      change brownianUpperConditionedPositiveRationalEvals x p q = x
      simp [brownianUpperConditionedPositiveRationalEvals,
        brownianUpperConditionedPositivePath, s, hs, hp]
    exact Measure.ae_compProd_of_ae_ae hdiagSet hfiber
  let pack : ℝ × (ℚ → ℝ) → (Fin 1 → ℝ) × (ℚ → ℝ) :=
    fun z => (fun _ => z.1, z.2)
  have hpack : Measurable pack := by
    apply (measurable_pi_iff.mpr fun _ => measurable_fst).prodMk measurable_snd
  let μAp : Measure ((Fin 1 → ℝ) × (ℚ → ℝ)) := μA.map pack
  let μRp : Measure ((Fin 1 → ℝ) × (ℚ → ℝ)) := μR.map pack
  have hrect : ∀ s ∈ MeasureTheory.measurableCylinders (fun _ : Fin 1 => ℝ),
      ∀ u ∈ MeasureTheory.measurableCylinders (fun _ : ℚ => ℝ),
        μAp (s ×ˢ u) = μRp (s ×ˢ u) := by
    intro s hs u hu
    obtain ⟨I, S, hS, rfl⟩ := (MeasureTheory.mem_measurableCylinders s).mp hs
    obtain ⟨J, T, hT, rfl⟩ := (MeasureTheory.mem_measurableCylinders u).mp hu
    let positiveGrid : Finset ℚ := J.filter fun q => 0 < (q : ℝ)
    let n := positiveGrid.card
    let offsets : Fin n → ℚ := fun i => (positiveGrid.orderIsoOfFin rfl i).val
    have hOffsetsPos : ∀ i, 0 < (offsets i : ℝ) := by
      intro i
      exact (Finset.mem_filter.mp (positiveGrid.orderIsoOfFin rfl i).2).2
    have hOffsetsMono : StrictMono offsets := by
      intro i j hij
      simpa [offsets] using (positiveGrid.orderIsoOfFin rfl).strictMono hij
    let futureTimes : Fin n → ℝ≥0 := fun i => t + (offsets i : ℝ).toNNReal
    have hFutureMono : StrictMono futureTimes := by
      intro i j hij
      have hq := hOffsetsMono hij
      have hqReal : (offsets i : ℝ) < (offsets j : ℝ) := by exact_mod_cast hq
      have hqNN : (offsets i : ℝ).toNNReal < (offsets j : ℝ).toNNReal := by
        apply NNReal.coe_lt_coe.mp
        rw [Real.coe_toNNReal _ (hOffsetsPos i).le,
          Real.coe_toNNReal _ (hOffsetsPos j).le]
        exact hqReal
      simpa [futureTimes] using add_lt_add_left hqNN t
    have hOneMono : StrictMono (fun _ : Fin 1 => t) := by
      intro i j hij
      fin_cases i
      fin_cases j
      omega
    have hMonoEndpoint : StrictMono (Fin.append (fun _ : Fin 1 => t) futureTimes) :=
      strictMono_finAppend_of_cross (fun _ : Fin 1 => t) futureTimes hOneMono hFutureMono
        (fun _ j => by
          have hq : 0 < (offsets j : ℝ).toNNReal := by
            apply NNReal.coe_pos.mp
            rw [Real.coe_toNNReal _ (hOffsetsPos j).le]
            exact hOffsetsPos j
          simpa [futureTimes] using lt_add_of_pos_right t hq)
    let futureProject : (ℚ → ℝ) → Fin n → ℝ := fun y i => y (offsets i)
    let pairProject : ℝ × (ℚ → ℝ) → ℝ × (Fin n → ℝ) :=
      fun z => (z.1, futureProject z.2)
    have hFutureProject : Measurable futureProject := by
      apply measurable_pi_iff.mpr
      intro i
      exact measurable_pi_apply (offsets i)
    have hPairProject : Measurable pairProject :=
      measurable_fst.prodMk (hFutureProject.comp measurable_snd)
    let readPair : (ℝ × (Fin n → ℝ)) → ( (∀ i : I, ℝ) × (∀ j : J, ℝ)) :=
      fun z => (fun _ => z.1, fun j =>
        if hq : 0 < (j.1 : ℝ) then
          z.2 ((positiveGrid.orderIsoOfFin rfl).symm ⟨j.1,
            Finset.mem_filter.mpr ⟨j.2, hq⟩⟩)
        else z.1)
    have hReadPair : Measurable readPair := by
      apply (measurable_pi_iff.mpr fun _ => measurable_fst).prodMk
      apply measurable_pi_iff.mpr
      intro j
      by_cases hq : 0 < (j.1 : ℝ)
      · simp only [dite_eq_left hq]
        exact (measurable_pi_apply _).comp measurable_snd
      · simp only [dite_eq_right hq]
        exact measurable_fst
    have hReadA : ∀ᵐ z ∂μA, readPair (pairProject z) =
        (I.restrict (fun _ : Fin 1 => z.1), J.restrict z.2) := by
      filter_upwards [hdiagA] with z hz
      apply Prod.ext
      · funext i
        rfl
      · funext j
        by_cases hq : 0 < (j.1 : ℝ)
        · have hjGrid : j.1 ∈ positiveGrid :=
            Finset.mem_filter.mpr ⟨j.2, hq⟩
          let i : Fin n := (positiveGrid.orderIsoOfFin rfl).symm ⟨j.1, hjGrid⟩
          have hi : positiveGrid.orderIsoOfFin rfl i = ⟨j.1, hjGrid⟩ :=
            (positiveGrid.orderIsoOfFin rfl).apply_symm_apply ⟨j.1, hjGrid⟩
          have hoff : offsets i = j.1 := congrArg Subtype.val hi
          simp [readPair, pairProject, futureProject, hq, i, hoff]
        · have hq' : (j.1 : ℝ) ≤ 0 := le_of_not_gt hq
          have hdiag := hz j.1 hq'
          simp [readPair, pairProject, hq, hdiag]
    have hReadR : ∀ᵐ z ∂μR, readPair (pairProject z) =
        (I.restrict (fun _ : Fin 1 => z.1), J.restrict z.2) := by
      filter_upwards [hdiagR] with z hz
      apply Prod.ext
      · funext i
        rfl
      · funext j
        by_cases hq : 0 < (j.1 : ℝ)
        · have hjGrid : j.1 ∈ positiveGrid :=
            Finset.mem_filter.mpr ⟨j.2, hq⟩
          let i : Fin n := (positiveGrid.orderIsoOfFin rfl).symm ⟨j.1, hjGrid⟩
          have hi : positiveGrid.orderIsoOfFin rfl i = ⟨j.1, hjGrid⟩ :=
            (positiveGrid.orderIsoOfFin rfl).apply_symm_apply ⟨j.1, hjGrid⟩
          have hoff : offsets i = j.1 := congrArg Subtype.val hi
          simp [readPair, pairProject, futureProject, hq, i, hoff]
        · have hq' : (j.1 : ℝ) ≤ 0 := le_of_not_gt hq
          have hdiag := hz j.1 hq'
          simp [readPair, pairProject, hq, hdiag]
    have hmapEventA : μAp (MeasureTheory.cylinder I S ×ˢ MeasureTheory.cylinder J T) =
        ((μA.map pairProject).map readPair) (S ×ˢ T) := by
      change (μA.map pack) (MeasureTheory.cylinder I S ×ˢ MeasureTheory.cylinder J T) = _
      rw [Measure.map_apply hpack
        (MeasurableSet.prod
          (MeasurableSet.of_mem_measurableCylinders
            (MeasureTheory.cylinder_mem_measurableCylinders I S hS))
          (MeasurableSet.of_mem_measurableCylinders
            (MeasureTheory.cylinder_mem_measurableCylinders J T hT))),
        Measure.map_map hReadPair hPairProject,
        Measure.map_apply (hReadPair.comp hPairProject) (MeasurableSet.prod hS hT)]
      apply measure_congr
      filter_upwards [hReadA] with z hz
      simp [MeasureTheory.cylinder, pack, hz]
    have hmapEventR : μRp (MeasureTheory.cylinder I S ×ˢ MeasureTheory.cylinder J T) =
        ((μR.map pairProject).map readPair) (S ×ˢ T) := by
      change (μR.map pack) (MeasureTheory.cylinder I S ×ˢ MeasureTheory.cylinder J T) = _
      rw [Measure.map_apply hpack
        (MeasurableSet.prod
          (MeasurableSet.of_mem_measurableCylinders
            (MeasureTheory.cylinder_mem_measurableCylinders I S hS))
          (MeasurableSet.of_mem_measurableCylinders
            (MeasureTheory.cylinder_mem_measurableCylinders J T hT))),
        Measure.map_map hReadPair hPairProject,
        Measure.map_apply (hReadPair.comp hPairProject) (MeasurableSet.prod hS hT)]
      apply measure_congr
      filter_upwards [hReadR] with z hz
      simp [MeasureTheory.cylinder, pack, hz]
    have hfiniteProj : μA.map pairProject = μR.map pairProject := by
      simpa [μA, μR, pairProject, futureProject] using
        (conditionedPositiveFutureKernel_reference_finite_compProd
          (hP := hP) B hB t ht hν n offsets hOffsetsPos hOffsetsMono hMonoEndpoint)
    rw [hmapEventA, hmapEventR, hfiniteProj]
  have htotal := hrect Set.univ
    (MeasureTheory.univ_mem_measurableCylinders (fun _ : Fin 1 => ℝ)) Set.univ
    (MeasureTheory.univ_mem_measurableCylinders (fun _ : ℚ => ℝ))
  have hfinite : μAp Set.univ < ∞ := by
    change (μA.map pack) Set.univ < ∞
    rw [Measure.map_apply hpack MeasurableSet.univ]
    exact measure_lt_top _ _
  let : IsFiniteMeasure μAp := ⟨hfinite⟩
  have hpacked := measure_eq_of_cylinder_rectangles μAp μRp hrect (by simpa using htotal)
  let unpack : (Fin 1 → ℝ) × (ℚ → ℝ) → ℝ × (ℚ → ℝ) :=
    fun z => (z.1 0, z.2)
  have hunpack : Measurable unpack :=
    ((measurable_pi_apply 0).comp measurable_fst).prodMk measurable_snd
  have hpackUnpack : unpack ∘ pack = id := by
    funext z
    ext <;> rfl
  have hleft : μA = μAp.map unpack := by
    change μA = (μA.map pack).map unpack
    rw [Measure.map_map hunpack hpack]
    rw [hpackUnpack, Measure.map_id]
  have hright : μR = μRp.map unpack := by
    change μR = (μR.map pack).map unpack
    rw [Measure.map_map hunpack hpack]
    rw [hpackUnpack, Measure.map_id]
  change μA = μR
  rw [hleft, hright, hpacked]

/-- The actual conditional future kernel is the Brownian reference kernel at almost every state
of the entrance process. The joint-law identity above and uniqueness of disintegrations upgrade
the cylinder calculation to equality of the complete rational-path kernels. -/
theorem conditionedPositiveFutureKernel_eq_reference_ae
    {ν : ℝ} {P : Measure BrownianPath} [IsFiniteMeasure P]
    (hP : IsNegativeConditionedBrownianLaw ν P)
    (B : Measure BrownianPath) [SFinite B]
    (hB : IsBrownianReal (fun t p => p t) B)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (hν : 0 < ν) :
    ∀ᵐ x ∂P.map (conditionedPositiveStateAt t),
      conditionedPositiveFutureKernel t P x =
        brownianUpperConditionedReferenceFutureKernel B ν hν x := by
  classical
  let μx : Measure ℝ := P.map (conditionedPositiveStateAt t)
  let κA : Kernel ℝ (ℚ → ℝ) := conditionedPositiveFutureKernel t P
  let κR : Kernel ℝ (ℚ → ℝ) :=
    brownianUpperConditionedReferenceFutureKernel B ν hν
  let ρ : Measure (ℝ × (ℚ → ℝ)) := μx ⊗ₘ κA
  have hμxTop : μx Set.univ < ∞ := by
    change (P.map (conditionedPositiveStateAt t)) Set.univ < ∞
    rw [Measure.map_apply (measurable_conditionedPositiveStateAt t)
      MeasurableSet.univ]
    simp only [Set.preimage_univ]
    exact measure_lt_top _ _
  have hfst : ρ.fst = μx := by
    change (μx ⊗ₘ κA).fst = μx
    exact Measure.fst_compProd μx κA
  have hρTop : ρ Set.univ < ∞ := by
    have htotal : ρ Set.univ = μx Set.univ := by
      have hh := congrArg (fun m : Measure ℝ => m Set.univ) hfst
      calc
        ρ Set.univ = (Measure.map Prod.fst ρ) Set.univ := by
          rw [Measure.map_apply measurable_fst MeasurableSet.univ]
          simp
        _ = μx Set.univ := hh
    rw [htotal]
    exact hμxTop
  let : IsFiniteMeasure ρ := ⟨hρTop⟩
  let : IsFiniteKernel κR :=
    isFiniteKernel_brownianUpperConditionedReferenceFutureKernel B hB ν hν
  have hcomp : ρ = μx ⊗ₘ κR := by
    simpa [ρ, μx, κA, κR] using
      (conditionedPositiveFutureKernel_reference_compProd
        (hP := hP) B hB t ht hν)
  have hA : ρ = ρ.fst ⊗ₘ κA := by
    rw [hfst]
  have hR : ρ = ρ.fst ⊗ₘ κR := by
    calc
      ρ = μx ⊗ₘ κR := hcomp
      _ = ρ.fst ⊗ₘ κR := by rw [hfst]
  have hAae : ∀ᵐ x ∂μx, κA x = ρ.condKernel x := by
    simpa [hfst] using eq_condKernel_of_measure_eq_compProd κA hA
  have hRae : ∀ᵐ x ∂μx, κR x = ρ.condKernel x := by
    simpa [hfst] using eq_condKernel_of_measure_eq_compProd κR hR
  filter_upwards [hAae, hRae] with x hAx hRx
  rw [hAx, hRx]

end DOZZ.Proofs

end

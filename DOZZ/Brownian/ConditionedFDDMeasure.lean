/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitFDDMarkov
public import DOZZ.Brownian.ConditionedKernelProbability
public import Mathlib.Probability.Kernel.Composition.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Positive-coordinate finite-dimensional laws

The path-law characterization `DOZZ.IsNegativeConditionedBrownianLaw` is stated for negative
coordinates. This file transports each of its finite-dimensional laws through coordinatewise
reflection, preserving the Lebesgue density and exposing the positive entrance density used in
the deterministic-time Markov split.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DOZZ.Proofs

/-- Coordinatewise reflection on a finite-dimensional real vector. -/
def conditionedCoordinateNegEquiv (ι : Type*) [Fintype ι] : (ι → ℝ) ≃ᵐ (ι → ℝ) :=
  MeasurableEquiv.piCongrRight fun _ => MeasurableEquiv.neg ℝ

@[simp]
theorem conditionedCoordinateNegEquiv_apply (ι : Type*) [Fintype ι]
    (x : ι → ℝ) (i : ι) :
    conditionedCoordinateNegEquiv ι x i = -x i := rfl

/-- Coordinatewise reflection preserves finite-dimensional Lebesgue measure. -/
theorem map_conditionedCoordinateNegEquiv_volume (ι : Type*) [Fintype ι] :
    (volume : Measure (ι → ℝ)).map (conditionedCoordinateNegEquiv ι) = volume := by
  let : SigmaFinite ((volume : Measure ℝ).map Neg.neg) := by
    rw [Measure.map_neg_eq_self]
    infer_instance
  have hpi :
      (Measure.pi (fun _ : ι => (volume : Measure ℝ))).map
          (fun x i => -x i) = Measure.pi (fun _ : ι => (volume : Measure ℝ)) := by
    rw [Measure.pi_map_pi (f := fun _ => Neg.neg) (fun _ => measurable_neg.aemeasurable)]
    simp only [Measure.map_neg_eq_self]
  calc
    (volume : Measure (ι → ℝ)).map (conditionedCoordinateNegEquiv ι) =
        (Measure.pi (fun _ : ι => (volume : Measure ℝ))).map (fun x i => -x i) := by
          rw [volume_pi]
          rfl
    _ = Measure.pi (fun _ : ι => (volume : Measure ℝ)) := hpi
    _ = volume := by rw [volume_pi]

/-- Transport a density through a measure-preserving measurable equivalence. -/
theorem map_withDensity_of_measurePreserving_equiv
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (ν : Measure β)
    (hμ : MeasurePreserving e μ ν) (f : α → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map e = ν.withDensity (f ∘ e.symm) := by
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply e.measurable hs,
    withDensity_apply f (hs.preimage e.measurable),
    withDensity_apply (f ∘ e.symm) hs]
  calc
    ∫⁻ x in e ⁻¹' s, f x ∂μ =
        ∫⁻ x in e ⁻¹' s, f (e.symm (e x)) ∂μ := by
          apply setLIntegral_congr_fun
          · exact hs.preimage e.measurable
          · intro x hx
            simp
    _ = ∫⁻ x in s, f (e.symm x) ∂ν := by
          conv_rhs => rw [← hμ.map_eq]
          exact (setLIntegral_map hs (hf.comp e.symm.measurable) e.measurable).symm

/-- Reindex a finite vector into its past and future coordinate blocks. -/
noncomputable def conditionedFiniteVectorSplitEquiv (m n : ℕ) :
    (Fin (m + n) → ℝ) ≃ᵐ ((Fin m → ℝ) × (Fin n → ℝ)) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin (m + n) => ℝ) finSumFinEquiv).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n => ℝ))

@[simp]
theorem conditionedFiniteVectorSplitEquiv_append (m n : ℕ)
    (x : Fin m → ℝ) (y : Fin n → ℝ) :
    conditionedFiniteVectorSplitEquiv m n (Fin.append x y) = (x, y) := by
  change Equiv.sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n => ℝ)
      ((Equiv.piCongrLeft (fun _ : Fin (m + n) => ℝ) finSumFinEquiv).symm
        (Fin.append x y)) = (x, y)
  ext i <;> simp [Equiv.sumPiEquivProdPi_apply,
    Equiv.piCongrLeft_symm_apply, Fin.append_left, Fin.append_right]

/-- The finite-vector past/future reindexing preserves Lebesgue measure. -/
theorem measurePreserving_conditionedFiniteVectorSplitEquiv (m n : ℕ) :
    MeasurePreserving (conditionedFiniteVectorSplitEquiv m n)
      (volume : Measure (Fin (m + n) → ℝ))
      (volume : Measure ((Fin m → ℝ) × (Fin n → ℝ))) := by
  unfold conditionedFiniteVectorSplitEquiv
  exact
    ((volume_measurePreserving_piCongrLeft (fun _ : Fin (m + n) => ℝ)
      (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n))).symm).trans
      (volume_measurePreserving_sumPiEquivProdPi
        (fun _ : Fin m ⊕ Fin n => ℝ))

/-- If a finite-dimensional density splits into a past factor and a future factor depending on
the past endpoint, its law is the composition product of the past law and the future density
kernel. This is the measure-level form of finite-cylinder Markov factorization. -/
theorem map_withDensity_conditionedFiniteVectorSplit
    (m n : ℕ) (f : (Fin m → ℝ) → ℝ≥0∞)
    (g : (Fin m → ℝ) → (Fin n → ℝ) → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable (Function.uncurry g))
    (hgtop : ∀ x y, g x y ≠ ∞) :
    (((volume : Measure (Fin (m + n) → ℝ)).withDensity
      (fun z => f ((conditionedFiniteVectorSplitEquiv m n z).1) *
        g (conditionedFiniteVectorSplitEquiv m n z).1
          (conditionedFiniteVectorSplitEquiv m n z).2)).map
        (conditionedFiniteVectorSplitEquiv m n)) =
      ((volume : Measure (Fin m → ℝ)).withDensity f) ⊗ₘ
        (Kernel.const (Fin m → ℝ) (volume : Measure (Fin n → ℝ))).withDensity g := by
  let e := conditionedFiniteVectorSplitEquiv m n
  have hvol := measurePreserving_conditionedFiniteVectorSplitEquiv m n
  have hdensity : Measurable (fun z : Fin (m + n) → ℝ =>
      f (e z).1 * g (e z).1 (e z).2) := by
    exact (hf.comp measurable_fst).mul
      (hg.comp (measurable_fst.prodMk measurable_snd)) |>.comp e.measurable
  rw [map_withDensity_of_measurePreserving_equiv e volume volume hvol _ hdensity]
  have hcomp :
      ((volume : Measure (Fin m → ℝ)).withDensity f) ⊗ₘ
        (Kernel.const (Fin m → ℝ) (volume : Measure (Fin n → ℝ))).withDensity g =
      (volume : Measure ((Fin m → ℝ) × (Fin n → ℝ))).withDensity
        (fun z => f z.1 * g z.1 z.2) := by
    let : IsSFiniteKernel
        ((Kernel.const (Fin m → ℝ) (volume : Measure (Fin n → ℝ))).withDensity g) :=
      Kernel.IsSFiniteKernel.withDensity _ hgtop
    rw [Measure.withDensity_compProd_withDensity hf hg,
      Measure.compProd_const, ← Measure.volume_eq_prod]
  rw [hcomp]
  congr 1
  funext z
  simp [e]

private theorem measurable_negativeConditionedTransitionDensity_pair
    (ν dt : ℝ) :
    Measurable (fun z : ℝ × ℝ => negativeConditionedTransitionDensity ν dt z.1 z.2) := by
  classical
  by_cases hν : 0 ≤ ν
  · by_cases hdt : 0 < dt
    · have hset : MeasurableSet {z : ℝ × ℝ | 0 < -z.1 ∧ 0 < -z.2} := by
        exact (measurableSet_lt measurable_const measurable_fst.neg).inter
          (measurableSet_lt measurable_const measurable_snd.neg)
      have hform : Measurable (fun z : ℝ × ℝ =>
          Real.exp (ν * (-z.2 - -z.1) - ν ^ 2 * dt / 2) *
            (brownianHeatDensity dt (-z.2 - -z.1) -
              brownianHeatDensity dt (-z.2 + -z.1)) *
            conditionedH ν (-z.2) / conditionedH ν (-z.1)) := by
        by_cases hν0 : ν = 0
        · simp [brownianHeatDensity, hdt, conditionedH, hν0]
          fun_prop
        · simp [brownianHeatDensity, hdt, conditionedH, hν0]
          fun_prop
      let : DecidablePred (fun z : ℝ × ℝ => 0 < -z.1 ∧ 0 < -z.2) :=
        fun z => Classical.propDecidable _
      simpa [negativeConditionedTransitionDensity, conditionedPositiveTransitionDensity,
        hν, hdt] using
        @Measurable.ite (ℝ × ℝ) ℝ _ _ _ _
          (fun z : ℝ × ℝ => 0 < -z.1 ∧ 0 < -z.2) this hset hform measurable_const
    · simp [negativeConditionedTransitionDensity, conditionedPositiveTransitionDensity, hν, hdt]
  · simp [negativeConditionedTransitionDensity, conditionedPositiveTransitionDensity, hν]

theorem measurable_conditionedPositiveEntranceDensity_arg
    (ν t : ℝ) : Measurable (fun y : ℝ => conditionedPositiveEntranceDensity ν t y) := by
  classical
  by_cases hν : 0 ≤ ν
  · by_cases ht : 0 < t
    · have hset : MeasurableSet {y : ℝ | 0 < y} :=
        measurableSet_lt measurable_const measurable_id
      have hform : Measurable (fun y : ℝ =>
          if ν = 0 then
            Real.sqrt (2 / Real.pi) * y ^ 2 / t ^ (3 / 2 : ℝ) *
              Real.exp (-y ^ 2 / (2 * t))
          else Real.sqrt (2 / Real.pi) * t ^ (-(3 / 2 : ℝ)) *
              (y * Real.sinh (ν * y) / ν) *
              Real.exp (-y ^ 2 / (2 * t) - ν ^ 2 * t / 2)) := by
        by_cases hν0 : ν = 0
        · simp [hν0]
          fun_prop
        · simp [hν0]
          fun_prop
      let : DecidablePred (fun y : ℝ => 0 < y) := fun y => Classical.propDecidable _
      simpa [conditionedPositiveEntranceDensity, hν, ht] using
        @Measurable.ite ℝ ℝ _ _ _ _ (fun y : ℝ => 0 < y) this hset hform measurable_const
    · simp [conditionedPositiveEntranceDensity, hν, ht]
  · simp [conditionedPositiveEntranceDensity, hν]

/-- Joint measurability of the explicit positive Doob transition density in start and endpoint. -/
theorem measurable_conditionedPositiveTransitionDensity_pair
    (ν dt : ℝ) :
    Measurable (fun z : ℝ × ℝ => conditionedPositiveTransitionDensity ν dt z.1 z.2) := by
  have hneg := measurable_negativeConditionedTransitionDensity_pair ν dt
  have hreflect : Measurable (fun z : ℝ × ℝ => (-z.1, -z.2)) :=
    measurable_fst.neg.prodMk measurable_snd.neg
  have hfun : (fun z : ℝ × ℝ => conditionedPositiveTransitionDensity ν dt z.1 z.2) =
      (fun z => negativeConditionedTransitionDensity ν dt (-z.1) (-z.2)) := by
    funext z
    simp [negativeConditionedTransitionDensity]
  rw [hfun]
  exact hneg.comp hreflect

/-- The entrance density is nonnegative everywhere for nonnegative drift and positive time. -/
theorem conditionedPositiveEntranceDensity_nonneg
    {ν t : ℝ} (hν : 0 ≤ ν) (ht : 0 < t) (y : ℝ) :
    0 ≤ conditionedPositiveEntranceDensity ν t y := by
  by_cases hy : 0 < y
  · by_cases hν0 : ν = 0
    · simp [conditionedPositiveEntranceDensity, ht, hy, hν0]
      positivity
    · have hνpos : 0 < ν := lt_of_le_of_ne hν (Ne.symm hν0)
      simp only [conditionedPositiveEntranceDensity, hν, ht, hy, and_self, ite_true, hν0]
      have hsinh : 0 < Real.sinh (ν * y) := Real.sinh_pos_iff.mpr (mul_pos hνpos hy)
      positivity
  · have hy' : y ≤ 0 := le_of_not_gt hy
    simp [conditionedPositiveEntranceDensity, hν, ht, not_lt.mpr hy']

private theorem conditionedPositiveEntranceDensity_nonneg_any
    {ν t : ℝ} (hν : 0 ≤ ν) (y : ℝ) :
    0 ≤ conditionedPositiveEntranceDensity ν t y := by
  by_cases ht : 0 < t
  · exact conditionedPositiveEntranceDensity_nonneg hν ht y
  · have ht' : t ≤ 0 := le_of_not_gt ht
    simp [conditionedPositiveEntranceDensity, hν, not_lt.mpr ht']

private theorem conditionedPositiveTransitionDensity_nonneg_any
    {ν t x : ℝ} (hν : 0 ≤ ν) (y : ℝ) :
    0 ≤ conditionedPositiveTransitionDensity ν t x y := by
  by_cases ht : 0 < t
  · by_cases hx : 0 < x
    · exact conditionedPositiveTransitionDensity_nonneg hν ht hx y
    · have hx' : x ≤ 0 := le_of_not_gt hx
      simp [conditionedPositiveTransitionDensity, hν, ht, not_lt.mpr hx']
  · have ht' : t ≤ 0 := le_of_not_gt ht
    simp [conditionedPositiveTransitionDensity, hν, not_lt.mpr ht']

/-- A finite transition chain has nonnegative density when its observation times are strictly
increasing after the starting time. -/
theorem conditionedPositiveTimeChainDensity_nonneg
    {ν t₀ x₀ : ℝ} (hν : 0 ≤ ν) (times values : List ℝ)
    (hlen : times.length = values.length) :
    0 ≤ conditionedPositiveTimeChainDensity ν t₀ x₀ times values := by
  induction times generalizing t₀ x₀ values with
  | nil =>
      cases values <;> simp [conditionedPositiveTimeChainDensity]
  | cons t ts ih =>
      cases values with
      | nil => simp at hlen
      | cons x xs =>
          have htailLen : ts.length = xs.length := by simpa using hlen
          have hstep : 0 ≤ conditionedPositiveTransitionDensity ν (t - t₀) x₀ x := by
            exact conditionedPositiveTransitionDensity_nonneg_any hν x
          have htail := ih (t₀ := t) (x₀ := x) xs htailLen
          simpa [conditionedPositiveTimeChainDensity] using mul_nonneg hstep htail

/-- The positive entrance finite-dimensional density is pointwise nonnegative at positive,
strictly increasing observation times. -/
theorem conditionedPositiveFDDDensity_nonneg
    {ν : ℝ} (hν : 0 ≤ ν) (times values : List ℝ)
    (hlen : times.length = values.length) :
    0 ≤ conditionedPositiveFDDDensity ν times values := by
  cases times with
  | nil =>
      cases values <;> simp [conditionedPositiveFDDDensity]
  | cons t ts =>
      cases values with
      | nil => simp at hlen
      | cons x xs =>
          have htailLen : ts.length = xs.length := by simpa using hlen
          have hentrance : 0 ≤ conditionedPositiveEntranceDensity ν t x :=
            conditionedPositiveEntranceDensity_nonneg_any hν x
          have hchain : 0 ≤ conditionedPositiveTimeChainDensity ν t x ts xs := by
            exact conditionedPositiveTimeChainDensity_nonneg hν ts xs htailLen
          simpa [conditionedPositiveFDDDensity] using mul_nonneg hentrance hchain

/-- The entrance FDD density splits at the final coordinate of any nonempty finite past block.
This form is convenient when the FDD is reindexed as a past vector and a future vector. -/
theorem conditionedPositiveFDDDensity_append_split
    (ν t₀ x₀ : ℝ) (pastTimes pastValues futureTimes futureValues : List ℝ)
    (hpast : pastTimes.length = pastValues.length) :
    conditionedPositiveFDDDensity ν (t₀ :: (pastTimes ++ futureTimes))
        (x₀ :: (pastValues ++ futureValues)) =
      conditionedPositiveFDDDensity ν (t₀ :: pastTimes) (x₀ :: pastValues) *
        conditionedPositiveTimeChainDensity ν
          (conditionedPositiveLastTime t₀ pastTimes)
          (conditionedPositiveLastState x₀ pastValues) futureTimes futureValues := by
  rw [conditionedPositiveFDDDensity_split ν t₀ x₀ pastTimes pastValues
    futureTimes futureValues hpast,
    conditionedPositiveFDDDensity_cons]

theorem conditionedPositiveLastTime_ofFn_tail {k : ℕ} (f : Fin (k + 1) → ℝ) :
    conditionedPositiveLastTime (f 0) (List.ofFn fun i : Fin k => f i.succ) =
      f (Fin.last k) := by
  induction k with
  | zero => simp [conditionedPositiveLastTime]
  | succ k ih =>
      rw [List.ofFn_succ, conditionedPositiveLastTime]
      simpa [Fin.last] using ih (fun i : Fin (k + 1) => f i.succ)

theorem conditionedPositiveLastState_ofFn_tail {k : ℕ} (f : Fin (k + 1) → ℝ) :
    conditionedPositiveLastState (f 0) (List.ofFn fun i : Fin k => f i.succ) =
      f (Fin.last k) := by
  induction k with
  | zero => simp [conditionedPositiveLastState]
  | succ k ih =>
      rw [List.ofFn_succ, conditionedPositiveLastState]
      simpa [Fin.last] using ih (fun i : Fin (k + 1) => f i.succ)

private theorem measurable_negativeConditionedTransitionChainDensity_ofFn
    (ν : ℝ) : ∀ (n : ℕ) (t₀ : ℝ) (times : Fin n → ℝ),
      Measurable (fun z : ℝ × (Fin n → ℝ) =>
          negativeConditionedTransitionChainDensity ν t₀ z.1
          (List.ofFn times) (List.ofFn z.2)) := by
  intro n
  induction n with
  | zero =>
      intro t₀ times
      simp [negativeConditionedTransitionChainDensity]
  | succ n ih =>
      intro t₀ times
      have hstep : Measurable (fun z : ℝ × (Fin (n + 1) → ℝ) =>
          negativeConditionedTransitionDensity ν (times 0 - t₀) z.1 (z.2 0)) := by
        exact (measurable_negativeConditionedTransitionDensity_pair ν
          (times 0 - t₀)).comp
            (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
      have hinput : Measurable (fun z : ℝ × (Fin (n + 1) → ℝ) =>
          (z.2 0, fun i : Fin n => z.2 i.succ)) := by
        exact (measurable_pi_apply 0).comp measurable_snd |>.prodMk
          (measurable_pi_iff.mpr fun i =>
            (measurable_pi_apply i.succ).comp measurable_snd)
      simp only [List.ofFn_succ, negativeConditionedTransitionChainDensity]
      exact hstep.mul ((ih (times 0) (fun i => times i.succ)).comp hinput)

private theorem measurable_negativeConditionedFDDDensity_ofFn
    (ν : ℝ) : ∀ (n : ℕ) (times : Fin n → ℝ),
      Measurable (fun x : Fin n → ℝ =>
        negativeConditionedFDDDensity ν (List.ofFn times) (List.ofFn x)) := by
  intro n
  induction n with
  | zero =>
      intro times
      simp [negativeConditionedFDDDensity]
  | succ n ih =>
      intro times
      have hinput : Measurable (fun x : Fin (n + 1) → ℝ =>
          (x 0, fun i : Fin n => x i.succ)) := by
        exact (measurable_pi_apply 0).prodMk
          (measurable_pi_iff.mpr fun i => measurable_pi_apply i.succ)
      have hentrance : Measurable (fun x : Fin (n + 1) → ℝ =>
          conditionedPositiveEntranceDensity ν (times 0) (-(x 0))) := by
        exact (measurable_conditionedPositiveEntranceDensity_arg ν (times 0)).comp
          (measurable_pi_apply 0).neg
      have hchain : Measurable (fun x : Fin (n + 1) → ℝ =>
          negativeConditionedTransitionChainDensity ν (times 0) (x 0)
            (List.ofFn fun i : Fin n => times i.succ)
            (List.ofFn fun i : Fin n => x i.succ)) := by
        exact (measurable_negativeConditionedTransitionChainDensity_ofFn ν n
          (times 0) (fun i : Fin n => times i.succ)).comp hinput
      simp only [List.ofFn_succ, negativeConditionedFDDDensity]
      change Measurable
        ((fun x : Fin (n + 1) → ℝ =>
            conditionedPositiveEntranceDensity ν (times 0) (-(x 0))) *
          (fun x : Fin (n + 1) → ℝ =>
            negativeConditionedTransitionChainDensity ν (times 0) (x 0)
              (List.ofFn fun i : Fin n => times i.succ)
              (List.ofFn fun i : Fin n => x i.succ)))
      exact hentrance.mul hchain

/-- The explicit positive entrance FDD density on a finite vector, in the `max 0` convention of
`DOZZ.IsNegativeConditionedBrownianLaw`. -/
noncomputable def conditionedPositiveFDDVectorDensity (ν : ℝ) {n : ℕ}
    (times : Fin n → ℝ) (x : Fin n → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (max 0 (conditionedPositiveFDDDensity ν (List.ofFn times) (List.ofFn x)))

/-- The finite future transition-chain density on a vector of future observations. -/
noncomputable def conditionedPositiveFutureVectorDensity (ν : ℝ) {k n : ℕ}
    (times : Fin (k + 1) → ℝ) (futureTimes : Fin n → ℝ)
    (x : Fin (k + 1) → ℝ) (y : Fin n → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (max 0 (conditionedPositiveTimeChainDensity ν
    (times (Fin.last k)) (x (Fin.last k))
    (List.ofFn futureTimes) (List.ofFn y)))

private theorem measurable_conditionedPositiveTimeChainDensity_ofFn
    (ν : ℝ) : ∀ (n : ℕ) (t₀ : ℝ) (times : Fin n → ℝ),
      Measurable (fun z : ℝ × (Fin n → ℝ) =>
        conditionedPositiveTimeChainDensity ν t₀ z.1
          (List.ofFn times) (List.ofFn z.2)) := by
  intro n
  induction n with
  | zero =>
      intro t₀ times
      simp [conditionedPositiveTimeChainDensity]
  | succ n ih =>
      intro t₀ times
      have hstep : Measurable (fun z : ℝ × (Fin (n + 1) → ℝ) =>
          conditionedPositiveTransitionDensity ν (times 0 - t₀) z.1 (z.2 0)) := by
        exact (measurable_conditionedPositiveTransitionDensity_pair ν
          (times 0 - t₀)).comp
            (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd))
      have hinput : Measurable (fun z : ℝ × (Fin (n + 1) → ℝ) =>
          (z.2 0, fun i : Fin n => z.2 i.succ)) := by
        exact (measurable_pi_apply 0).comp measurable_snd |>.prodMk
          (measurable_pi_iff.mpr fun i =>
            (measurable_pi_apply i.succ).comp measurable_snd)
      simp only [List.ofFn_succ, conditionedPositiveTimeChainDensity]
      exact hstep.mul ((ih (times 0) (fun i : Fin n => times i.succ)).comp hinput)

theorem measurable_conditionedPositiveFDDVectorDensity (ν : ℝ) {n : ℕ}
    (times : Fin n → ℝ) :
    Measurable (conditionedPositiveFDDVectorDensity ν times) := by
  have hneg : Measurable (fun x : Fin n → ℝ =>
      negativeConditionedFDDDensity ν (List.ofFn times)
        (List.ofFn fun i => -x i)) := by
    exact (measurable_negativeConditionedFDDDensity_ofFn ν n times).comp
      (measurable_pi_iff.mpr fun i => (measurable_pi_apply i).neg)
  have hEq : (fun x : Fin n → ℝ =>
      conditionedPositiveFDDDensity ν (List.ofFn times) (List.ofFn x)) =
      fun x => negativeConditionedFDDDensity ν (List.ofFn times)
        (List.ofFn fun i => -x i) := by
    funext x
    have hvals : List.ofFn (fun i : Fin n => -x i) =
        (List.ofFn fun i : Fin n => x i).map Neg.neg := by
      simp [Function.comp_def]
    calc
      conditionedPositiveFDDDensity ν (List.ofFn times) (List.ofFn x) =
          negativeConditionedFDDDensity ν (List.ofFn times)
            ((List.ofFn fun i : Fin n => x i).map Neg.neg) :=
        (negativeConditionedFDDDensity_reflect ν (List.ofFn times)
          (List.ofFn fun i : Fin n => x i)).symm
      _ = negativeConditionedFDDDensity ν (List.ofFn times)
          (List.ofFn fun i : Fin n => -x i) := by rw [← hvals]
  change Measurable (fun x : Fin n → ℝ => ENNReal.ofReal (max 0
    (conditionedPositiveFDDDensity ν (List.ofFn times) (List.ofFn x))))
  have hfun : (fun x : Fin n → ℝ => ENNReal.ofReal (max 0
      (conditionedPositiveFDDDensity ν (List.ofFn times) (List.ofFn x)))) =
    (fun x => ENNReal.ofReal (max 0
        (negativeConditionedFDDDensity ν (List.ofFn times)
        (List.ofFn fun i => -x i)))) := by
    funext x
    exact congrArg (fun z : ℝ => ENNReal.ofReal (max 0 z)) (congrFun hEq x)
  rw [hfun]
  exact ENNReal.measurable_ofReal.comp (Measurable.max measurable_const hneg)

theorem measurable_conditionedPositiveFutureVectorDensity (ν : ℝ) {k n : ℕ}
    (times : Fin (k + 1) → ℝ) (futureTimes : Fin n → ℝ) :
    Measurable (Function.uncurry (conditionedPositiveFutureVectorDensity ν times futureTimes)) := by
  let last : Fin (k + 1) := Fin.last k
  have hchain := measurable_conditionedPositiveTimeChainDensity_ofFn ν n
    (times last) futureTimes
  have hinput : Measurable (fun z : (Fin (k + 1) → ℝ) × (Fin n → ℝ) =>
      (z.1 last, z.2)) := by
    exact ((measurable_pi_apply last).comp measurable_fst).prodMk measurable_snd
  have hval : Measurable (fun z : (Fin (k + 1) → ℝ) × (Fin n → ℝ) =>
      conditionedPositiveTimeChainDensity ν (times last) (z.1 last)
        (List.ofFn futureTimes) (List.ofFn z.2)) := by
    exact hchain.comp ((measurable_fst.comp hinput).prodMk
      (measurable_snd.comp hinput))
  have hEq : Function.uncurry (conditionedPositiveFutureVectorDensity ν times futureTimes) =
      fun z => ENNReal.ofReal (max 0
        (conditionedPositiveTimeChainDensity ν (times last) (z.1 last)
          (List.ofFn futureTimes) (List.ofFn z.2))) := by
    funext z
    rfl
  rw [hEq]
  exact ENNReal.measurable_ofReal.comp (Measurable.max measurable_const hval)

/-- The positive-coordinate FDD of any law satisfying the negative FDD characterization
`DOZZ.IsNegativeConditionedBrownianLaw`. The density is kept in `max 0` form, exactly as in
that characterization. -/
theorem negativeConditionedLaw_positiveFDD
    {ν : ℝ} {P : Measure BrownianPath} (hP : IsNegativeConditionedBrownianLaw ν P)
    (n : ℕ) (hn : 0 < n) (times : Fin n → NNReal)
    (htimes : ∀ i, 0 < (times i : ℝ)) (hmono : StrictMono times) :
    P.map (fun p i => -(p (times i))) =
      (volume : Measure (Fin n → ℝ)).withDensity
        (fun x => ENNReal.ofReal (max 0 (conditionedPositiveFDDDensity ν
          (List.ofFn fun i => (times i : ℝ)) (List.ofFn fun i => x i)))) := by
  let neg := conditionedCoordinateNegEquiv (Fin n)
  have hnegmeas : Measurable neg := neg.measurable
  have hvol : MeasurePreserving neg (volume : Measure (Fin n → ℝ)) volume := by
    exact ⟨hnegmeas, map_conditionedCoordinateNegEquiv_volume (Fin n)⟩
  have hfd := hP.2.2.2 n hn times htimes hmono
  have heval : Measurable (fun p : BrownianPath => fun i => p (times i)) := by
    apply measurable_pi_iff.mpr
    intro i
    exact ContinuousMap.measurable_eval (times i)
  have hmap :
      (P.map (fun p i => -(p (times i)))) =
        (P.map (fun p i => p (times i))).map neg := by
    rw [Measure.map_map neg.measurable heval]
    rfl
  have hdensity : Measurable (fun x : Fin n → ℝ =>
      ENNReal.ofReal (max 0 (negativeConditionedFDDDensity ν
        (List.ofFn fun i => (times i : ℝ)) (List.ofFn fun i => x i)))) := by
    exact ENNReal.measurable_ofReal.comp (Measurable.max measurable_const
      (measurable_negativeConditionedFDDDensity_ofFn ν n
        (fun i => (times i : ℝ))))
  rw [hmap, hfd]
  rw [map_withDensity_of_measurePreserving_equiv neg volume volume hvol _ hdensity]
  congr 1
  funext x
  simp only [Function.comp_apply]
  have hvals : List.ofFn (fun i => neg.symm x i) =
      (List.ofFn fun i => x i).map Neg.neg := by
    calc
      List.ofFn (fun i => neg.symm x i) = List.ofFn (fun i => -x i) := by
        change List.ofFn (fun i => -x i) = List.ofFn (fun i => -x i)
        rfl
      _ = (List.ofFn fun i => x i).map Neg.neg := by
        rw [List.map_ofFn]
        rfl
  rw [hvals, negativeConditionedFDDDensity_reflect]

/-- At every strictly increasing finite observation grid, splitting immediately after the final
past coordinate turns the path FDD into the past density followed by the explicit future
transition-chain kernel. This is the finite past/future cylinder measure factorization. -/
theorem negativeConditionedLaw_finitePastFuture_compProd
    {ν : ℝ} {P : Measure BrownianPath} (hP : IsNegativeConditionedBrownianLaw ν P)
    {k n : ℕ} (pastTimes : Fin (k + 1) → NNReal) (futureTimes : Fin n → NNReal)
    (hPastPos : ∀ i, 0 < (pastTimes i : ℝ))
    (hFuturePos : ∀ i, 0 < (futureTimes i : ℝ))
    (hmono : StrictMono (Fin.append pastTimes futureTimes)) :
    P.map (fun p =>
      (fun i => -(p (pastTimes i)), fun j => -(p (futureTimes j))) :
        BrownianPath → (Fin (k + 1) → ℝ) × (Fin n → ℝ)) =
      ((volume : Measure (Fin (k + 1) → ℝ)).withDensity
        (conditionedPositiveFDDVectorDensity ν
          (fun i => (pastTimes i : ℝ)))) ⊗ₘ
        (Kernel.const (Fin (k + 1) → ℝ) (volume : Measure (Fin n → ℝ))).withDensity
          (conditionedPositiveFutureVectorDensity ν
            (fun i => (pastTimes i : ℝ)) (fun i => (futureTimes i : ℝ))) := by
  let totalTimes : Fin ((k + 1) + n) → NNReal := Fin.append pastTimes futureTimes
  let e := conditionedFiniteVectorSplitEquiv (k + 1) n
  let evalTotal : BrownianPath → Fin ((k + 1) + n) → ℝ :=
    fun p i => -(p (totalTimes i))
  let evalPast : BrownianPath → Fin (k + 1) → ℝ :=
    fun p i => -(p (pastTimes i))
  let evalFuture : BrownianPath → Fin n → ℝ :=
    fun p i => -(p (futureTimes i))
  let f : (Fin (k + 1) → ℝ) → ℝ≥0∞ :=
    conditionedPositiveFDDVectorDensity ν (fun i => (pastTimes i : ℝ))
  let g : (Fin (k + 1) → ℝ) → (Fin n → ℝ) → ℝ≥0∞ :=
    conditionedPositiveFutureVectorDensity ν
      (fun i => (pastTimes i : ℝ)) (fun i => (futureTimes i : ℝ))
  have htotalPos : ∀ i, 0 < (totalTimes i : ℝ) := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa [totalTimes] using hPastPos j
    · intro j
      simpa [totalTimes] using hFuturePos j
  have hevalTotal : Measurable evalTotal := by
    apply measurable_pi_iff.mpr
    intro i
    exact (ContinuousMap.measurable_eval (totalTimes i)).neg
  have hfd := negativeConditionedLaw_positiveFDD hP ((k + 1) + n) (by omega)
    totalTimes htotalPos hmono
  have hf : Measurable f := by
    exact measurable_conditionedPositiveFDDVectorDensity ν
      (fun i => (pastTimes i : ℝ))
  have hg : Measurable (Function.uncurry g) := by
    exact measurable_conditionedPositiveFutureVectorDensity ν
      (fun i => (pastTimes i : ℝ)) (fun i => (futureTimes i : ℝ))
  have hgtop : ∀ x y, g x y ≠ ∞ := by
    intro x y
    exact ENNReal.ofReal_ne_top
  have heappend (x : Fin (k + 1) → ℝ) (y : Fin n → ℝ) :
      e (Fin.append x y) = (x, y) :=
    conditionedFiniteVectorSplitEquiv_append (k + 1) n x y
  have heval : evalTotal = fun p => Fin.append (evalPast p) (evalFuture p) := by
    funext p
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simp [evalTotal, evalPast, totalTimes, Fin.append_left]
    · intro j
      simp [evalTotal, evalFuture, totalTimes, Fin.append_right]
  have hmapPair : (fun p => (evalPast p, evalFuture p)) = e ∘ evalTotal := by
    funext p
    rw [heval]
    exact (heappend (evalPast p) (evalFuture p)).symm
  have hPastListTimes : List.ofFn (fun i : Fin (k + 1) => (pastTimes i : ℝ)) =
      (pastTimes 0 : ℝ) :: List.ofFn (fun i : Fin k => (pastTimes i.succ : ℝ)) := by
    exact List.ofFn_succ
  have hPastListValues (x : Fin (k + 1) → ℝ) :
      List.ofFn x = x 0 :: List.ofFn (fun i : Fin k => x i.succ) :=
    List.ofFn_succ
  have hfactor : (fun z : Fin ((k + 1) + n) → ℝ =>
      conditionedPositiveFDDVectorDensity ν
        (fun i => (totalTimes i : ℝ)) z) =
      fun z => f (e z).1 * g (e z).1 (e z).2 := by
    funext z
    let x := (e z).1
    let y := (e z).2
    have hz : z = Fin.append x y := by
      apply e.injective
      simp [x, y, heappend]
    rw [hz]
    have hTimesVec :
        (fun i : Fin ((k + 1) + n) => (totalTimes i : ℝ)) =
          Fin.append (fun i : Fin (k + 1) => (pastTimes i : ℝ))
            (fun i : Fin n => (futureTimes i : ℝ)) := by
      funext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simp [totalTimes, Fin.append_left]
      · intro j
        simp [totalTimes, Fin.append_right]
    have hTimesTotal :
        List.ofFn (fun i : Fin ((k + 1) + n) => (totalTimes i : ℝ)) =
          List.ofFn (fun i : Fin (k + 1) => (pastTimes i : ℝ)) ++
            List.ofFn (fun i : Fin n => (futureTimes i : ℝ)) := by
      rw [hTimesVec, List.ofFn_fin_append]
    have hValuesTotal : List.ofFn (Fin.append x y) = List.ofFn x ++ List.ofFn y :=
      List.ofFn_fin_append x y
    have htailLen :
        (List.ofFn fun i : Fin k => (pastTimes i.succ : ℝ)).length =
          (List.ofFn fun i : Fin k => x i.succ).length := by simp
    have hsplit := conditionedPositiveFDDDensity_append_split ν
      (pastTimes 0 : ℝ) (x 0)
      (List.ofFn fun i : Fin k => (pastTimes i.succ : ℝ))
      (List.ofFn fun i : Fin k => x i.succ)
      (List.ofFn fun i : Fin n => (futureTimes i : ℝ)) (List.ofFn y) htailLen
    have hlastTime := conditionedPositiveLastTime_ofFn_tail
      (fun i : Fin (k + 1) => (pastTimes i : ℝ))
    have hlastState := conditionedPositiveLastState_ofFn_tail x
    have hpastNonneg := conditionedPositiveFDDDensity_nonneg hP.1
      (List.ofFn fun i : Fin (k + 1) => (pastTimes i : ℝ)) (List.ofFn x) (by simp)
    have hpastNonneg' : 0 ≤ conditionedPositiveFDDDensity ν
        ((pastTimes 0 : ℝ) :: List.ofFn (fun i : Fin k => (pastTimes i.succ : ℝ)))
        (x 0 :: List.ofFn (fun i : Fin k => x i.succ)) := by
      rw [← hPastListTimes, ← hPastListValues x]
      exact hpastNonneg
    have hfutureNonneg : 0 ≤ conditionedPositiveTimeChainDensity ν
        (pastTimes (Fin.last k) : ℝ) (x (Fin.last k))
        (List.ofFn fun i : Fin n => (futureTimes i : ℝ)) (List.ofFn y) := by
      exact conditionedPositiveTimeChainDensity_nonneg (t₀ := pastTimes (Fin.last k))
        (x₀ := x (Fin.last k)) hP.1
        (List.ofFn fun i : Fin n => (futureTimes i : ℝ)) (List.ofFn y) (by simp)
    change ENNReal.ofReal (max 0 (conditionedPositiveFDDDensity ν
        (List.ofFn fun i : Fin ((k + 1) + n) => (totalTimes i : ℝ))
        (List.ofFn (Fin.append x y)))) =
      conditionedPositiveFDDVectorDensity ν (fun i => (pastTimes i : ℝ))
          (e (Fin.append x y)).1 *
        conditionedPositiveFutureVectorDensity ν
          (fun i => (pastTimes i : ℝ)) (fun i => (futureTimes i : ℝ))
          (e (Fin.append x y)).1 (e (Fin.append x y)).2
    rw [heappend]
    change ENNReal.ofReal (max 0 (conditionedPositiveFDDDensity ν
        (List.ofFn fun i : Fin ((k + 1) + n) => (totalTimes i : ℝ))
        (List.ofFn (Fin.append x y)))) =
      ENNReal.ofReal (max 0 (conditionedPositiveFDDDensity ν
        (List.ofFn fun i : Fin (k + 1) => (pastTimes i : ℝ)) (List.ofFn x))) *
        ENNReal.ofReal (max 0 (conditionedPositiveTimeChainDensity ν
          (pastTimes (Fin.last k) : ℝ) (x (Fin.last k))
          (List.ofFn fun i : Fin n => (futureTimes i : ℝ)) (List.ofFn y)))
    rw [hTimesTotal, hValuesTotal, hPastListTimes, hPastListValues,
      List.cons_append, List.cons_append]
    rw [hsplit, hlastTime, hlastState]
    rw [max_eq_right (mul_nonneg hpastNonneg' hfutureNonneg),
      max_eq_right hpastNonneg', max_eq_right hfutureNonneg,
      ENNReal.ofReal_mul hpastNonneg']
  calc
    P.map (fun p => (evalPast p, evalFuture p)) = (P.map evalTotal).map e := by
      rw [hmapPair, Measure.map_map e.measurable hevalTotal]
    _ = ((volume : Measure (Fin ((k + 1) + n) → ℝ)).withDensity
          (conditionedPositiveFDDVectorDensity ν
            (fun i => (totalTimes i : ℝ)))).map e := by rw [hfd]; rfl
    _ = ((volume : Measure (Fin (k + 1) → ℝ)).withDensity f) ⊗ₘ
          (Kernel.const (Fin (k + 1) → ℝ) (volume : Measure (Fin n → ℝ))).withDensity g := by
      have hwd := congrArg
        (fun d : (Fin ((k + 1) + n) → ℝ) → ℝ≥0∞ =>
          (volume : Measure (Fin ((k + 1) + n) → ℝ)).withDensity d) hfactor
      have hmapwd := congrArg (fun μ : Measure (Fin ((k + 1) + n) → ℝ) => μ.map e) hwd
      rw [hmapwd]
      exact map_withDensity_conditionedFiniteVectorSplit (k + 1) n f g hf hg hgtop

/-- The two-time positive-coordinate law factors into the entrance density and one Doob
transition density. This is the first finite-dimensional deterministic-time Markov split used
to identify the future kernel. -/
theorem negativeConditionedLaw_twoTime_positiveFDD
    {ν : ℝ} {P : Measure BrownianPath} (hP : IsNegativeConditionedBrownianLaw ν P)
    (t₀ dt : NNReal) (ht₀ : 0 < (t₀ : ℝ)) (hdt : 0 < (dt : ℝ)) :
    P.map (fun p => (-(p t₀), -(p (t₀ + dt)))) =
      (volume : Measure (ℝ × ℝ)).withDensity (fun z =>
        ENNReal.ofReal (max 0 (conditionedPositiveEntranceDensity ν (t₀ : ℝ) z.1 *
          conditionedPositiveTransitionDensity ν (dt : ℝ) z.1 z.2))) := by
  let times : Fin 2 → NNReal := ![t₀, t₀ + dt]
  have htime : ∀ i, 0 < (times i : ℝ) := by
    intro i
    fin_cases i <;> simp only [times]
    · exact ht₀
    · exact add_pos_of_pos_of_nonneg ht₀ dt.2
  have hmono : StrictMono times := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [times]
  have hfd := negativeConditionedLaw_positiveFDD hP 2 (by norm_num) times htime hmono
  let e : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ := MeasurableEquiv.finTwoArrow
  let d : (Fin 2 → ℝ) → ℝ≥0∞ := fun x => ENNReal.ofReal (max 0
    (conditionedPositiveFDDDensity ν (List.ofFn fun i => (times i : ℝ))
      (List.ofFn fun i => x i)))
  have heval : Measurable (fun p : BrownianPath => fun i => -(p (times i))) := by
    apply measurable_pi_iff.mpr
    intro i
    exact (ContinuousMap.measurable_eval (times i)).neg
  have hvol : MeasurePreserving e (volume : Measure (Fin 2 → ℝ)) volume :=
    volume_preserving_finTwoArrow ℝ
  let g : ℝ × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (max 0
    (conditionedPositiveEntranceDensity ν (t₀ : ℝ) z.1 *
      conditionedPositiveTransitionDensity ν (dt : ℝ) z.1 z.2))
  have hg : Measurable g := by
    have hentrance : Measurable (fun z : ℝ × ℝ =>
        conditionedPositiveEntranceDensity ν (t₀ : ℝ) z.1) :=
      (measurable_conditionedPositiveEntranceDensity_arg ν (t₀ : ℝ)).comp measurable_fst
    have htransition : Measurable (fun z : ℝ × ℝ =>
        conditionedPositiveTransitionDensity ν (dt : ℝ) z.1 z.2) :=
      measurable_conditionedPositiveTransitionDensity_pair ν (dt : ℝ)
    exact ENNReal.measurable_ofReal.comp
      (Measurable.max measurable_const (hentrance.mul htransition))
  have hdensity : (fun x : Fin 2 → ℝ => g (e x)) = d := by
    funext x
    have he : e x = (x 0, x 1) := rfl
    have htimesList : List.ofFn (fun i : Fin 2 => (times i : ℝ)) =
        [(t₀ : ℝ), (t₀ : ℝ) + (dt : ℝ)] := by
      simp [times, NNReal.coe_add]
    have hvaluesList : List.ofFn (fun i : Fin 2 => x i) = [x 0, x 1] := by
      simp
    change g (e x) = ENNReal.ofReal (max 0 (conditionedPositiveFDDDensity ν
      (List.ofFn fun i => (times i : ℝ)) (List.ofFn fun i => x i)))
    rw [he, htimesList, hvaluesList]
    change ENNReal.ofReal (max 0 (conditionedPositiveEntranceDensity ν (t₀ : ℝ) (x 0) *
      conditionedPositiveTransitionDensity ν (dt : ℝ) (x 0) (x 1))) = _
    simp [conditionedPositiveFDDDensity, conditionedPositiveTimeChainDensity,
      add_sub_cancel_left]
  have hcomp : (fun p : BrownianPath => (-(p t₀), -(p (t₀ + dt)))) =
      e ∘ (fun p i => -(p (times i))) := by
    funext p
    ext <;> simp [e, times]
  calc
    P.map (fun p => (-(p t₀), -(p (t₀ + dt)))) =
        (P.map (fun p i => -(p (times i)))).map e := by
          rw [Measure.map_map e.measurable heval]
          rw [hcomp]
    _ = ((volume : Measure (Fin 2 → ℝ)).withDensity d).map e := by
          rw [hfd]
    _ = (volume : Measure (ℝ × ℝ)).withDensity (d ∘ e.symm) := by
          exact map_withDensity_of_measurePreserving_equiv e volume volume hvol _
            (hdensity ▸ hg.comp e.measurable)
    _ = (volume : Measure (ℝ × ℝ)).withDensity g := by
          congr 1
          funext z
          have hz := congrFun hdensity (e.symm z)
          simpa using hz.symm

end DOZZ.Proofs

end

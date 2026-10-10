/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitEntranceDensityLimit
public import DOZZ.Brownian.LastExitReferenceKernel

/-!
# Finite projections of the Brownian reference kernel

At positive rational offsets, the explicit Brownian reference future kernel has the finite Doob
density. This identifies the kernel probabilities in the last-exit cell formula with the
measurable entrance-density limit proved separately.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Every finite projection of the reference future kernel is the explicit finite Doob law. -/
theorem brownianUpperConditionedReferenceFutureKernel_finite_projection_doob
    (B : Measure BrownianPath) [SFinite B]
    (hB : IsBrownianReal (fun t p => p t) B)
    (ν t x : ℝ) (hν : 0 < ν) (ht : 0 < t) (hx : 0 < x)
    (n : ℕ) (offsets : Fin n → ℚ)
    (hoff : ∀ i, 0 < (offsets i : ℝ)) (hmono : StrictMono offsets) :
    (brownianUpperConditionedReferenceFutureKernel B ν hν x).map
        (fun y i => y (offsets i)) =
      volume.withDensity (brownianDoobFinitePDF ν n
        (brownianFirstHitElapsed n (fun i => Real.toNNReal (offsets i))) x) := by
  classical
  let ts : Fin n → ℝ≥0 := fun i => Real.toNNReal (offsets i)
  let ds : Fin n → ℝ≥0 := brownianFirstHitElapsed n ts
  have hts0 : ∀ i, 0 < ts i := by
    intro i
    exact Real.toNNReal_pos.mpr (hoff i)
  have htsmono : StrictMono ts := by
    intro i j hij
    rw [← NNReal.coe_lt_coe,
      Real.coe_toNNReal _ (hoff i).le,
      Real.coe_toNNReal _ (hoff j).le]
    exact_mod_cast hmono hij
  have hds : ∀ i, 0 < ds i := by
    intro i
    exact brownianFirstHitElapsed_pos n ts hts0 htsmono i
  have htimes : brownianFirstHitTimes n ds = ts := by
    cases n with
    | zero => funext i; exact Fin.elim0 i
    | succ m => exact brownianFirstHitTimes_elapsed m ts htsmono.monotone
  have htimesReal : (fun i : Fin n => (brownianFirstHitTimes n ds i : ℝ)) =
      fun i => (offsets i : ℝ) := by
    funext i
    have hi := congrFun htimes i
    simpa [ts, Real.coe_toNNReal (offsets i : ℝ) (hoff i).le] using
      congrArg (fun z : ℝ≥0 => (z : ℝ)) hi
  have hpdf : ∀ y : Fin n → ℝ,
      brownianDoobFinitePDF ν n ds x y =
        conditionedPositiveFutureVectorDensity ν
          (fun _ : Fin 1 => t) (fun i => t + (offsets i : ℝ))
          (fun _ => x) y := by
    intro y
    have hchain := brownianDoobFinitePDF_eq_chain_from_elapsed ν 0 x hν n ds hds y
    have htranslate := conditionedPositiveTimeChainDensity_translate ν t 0 x
      (fun i => (offsets i : ℝ)) y
    have hleft : (List.ofFn fun i : Fin n =>
        (0 : ℝ) + (brownianFirstHitTimes n ds i : ℝ)) =
          List.ofFn (fun i => (offsets i : ℝ)) := by
      apply congrArg List.ofFn
      funext i
      simpa using congrFun htimesReal i
    rw [hleft] at hchain
    have htargetNonneg : 0 ≤ conditionedPositiveTimeChainDensity ν t x
        (List.ofFn fun i : Fin n => t + (offsets i : ℝ)) (List.ofFn y) :=
      conditionedPositiveTimeChainDensity_nonneg hν.le _ _ (by simp)
    change brownianDoobFinitePDF ν n ds x y =
      ENNReal.ofReal (max 0 (conditionedPositiveTimeChainDensity ν t x
        (List.ofFn fun i : Fin n => t + (offsets i : ℝ)) (List.ofFn y)))
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
  have hproject : Measurable (fun y : ℚ → ℝ => fun i => y (offsets i)) :=
    measurable_pi_iff.mpr (fun i => measurable_pi_apply (offsets i))
  have hinput : Measurable (fun z : ℝ × (Fin n → ℝ) =>
      ((fun _ : Fin 1 => z.1), z.2)) := by
    apply Measurable.prodMk
    · exact measurable_pi_iff.mpr (fun _ => measurable_fst)
    · exact measurable_snd
  have hD : Measurable (fun z : ℝ × (Fin n → ℝ) =>
      conditionedPositiveFutureVectorDensity ν
        (fun _ : Fin 1 => t) (fun i => t + (offsets i : ℝ))
        (fun _ => z.1) z.2) := by
    exact (measurable_conditionedPositiveFutureVectorDensity ν
      (fun _ : Fin 1 => t) (fun i => t + (offsets i : ℝ))).comp hinput
  have hmeasure :
      volume.withDensity (brownianDoobFinitePDF ν n ds x) =
        volume.withDensity (fun y => conditionedPositiveFutureVectorDensity ν
          (fun _ : Fin 1 => t) (fun i => t + (offsets i : ℝ)) (fun _ => x) y) := by
    congr 1
    funext y
    exact hpdf y
  apply Measure.ext
  intro A hA
  have hproj := brownianUpperConditionedReferenceFutureKernel_finite_projection
    B hB ν t x hν ht hx n offsets hoff hmono A hA
  calc
    ((brownianUpperConditionedReferenceFutureKernel B ν hν x).map
        (fun y i => y (offsets i))) A =
      ((Kernel.const ℝ (volume : Measure (Fin n → ℝ))).withDensity
        (fun z y => conditionedPositiveFutureVectorDensity ν
          (fun _ : Fin 1 => t) (fun i => t + (offsets i : ℝ))
          (fun _ => z) y)) x A := hproj
    _ = (volume.withDensity (fun y => conditionedPositiveFutureVectorDensity ν
          (fun _ : Fin 1 => t) (fun i => t + (offsets i : ℝ))
          (fun _ => x) y)) A := by
      rw [Kernel.withDensity_apply _ hD x, Kernel.const_apply]
    _ = (volume.withDensity (brownianDoobFinitePDF ν n ds x)) A := by
      rw [hmeasure]

/-- Finite rational projections of the Brownian reference future kernel converge on every
measurable event to the conditioned entrance finite-dimensional law as the start decreases to
zero. -/
theorem brownianUpperConditionedReferenceFutureKernel_finite_projection_tendsto_entrance
    (B : Measure BrownianPath) [SFinite B]
    (hB : IsBrownianReal (fun t p => p t) B)
    (Q : Measure BrownianPath) (ν t : ℝ) (hν : 0 < ν)
    (hQ : IsNegativeConditionedBrownianLaw ν Q) (ht : 0 < t)
    (n : ℕ) (offsets : Fin n → ℚ)
    (hoff : ∀ i, 0 < (offsets i : ℝ)) (hmono : StrictMono offsets)
    (xs : ℕ → ℝ) (hxs : ∀ k, 0 < xs k) (hxlim : Tendsto xs atTop (𝓝 0))
    (A : Set (Fin n → ℝ)) (hA : MeasurableSet A) :
    Tendsto
      (fun k => (brownianUpperConditionedReferenceFutureKernel B ν hν (xs k)).map
        (fun y i => y (offsets i)) A)
      atTop
      (𝓝 ((volume.withDensity (brownianEntranceFinitePDF ν n
        (brownianFirstHitElapsed n (fun i => Real.toNNReal (offsets i))))) A)) := by
  let ts : Fin n → ℝ≥0 := fun i => Real.toNNReal (offsets i)
  let ds : Fin n → ℝ≥0 := brownianFirstHitElapsed n ts
  have hts0 : ∀ i, 0 < ts i := by
    intro i
    exact Real.toNNReal_pos.mpr (hoff i)
  have htsmono : StrictMono ts := by
    intro i j hij
    rw [← NNReal.coe_lt_coe,
      Real.coe_toNNReal _ (hoff i).le,
      Real.coe_toNNReal _ (hoff j).le]
    exact_mod_cast hmono hij
  have hds : ∀ i, 0 < ds i := by
    intro i
    exact brownianFirstHitElapsed_pos n ts hts0 htsmono i
  have hlimit := brownianDoobFinitePDF_measure_tendsto_entrance_event
    B Q hB ν hν hQ n ds hds xs hxs hxlim A hA
  have heq (k : ℕ) :
      (brownianUpperConditionedReferenceFutureKernel B ν hν (xs k)).map
          (fun y i => y (offsets i)) =
        volume.withDensity (brownianDoobFinitePDF ν n ds (xs k)) := by
    exact brownianUpperConditionedReferenceFutureKernel_finite_projection_doob
      B hB ν t (xs k) hν ht (hxs k) n offsets hoff hmono
  have hfun : (fun k =>
      (brownianUpperConditionedReferenceFutureKernel B ν hν (xs k)).map
        (fun y i => y (offsets i)) A) =
      fun k => (volume.withDensity (brownianDoobFinitePDF ν n ds (xs k))) A := by
    funext k
    rw [heq k]
  have hdsEq : ds = brownianFirstHitElapsed n
      (fun i => Real.toNNReal (offsets i)) := by
    rfl
  rw [hfun, hdsEq]
  exact hlimit

end DOZZ.Proofs

end

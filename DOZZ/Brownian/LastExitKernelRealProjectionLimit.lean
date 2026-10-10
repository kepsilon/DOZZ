/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitKernelInitial

/-!
# Real-valued finite projection limit of the reference kernel

The entrance-density convergence for the reference kernel is stated in `ℝ≥0∞`. This module
records its real-measure form and the corresponding one-sided filter limit at zero.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- For every measurable finite-dimensional event on positive rational offsets, the real
probability under the reference kernel converges to its entrance probability as the start tends to
zero through positive values. -/
theorem brownianUpperConditionedReferenceFutureKernel_real_projection_tendsto_entrance
    (B : Measure BrownianPath) [SFinite B]
    (hB : IsBrownianReal (fun t p => p t) B)
    (Q : Measure BrownianPath) (ν : ℝ) (hν : 0 < ν)
    (hQ : IsNegativeConditionedBrownianLaw ν Q)
    (n : ℕ) (offsets : Fin n → ℚ)
    (hoff : ∀ i, 0 < (offsets i : ℝ)) (hmono : StrictMono offsets)
    (A : Set (Fin n → ℝ)) (hA : MeasurableSet A) :
    Tendsto
      (fun z => (brownianUpperConditionedReferenceFutureKernel B ν hν z).real
        {y | (fun i => y (offsets i)) ∈ A})
      (𝓝[>] (0 : ℝ))
      (𝓝 ((volume.withDensity (brownianEntranceFinitePDF ν n
        (brownianFirstHitElapsed n (fun i => Real.toNNReal (offsets i))))) A).toReal) := by
  classical
  let project : (ℚ → ℝ) → (Fin n → ℝ) := fun y i => y (offsets i)
  let C : Set (ℚ → ℝ) := project ⁻¹' A
  have hproject : Measurable project :=
    measurable_pi_iff.mpr (fun i => measurable_pi_apply (offsets i))
  have hC : MeasurableSet C := hA.preimage hproject
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
  let M : Measure (Fin n → ℝ) := volume.withDensity
    (brownianEntranceFinitePDF ν n ds)
  have hMprob : IsProbabilityMeasure M := by
    refine ⟨?_⟩
    change (volume.withDensity (brownianEntranceFinitePDF ν n ds)) Set.univ = 1
    rw [withDensity_apply _ MeasurableSet.univ]
    simpa only [setLIntegral_univ] using
      lintegral_brownianEntranceFinitePDF_one Q ν hν hQ n ds hds
  have hMfinite : M A ≠ ∞ := measure_ne_top M A
  rw [Filter.tendsto_iff_seq_tendsto]
  intro xs hxs
  rcases tendsto_nhdsWithin_iff.mp hxs with ⟨hxlim, hxpos⟩
  let ys : ℕ → ℝ := fun k => if 0 < xs k then xs k else 1
  have hyspos : ∀ k, 0 < ys k := by
    intro k
    by_cases hk : 0 < xs k <;> simp [ys, hk]
  have hysEq : (fun k => ys k) =ᶠ[atTop] xs := by
    filter_upwards [hxpos] with k hk
    have hk' : 0 < xs k := hk
    simp [ys, hk']
  have hyslim : Tendsto ys atTop (𝓝 0) := hxlim.congr' hysEq.symm
  have hkernel := brownianUpperConditionedReferenceFutureKernel_finite_projection_tendsto_entrance
    B hB Q ν 1 hν hQ (by norm_num) n offsets hoff hmono ys hyspos hyslim A hA
  have hreal := (ENNReal.continuousAt_toReal hMfinite).tendsto.comp hkernel
  have hfun : (fun k =>
      (brownianUpperConditionedReferenceFutureKernel B ν hν (ys k)).real C) =
      fun k => ((brownianUpperConditionedReferenceFutureKernel B ν hν (ys k)).map
        project A).toReal := by
    funext k
    rw [measureReal_def, Measure.map_apply hproject hA]
  have hreal' : Tendsto
      (fun k => (brownianUpperConditionedReferenceFutureKernel B ν hν (ys k)).real C)
      atTop (𝓝 (M A).toReal) := by
    simpa [M] using hfun ▸ hreal
  have hxy : (fun k =>
      (brownianUpperConditionedReferenceFutureKernel B ν hν (xs k)).real C) =ᶠ[atTop]
      fun k => (brownianUpperConditionedReferenceFutureKernel B ν hν (ys k)).real C := by
    filter_upwards [hxpos] with k hk
    have hk' : 0 < xs k := hk
    simp [ys, hk']
  have hseq := hreal'.congr' hxy.symm
  change Tendsto
    (fun k => (brownianUpperConditionedReferenceFutureKernel B ν hν (xs k)).real C)
    atTop (𝓝 (M A).toReal)
  exact hseq

end DOZZ.Proofs

end

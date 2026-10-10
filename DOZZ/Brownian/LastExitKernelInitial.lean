/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.LastExitDyadicEndpointTail

/-!
# Initial coordinate of the reference entrance kernel

The reference kernel is a conditioned Brownian path reflected from its prescribed initial state.
Its rational evaluation at zero is therefore deterministic. This identifies the endpoint-tail test
in the dyadic cell formula with its state-space tail.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace DOZZ.Proofs

/-- The reference kernel's time-zero coordinate is its starting state, in the sense of measures. -/
theorem brownianUpperConditionedReferenceFutureKernel_real_initialIci
    (B : Measure BrownianPath) [SFinite B]
    (hB : IsBrownianReal (fun t p => p t) B)
    (ν z δ : ℝ) (hν : 0 < ν) (hz : 0 < z) :
    (brownianUpperConditionedReferenceFutureKernel B ν hν z).real
      {y | δ ≤ y 0} = if δ ≤ z then 1 else 0 := by
  let K := brownianUpperConditionedReferenceFutureKernel B ν hν z
  have : IsProbabilityMeasure (brownianBelowConditionedLaw B ν z) :=
    isProbabilityMeasure_brownianBelowConditionedLaw B hB ν z hν hz
  have : IsProbabilityMeasure K := by
    dsimp [K]
    rw [brownianUpperConditionedReferenceFutureKernel_apply_conditioned B ν z hν hz]
    infer_instance
  have hzero : ∀ᵐ y ∂K, y 0 = z := by
    simpa [K] using brownianUpperConditionedReferenceFutureKernel_eval_zero_ae
      B hB ν z hν hz
  by_cases hδz : δ ≤ z
  · have hset : {y : ℚ → ℝ | δ ≤ y 0} =ᵐ[K] Set.univ := by
      filter_upwards [hzero] with y hy
      simp [hy, hδz]
    have hm : K {y : ℚ → ℝ | δ ≤ y 0} = K Set.univ := measure_congr hset
    rw [measureReal_def, hm]
    simp [hδz]
  · have hset : {y : ℚ → ℝ | δ ≤ y 0} =ᵐ[K] (∅ : Set (ℚ → ℝ)) := by
      filter_upwards [hzero] with y hy
      simp [hy, hδz]
    have hm : K {y : ℚ → ℝ | δ ≤ y 0} = 0 := by
      rw [measure_congr hset]
      simp
    rw [measureReal_def, hm]
    simp [hδz]

end DOZZ.Proofs

end

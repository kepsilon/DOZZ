/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.Construction.GMCRootedIdentity
public import DOZZ.GFFStructure.CircleCovariance
public import DOZZ.GMC.CirclePotential

/-! Point-root covariance is the small-radius limit of the circle-root covariance. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped Distributions

namespace DOZZ.Proofs

/-- As the circle shrinks to its center, its covariance with a smooth test converges to the
point-root covariance used in the rooted GMC identity. -/
theorem circleCross_tendsto_gffRootCovariance
    (u : ℂ) (f : TestFn) :
    Tendsto (fun r : ℝ => circleCross u r f) atTop
      (𝓝 (gffRootCovariance u f)) := by
  let k : ℂ → ℝ := fun z => gffRootCovariance z f
  have hk : Continuous k := gffRootCovariance_continuous f
  have hcross (r : ℝ) : circleCross u r f =
      ∫ z, k z ∂circleMeasure u r := by
    rw [circleCross_eq_integral_testKernel]
    apply integral_congr_ae
    filter_upwards with z
    rfl
  have haverage (r : ℝ) : (∫ z, k z ∂circleMeasure u r) =
      Real.circleAverage k u (Real.exp (-r)) := by
    exact CirclePotential.integral_circleMeasure_eq_circleAverage hk.measurable u r
  have hexp : Tendsto (fun r : ℝ => Real.exp (-r)) atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero
  have havg : Tendsto (fun r : ℝ => Real.circleAverage k u (Real.exp (-r))) atTop
      (𝓝 (Real.circleAverage k u 0)) := by
    exact (Real.Continuous.circleAverage hk).continuousAt.tendsto.comp hexp
  have hzero : Real.circleAverage k u 0 = k u := by simp [k]
  simpa [k, hcross, haverage, hzero] using havg


end DOZZ.Proofs

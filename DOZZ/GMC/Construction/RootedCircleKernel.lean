/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-/
module

public import DOZZ.GMC.Construction.RootedCovarianceLimit

/-! Convergence and domination for a single-circle root potential. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped Distributions

namespace DOZZ.Proofs

/-- A shrinking circle potential approaches the point potential away from the root. -/
theorem circleRootPotential_tendsto (u x : ℂ) (hxu : x ≠ u) :
    Tendsto (fun r : ℝ => ∫ v, gffKernel x v ∂circleMeasure u r) atTop
      (𝓝 (gffKernel u x)) := by
  rw [gffKernel_comm u x]
  let k : ℂ → ℝ := fun z => Real.log (normPlus z)
  have hk : Continuous k := continuous_log_normPlus
  have haverage (r : ℝ) : (∫ v, k v ∂circleMeasure u r) =
      Real.circleAverage k u (Real.exp (-r)) :=
    CirclePotential.integral_circleMeasure_eq_circleAverage hk.measurable u r
  have hexp : Tendsto (fun r : ℝ => Real.exp (-r)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have havg : Tendsto (fun r : ℝ => ∫ v, k v ∂circleMeasure u r) atTop
      (𝓝 (k u)) := by
    have h : Tendsto (fun r : ℝ => Real.circleAverage k u (Real.exp (-r))) atTop
        (𝓝 (Real.circleAverage k u 0)) :=
      (Real.Continuous.circleAverage hk).continuousAt.tendsto.comp hexp
    simpa only [← haverage, Real.circleAverage_zero] using h
  have hd : 0 < ‖u - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxu.symm)
  have hevent : ∀ᶠ r : ℝ in atTop, Real.exp (-r) ≤ ‖u - x‖ :=
    (hexp.eventually (Iio_mem_nhds hd)).mono fun _ h => h.le
  have hlim := (tendsto_const_nhds : Tendsto
    (fun _ : ℝ => -Real.log ‖u - x‖ + Real.log (normPlus x)) atTop
      (𝓝 (-Real.log ‖u - x‖ + Real.log (normPlus x)))).add havg
  have heq : (fun r : ℝ => ∫ v, gffKernel x v ∂circleMeasure u r) =ᶠ[atTop]
      fun r => -Real.log ‖u - x‖ + Real.log (normPlus x) +
        ∫ v, k v ∂circleMeasure u r := by
    filter_upwards [hevent] with r hr
    rw [integral_gffKernel_circleMeasure, max_eq_right hr]
  have ht := hlim.congr' heq.symm
  simpa only [k, gffKernel, norm_sub_rev u] using ht

/-- At nonnegative logarithmic scales, a circle root potential is bounded by the singular
point potential plus a universal pinning correction. -/
theorem circleRootPotential_le_point_add_log_two
    (u x : ℂ) (r : ℝ) (hr : 0 ≤ r) (hxu : x ≠ u) :
    (∫ v, gffKernel x v ∂circleMeasure u r) ≤ gffKernel u x + Real.log 2 := by
  let _ := circleMeasure_isProbability u r
  have hrad : Real.exp (-r) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hr)
  have hplus : ∀ᵐ v ∂circleMeasure u r,
      Real.log (normPlus v) ≤ Real.log 2 + Real.log (normPlus u) := by
    filter_upwards [ae_mem_sphere_circleMeasure u r] with v hv
    have hdist : ‖v - u‖ = Real.exp (-r) := by
      simpa only [Metric.mem_sphere, dist_eq_norm] using hv
    have hnorm : ‖v‖ ≤ Real.exp (-r) + ‖u‖ := by
      calc
        ‖v‖ = ‖(v - u) + u‖ := by rw [sub_add_cancel]
        _ ≤ ‖v - u‖ + ‖u‖ := norm_add_le _ _
        _ = _ := by rw [hdist]
    have hu1 : 1 ≤ normPlus u := le_max_left _ _
    have hun : ‖u‖ ≤ normPlus u := le_max_right _ _
    have hvbound : normPlus v ≤ 2 * normPlus u := by
      unfold normPlus
      apply max_le
      · change 1 ≤ 2 * normPlus u
        linarith
      · change ‖v‖ ≤ 2 * normPlus u
        linarith
    have hulog : Real.log (2 * normPlus u) = Real.log 2 + Real.log (normPlus u) :=
      Real.log_mul (by norm_num) (ne_of_gt (lt_of_lt_of_le zero_lt_one hu1))
    exact (Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hvbound).trans_eq
      hulog
  have hpin : (∫ v, Real.log (normPlus v) ∂circleMeasure u r) ≤
      Real.log 2 + Real.log (normPlus u) := by
    have h := integral_mono_ae (integrable_log_normPlus_circleMeasure u r)
      (integrable_const (Real.log 2 + Real.log (normPlus u))) hplus
    simpa using h
  have hd : 0 < ‖u - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxu.symm)
  have hlog : Real.log ‖u - x‖ ≤ Real.log (max (Real.exp (-r)) ‖u - x‖) :=
    Real.log_le_log hd (le_max_right _ _)
  rw [integral_gffKernel_circleMeasure, gffKernel]
  linarith

end DOZZ.Proofs

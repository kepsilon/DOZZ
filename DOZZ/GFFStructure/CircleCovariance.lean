/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFFStructure.GaussianClosure
public import DOZZ.GFFStructure.CircleLogSeries

/-!
# Identification of circle covariances

Absolute logarithmic section bounds justify the mixed planar/arclength Fubini exchange.
The smooth energy and weak limits then identify the covariances of the given witness.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory Set Metric
open scoped Topology ENNReal NNReal Interval

namespace DOZZ.Proofs

/-- Absolute logarithmic sections have a uniform bound for poles in a fixed planar ball. -/
theorem integral_abs_log_circle_le (x z : ℂ) (r R : ℝ) (hz : ‖z‖ ≤ R) :
    (∫ w, |Real.log ‖z - w‖| ∂circleMeasure x r) ≤
      2 * Real.log (max 1 (R + ‖x‖ + Real.exp (-r))) + r := by
  let _ := circleMeasure_isProbability x r
  let L := Real.log (max 1 (R + ‖x‖ + Real.exp (-r)))
  have hL : 0 ≤ L := Real.log_nonneg (le_max_left _ _)
  have hi : Integrable (fun w => Real.log ‖z - w‖) (circleMeasure x r) := by
    simpa only [norm_sub_rev z] using integrable_log_norm_sub_circleMeasure x z r
  have hup : ∀ᵐ w ∂circleMeasure x r, |Real.log ‖z - w‖| ≤ 2 * L - Real.log ‖z - w‖ := by
    filter_upwards [ae_norm_sub_center_circleMeasure x r] with w hw
    have hwbound : ‖w‖ ≤ ‖x‖ + Real.exp (-r) := by
      calc
        ‖w‖ = ‖(w - x) + x‖ := by rw [sub_add_cancel]
        _ ≤ ‖w - x‖ + ‖x‖ := norm_add_le _ _
        _ = _ := by rw [hw]; ring
    have hd : ‖z - w‖ ≤ max 1 (R + ‖x‖ + Real.exp (-r)) := by
      exact (norm_sub_le _ _).trans ((add_le_add hz hwbound).trans
        (by simpa only [add_assoc] using le_max_right 1 (R + ‖x‖ + Real.exp (-r))))
    have hlog : Real.log ‖z - w‖ ≤ L := by
      by_cases hzero : ‖z - w‖ = 0
      · simpa only [hzero, Real.log_zero] using hL
      · exact Real.log_le_log (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)) hd
    rcases le_total 0 (Real.log ‖z - w‖) with h | h
    · rw [abs_of_nonneg h]
      linarith
    · rw [abs_of_nonpos h]
      linarith
  have hbound := integral_mono_ae hi.norm ((integrable_const (2 * L)).sub hi) hup
  have hsub := integral_sub (integrable_const (2 * L)) hi
  simp only [Pi.sub_apply, Real.norm_eq_abs] at hbound
  rw [hsub, integral_const, probReal_univ, one_smul,
    integral_log_norm_rev_sub_circleMeasure] at hbound
  have hlow := Real.log_le_log (Real.exp_pos (-r)) (le_max_left (Real.exp (-r)) ‖x - z‖)
  rw [Real.log_exp] at hlow
  change _ ≤ 2 * L + r
  linarith

/-- The pinned section has a uniform absolute-integral bound on any bounded set of poles. -/
theorem integral_abs_gffKernel_circle_le (x z : ℂ) (r R : ℝ) (hz : ‖z‖ ≤ R) :
    (∫ w, |gffKernel z w| ∂circleMeasure x r) ≤
      2 * Real.log (max 1 (R + ‖x‖ + Real.exp (-r))) + r +
        Real.log (max 1 R) + (∫ w, Real.log (normPlus w) ∂circleMeasure x r) := by
  let _ := circleMeasure_isProbability x r
  have hlog : Integrable (fun w => Real.log ‖z - w‖) (circleMeasure x r) := by
    simpa only [norm_sub_rev z] using integrable_log_norm_sub_circleMeasure x z r
  have hpin := integrable_log_normPlus_circleMeasure x r
  have hzc : Integrable (fun _ : ℂ => Real.log (normPlus z)) (circleMeasure x r) := integrable_const _
  have hznon : 0 ≤ Real.log (normPlus z) := Real.log_nonneg (le_max_left _ _)
  have hpoint w : |gffKernel z w| ≤ |Real.log ‖z - w‖| + Real.log (normPlus z) +
      Real.log (normPlus w) := by
    have hwnon : 0 ≤ Real.log (normPlus w) := Real.log_nonneg (le_max_left _ _)
    unfold gffKernel
    calc
      _ ≤ |-Real.log ‖z - w‖ + Real.log (normPlus z)| + |Real.log (normPlus w)| := abs_add_le _ _
      _ ≤ (|-Real.log ‖z - w‖| + |Real.log (normPlus z)|) + |Real.log (normPlus w)| :=
        add_le_add (abs_add_le _ _) le_rfl
      _ = _ := by rw [abs_neg, abs_of_nonneg hznon, abs_of_nonneg hwnon]
  have hbound := integral_mono_ae (integrable_gffKernel_circleMeasure x z r).norm
    ((hlog.norm.add hzc).add hpin) (Filter.Eventually.of_forall hpoint)
  have hfirst := integral_add hlog.norm hzc
  have hsecond := integral_add (hlog.norm.add hzc) hpin
  simp only [Pi.add_apply, Real.norm_eq_abs] at hfirst hsecond hbound
  rw [hsecond, hfirst, integral_const, probReal_univ, one_smul] at hbound
  have hzlog : Real.log (normPlus z) ≤ Real.log (max 1 R) := by
    apply Real.log_le_log (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    exact max_le_max le_rfl hz
  have hraw := integral_abs_log_circle_le x z r R hz
  linarith

/-- A smooth compact test times the circle kernel is absolutely product-integrable. -/
theorem integrable_test_circleKernel (x : ℂ) (r : ℝ) (f : TestFn) :
    Integrable (fun p : ℂ × ℂ => f p.1 * gffKernel p.1 p.2)
      ((volume : Measure ℂ).prod (circleMeasure x r)) := by
  let _ := circleMeasure_isProbability x r
  obtain ⟨R, _, hR⟩ := f.hasCompactSupport.isBounded.exists_pos_norm_le
  let C := 2 * Real.log (max 1 (R + ‖x‖ + Real.exp (-r))) + r +
    Real.log (max 1 R) + (∫ w, Real.log (normPlus w) ∂circleMeasure x r)
  have hm : Measurable (fun p : ℂ × ℂ => f p.1 * gffKernel p.1 p.2) := by
    fun_prop [gffKernel, normPlus]
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun z =>
    (integrable_gffKernel_circleMeasure x z r).const_mul (f z)), ?_⟩
  have hfi : Integrable f (volume : Measure ℂ) := f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  apply (hfi.norm.mul_const |C|).mono' hm.norm.aestronglyMeasurable.integral_prod_right'
  filter_upwards with z
  have hnon : 0 ≤ ∫ w, ‖f z * gffKernel z w‖ ∂circleMeasure x r :=
    integral_nonneg (fun _ => norm_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnon]
  by_cases hz : f z = 0
  · simp [hz]
  · have hzR : ‖z‖ ≤ R := hR z (subset_tsupport f hz)
    have hb := integral_abs_gffKernel_circle_le x z r R hzR
    calc
      _ = |f z| * (∫ w, |gffKernel z w| ∂circleMeasure x r) := by
        simp_rw [norm_mul, Real.norm_eq_abs]
        rw [integral_const_mul]
      _ ≤ |f z| * |C| := mul_le_mul_of_nonneg_left (hb.trans (le_abs_self C)) (abs_nonneg _)
      _ = ‖f z‖ * |C| := by rw [Real.norm_eq_abs]

/-- The pinned kernel is symmetric, including on its diagonal. -/
theorem gffKernel_comm (z w : ℂ) : gffKernel z w = gffKernel w z := by
  unfold gffKernel
  rw [norm_sub_rev]
  ring

/-- Absolute integrability identifies the two mixed circle/test energy orders. -/
theorem circleCross_eq_integral_testKernel (x : ℂ) (r : ℝ) (f : TestFn) :
    circleCross x r f = ∫ w, ∫ z, gffKernel w z * f z ∂volume ∂circleMeasure x r := by
  let _ := circleMeasure_isProbability x r
  have hi := integrable_test_circleKernel x r f
  unfold circleCross
  calc
    _ = ∫ z, ∫ w, f z * gffKernel z w ∂circleMeasure x r := by simp_rw [integral_const_mul]
    _ = ∫ w, ∫ z, f z * gffKernel z w ∂volume ∂circleMeasure x r := integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with w
      apply integral_congr_ae
      filter_upwards with z
      rw [gffKernel_comm z w, mul_comm]

/-- The test covariance is integration of the continuous test potential against the first test. -/
theorem gffCov_eq_integral_testKernel (f g : TestFn) :
    gffCov f g = ∫ z, f z * (∫ w, gffKernel z w * g w) := by
  unfold gffCov
  simp_rw [← integral_const_mul]
  congr 1
  funext z
  congr 1
  funext w
  ring

/-- Every mixed circle/test covariance is the mixed energy `DOZZ.circleCross`, on the given
probability space and for the original distribution-valued realization. -/
theorem circleAverage_test_covariance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (x : ℂ) (r : ℝ) (g : TestFn) :
    covariance (fun ω => Xc ω x r) (fun ω => X ω g) P = circleCross x r g := by
  let _ := hX.1
  obtain ⟨f, hg, hw⟩ := exists_testFn_circleEnergyGap_and_integral_tendsto x r
  have hweak := hw _ (continuous_testKernelPotential g)
  simp_rw [← gffCov_eq_integral_testKernel] at hweak
  have hzero : Tendsto (fun _ : ℕ => eLpNorm (fun ω => X ω g - X ω g) 2 P) atTop (𝓝 0) := by
    simpa only [sub_self, ← Pi.zero_def, eLpNorm_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
  have hcov := tendsto_covariance_of_eLpNorm_sub
    (fun n => equatorGFF_test_memLp X hX (f n)) (fun _ => equatorGFF_test_memLp X hX g)
    (hc.2.1 x r) (equatorGFF_test_memLp X hX g) (hc.2.2 x r f hg) hzero
  simp_rw [equatorGFF_test_covariance X hX] at hcov
  rw [circleCross_eq_integral_testKernel]
  exact tendsto_nhds_unique hcov hweak

/-- All circle/circle covariances are the double-circle kernel energy, before evaluation of
its intersecting-circle Fourier series. -/
theorem circleAverage_covariance_integral {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (x y : ℂ) (r s : ℝ) :
    covariance (fun ω => Xc ω x r) (fun ω => Xc ω y s) P =
      ∫ z, ∫ w, gffKernel z w ∂circleMeasure y s ∂circleMeasure x r := by
  let _ := hX.1
  obtain ⟨f, hg, hcross⟩ := exists_testFn_circleEnergyGap_and_cross_tendsto x r
  have hzero : Tendsto (fun _ : ℕ => eLpNorm (fun ω => Xc ω y s - Xc ω y s) 2 P) atTop (𝓝 0) := by
    simpa only [sub_self, ← Pi.zero_def, eLpNorm_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 0))
  have hl := tendsto_covariance_of_eLpNorm_sub
    (fun n => equatorGFF_test_memLp X hX (f n)) (fun _ => hc.2.1 y s)
    (hc.2.1 x r) (hc.2.1 y s) (hc.2.2 x r f hg) hzero
  have hval n : covariance (fun ω => X ω (f n)) (fun ω => Xc ω y s) P = circleCross y s (f n) := by
    rw [covariance_comm]
    exact circleAverage_test_covariance P X Xc hX hc y s (f n)
  simp_rw [hval] at hl
  exact tendsto_nhds_unique hl (hcross y s)

/-- Inner origin circles are orthogonal to tests supported outside the unit disk. -/
theorem circleCross_origin_exterior_eq_zero {r : ℝ} (hr : 0 ≤ r) (f : TestFn)
    (hs : tsupport f ⊆ {w : ℂ | 1 ≤ ‖w‖}) : circleCross 0 r f = 0 := by
  unfold circleCross
  simp_rw [integral_gffKernel_circleMeasure]
  rw [integral_log_normPlus_circleMeasure_origin_eq_max, max_eq_left (neg_nonpos.mpr hr)]
  apply integral_eq_zero_of_ae
  filter_upwards with z
  by_cases hz : f z = 0
  · simp [hz]
  · have hn : 1 ≤ ‖z‖ := hs (subset_tsupport f hz)
    have he : Real.exp (-r) ≤ ‖z‖ := (exp_neg_le_one hr).trans hn
    simp only [zero_sub, norm_neg, Pi.zero_apply, max_eq_right he, normPlus, max_eq_right hn, neg_add_cancel,
      add_zero, mul_zero]

/-- Two independent radial finite-dimensional Brownian laws for every witness, and the inner path
independent of the exterior field on `{‖w‖ ≥ 1}` ([KRV, Remark 2.2]); used in [KRV, §10.2]. -/
theorem circleAverage_origin_preBrownian {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) :
    IsPreBrownianReal (fun t : ℝ≥0 => fun ω => Xc ω 0 t) P ∧
    IsPreBrownianReal (fun t : ℝ≥0 => fun ω => Xc ω 0 (-(t : ℝ))) P ∧
    IndepFun (fun ω => fun t : ℝ≥0 => Xc ω 0 t)
      (fun ω => fun t : ℝ≥0 => Xc ω 0 (-(t : ℝ))) P ∧
    IndepFun (fun ω => fun t : ℝ≥0 => Xc ω 0 t)
      (fun ω => fun f : {f : TestFn // tsupport f ⊆ {w : ℂ | 1 ≤ ‖w‖}} => X ω f.val) P := by
  let _ := hX.1
  have hG := (circleAverage_isGaussianProcess P X Xc hX hc).1
  have hmean := (circleAverage_isGaussianProcess P X Xc hX hc).2
  have hin : IsGaussianProcess (fun t : ℝ≥0 => fun ω => Xc ω 0 t) P := by
    simpa only [Function.comp_def] using hG.comp_right (fun t : ℝ≥0 => ((0 : ℂ), (t : ℝ)))
  have hout : IsGaussianProcess (fun t : ℝ≥0 => fun ω => Xc ω 0 (-(t : ℝ))) P := by
    simpa only [Function.comp_def] using hG.comp_right (fun t : ℝ≥0 => ((0 : ℂ), -(t : ℝ)))
  refine ⟨preBrownian_of_gaussian_min_covariance _ hin (fun t => hmean 0 t) ?_,
    preBrownian_of_gaussian_min_covariance _ hout (fun t => hmean 0 (-(t : ℝ))) ?_, ?_, ?_⟩
  · intro t u
    rw [circleAverage_covariance_integral P X Xc hX hc,
      integral_integral_gffKernel_origin_nonneg t.coe_nonneg u.coe_nonneg]
  · intro t u
    rw [circleAverage_covariance_integral P X Xc hX hc,
      integral_integral_gffKernel_origin_nonpos t.coe_nonneg u.coe_nonneg]
  · have hboth : IsGaussianProcess
        (Sum.elim (fun t : ℝ≥0 => fun ω => Xc ω 0 t)
          (fun t : ℝ≥0 => fun ω => Xc ω 0 (-(t : ℝ)))) P := by
      convert hG.comp_right (Sum.elim
        (fun t : ℝ≥0 => ((0 : ℂ), (t : ℝ)))
        (fun t : ℝ≥0 => ((0 : ℂ), -(t : ℝ)))) using 1
      funext q
      cases q <;> rfl
    apply hboth.indepFun_of_covariance_eq_zero
      (fun t => (hc.2.1 0 t).aemeasurable)
      (fun t => (hc.2.1 0 (-(t : ℝ))).aemeasurable)
    intro t u
    rw [circleAverage_covariance_integral P X Xc hX hc,
      integral_integral_gffKernel_origin_cross t.coe_nonneg u.coe_nonneg]
  · let E := {f : TestFn // tsupport f ⊆ {w : ℂ | 1 ≤ ‖w‖}}
    have hboth : IsGaussianProcess
        (Sum.elim (fun t : ℝ≥0 => fun ω => Xc ω 0 t)
          (fun f : E => fun ω => X ω f.val)) P := by
      convert (circleAverage_tests_isGaussianProcess X Xc hX hc).comp_right
        (Sum.elim (fun t : ℝ≥0 => Sum.inl ((0 : ℂ), (t : ℝ)))
          (fun f : E => Sum.inr f.val)) using 1
      funext q
      cases q <;> rfl
    apply hboth.indepFun_of_covariance_eq_zero
      (fun t => (hc.2.1 0 t).aemeasurable)
      (fun f => (equatorGFF_test_memLp X hX f.val).aemeasurable)
    intro t f
    rw [circleAverage_test_covariance P X Xc hX hc,
      circleCross_origin_exterior_eq_zero t.coe_nonneg f.val f.property]

/-- On a continuous witness the two radial processes are Brownian paths ([KRV, Remark 2.2]). Use
`exists_continuous_circleAverage` for arbitrary witnesses. -/
theorem circleAverage_origin_brownian {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2)) :
    IsBrownianReal (fun t : ℝ≥0 => fun ω => Xc ω 0 t) P ∧
    IsBrownianReal (fun t : ℝ≥0 => fun ω => Xc ω 0 (-(t : ℝ))) P := by
  have hpre := circleAverage_origin_preBrownian P X Xc hX hc
  exact ⟨brownian_of_preBrownian_circle_path Xc
      (fun t : ℝ≥0 => ((0 : ℂ), (t : ℝ))) (by fun_prop) hpre.1 hcont,
    brownian_of_preBrownian_circle_path Xc
      (fun t : ℝ≥0 => ((0 : ℂ), -(t : ℝ))) (by fun_prop) hpre.2.1 hcont⟩

/-- The elementary exterior-center covariance is valid for the actual witness. -/
theorem circleAverage_covariance_exterior {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (x : ℂ) (hx : 2 ≤ ‖x‖) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    covariance (fun ω => Xc ω x r) (fun ω => Xc ω x s) P = min r s + 2 * Real.log ‖x‖ := by
  let _ := circleMeasure_isProbability x r
  have hpR := integral_log_normPlus_circleMeasure_exterior
    ((add_le_add le_rfl (exp_neg_le_one hr)).trans (by simpa only [one_add_one_eq_two] using hx))
  have hpS := integral_log_normPlus_circleMeasure_exterior
    ((add_le_add le_rfl (exp_neg_le_one hs)).trans (by simpa only [one_add_one_eq_two] using hx))
  rw [circleAverage_covariance_integral P X Xc hX hc]
  simp_rw [integral_gffKernel_circleMeasure, hpS]
  have heq : (fun z : ℂ => -Real.log (max (Real.exp (-s)) ‖x - z‖) +
      Real.log (normPlus z) + Real.log ‖x‖) =ᵐ[circleMeasure x r]
      fun z => -Real.log (max (Real.exp (-s)) (Real.exp (-r))) +
        Real.log (normPlus z) + Real.log ‖x‖ := by
    filter_upwards [ae_norm_sub_center_circleMeasure x r] with z hz
    rw [norm_sub_rev, hz]
  rw [integral_congr_ae heq]
  have hpin := integrable_log_normPlus_circleMeasure x r
  have hfirst := integral_add (integrable_const (-Real.log (max (Real.exp (-s)) (Real.exp (-r))))) hpin
  have hsecond := integral_add
    ((integrable_const (-Real.log (max (Real.exp (-s)) (Real.exp (-r))))).add hpin)
    (integrable_const (Real.log ‖x‖))
  simp only [Pi.add_apply] at hfirst hsecond
  rw [hsecond, hfirst, integral_const, integral_const, probReal_univ, one_smul, one_smul, hpR]
  have hraw := integral_integral_log_norm_concentric_eq_neg_min x s r
  rw [integral_integral_log_norm_concentric, min_comm] at hraw
  rw [hraw]
  ring

/-- Continuous-witness path upgrade of [KRV, Remark 2.2]. -/
theorem circleAverage_exterior_brownian {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (c : ℂ) (hout : 2 ≤ ‖c‖) :
    IsBrownianReal (fun t : ℝ≥0 => fun ω => Xc ω c t - Xc ω c 0) P := by
  let _ := hX.1
  have hG := (circleAverage_isGaussianProcess P X Xc hX hc).1
  have hmean := (circleAverage_isGaussianProcess P X Xc hX hc).2
  have hGc : IsGaussianProcess (fun t : ℝ≥0 => fun ω => Xc ω c t) P := by
    simpa only [Function.comp_def] using hG.comp_right (fun t : ℝ≥0 => (c, (t : ℝ)))
  have hpre : IsPreBrownianReal (fun t : ℝ≥0 => fun ω => Xc ω c t - Xc ω c 0) P := by
    apply preBrownian_of_gaussian_min_covariance _ (isGaussianProcess_sub_fixed hGc 0)
    · intro t
      simp only [NNReal.coe_zero]
      rw [integral_sub ((hc.2.1 c t).integrable (by norm_num)) ((hc.2.1 c 0).integrable (by norm_num)), hmean, hmean, sub_self]
    · intro t u
      simp only [NNReal.coe_zero]
      have hcov := covariance_fun_sub_fun_sub (hc.2.1 c t) (hc.2.1 c 0) (hc.2.1 c u) (hc.2.1 c 0)
      rw [hcov, circleAverage_covariance_exterior P X Xc hX hc c hout t.coe_nonneg u.coe_nonneg,
        circleAverage_covariance_exterior P X Xc hX hc c hout t.coe_nonneg le_rfl,
        circleAverage_covariance_exterior P X Xc hX hc c hout le_rfl u.coe_nonneg,
        circleAverage_covariance_exterior P X Xc hX hc c hout le_rfl le_rfl,
        min_eq_right t.coe_nonneg, min_eq_left u.coe_nonneg, min_self]
      ring
  exact brownian_of_preBrownian_circle_increment_path Xc
    (fun t : ℝ≥0 => (c, (t : ℝ))) (c, 0) (by fun_prop) hpre hcont

/-- Subtracting a continuous separable pinning potential commutes with the test pairing. -/
theorem gffCov_sub_potential_integral (f g : TestFn) (p : ℂ → ℝ) (hp : Continuous p) (C : ℝ) :
    gffCov f g - (∫ z, f z * p z) * (∫ z, g z) -
      (∫ z, f z) * (∫ z, g z * p z) + (∫ z, f z) * (∫ z, g z) * C =
      ∫ z, f z * (∫ w, (gffKernel z w - p z - p w + C) * g w) := by
  have hgi : Integrable g (volume : Measure ℂ) := g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport
  have hfi : Integrable f (volume : Measure ℂ) := f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hgp : Integrable (fun w => p w * g w) :=
    (hp.mul g.continuous).integrable_of_hasCompactSupport g.hasCompactSupport.mul_left
  have hfp : Integrable (fun z => f z * p z) :=
    (f.continuous.mul hp).integrable_of_hasCompactSupport f.hasCompactSupport.mul_right
  have hinner z : (∫ w, (gffKernel z w - p z - p w + C) * g w) =
      (∫ w, gffKernel z w * g w) - p z * (∫ w, g w) -
        (∫ w, p w * g w) + C * (∫ w, g w) := by
    have hkg := integrable_testKernel_section g z
    have heq w : (gffKernel z w - p z - p w + C) * g w =
        ((gffKernel z w * g w - p z * g w) - p w * g w) + C * g w := by ring
    simp_rw [heq]
    have hfirst := integral_sub hkg (hgi.const_mul (p z))
    have hsecond := integral_sub (hkg.sub (hgi.const_mul (p z))) hgp
    have hthird := integral_add ((hkg.sub (hgi.const_mul (p z))).sub hgp) (hgi.const_mul C)
    simp only [Pi.sub_apply] at hfirst hsecond hthird
    rw [hthird, hsecond, hfirst, integral_const_mul, integral_const_mul]
  have hA : Integrable (fun z => f z * (∫ w, gffKernel z w * g w)) :=
    (f.continuous.mul (continuous_testKernelPotential g)).integrable_of_hasCompactSupport
      f.hasCompactSupport.mul_right
  simp_rw [hinner, mul_add, mul_sub, ← mul_assoc]
  have hfirst := integral_sub hA (hfp.mul_const (∫ w, g w))
  have hsecond := integral_sub (hA.sub (hfp.mul_const (∫ w, g w)))
    (hfi.mul_const (∫ w, p w * g w))
  have hthird := integral_add ((hA.sub (hfp.mul_const (∫ w, g w))).sub
    (hfi.mul_const (∫ w, p w * g w))) ((hfi.mul_const C).mul_const (∫ w, g w))
  simp only [Pi.sub_apply] at hfirst hsecond hthird
  rw [hthird, hsecond, hfirst, integral_mul_const, integral_mul_const, integral_mul_const,
    integral_mul_const, ← gffCov_eq_integral_testKernel]
  have hpg : (∫ w, p w * g w) = ∫ w, g w * p w := by
    congr 1
    funext w
    ring
  rw [hpg]
  ring

/-- The circle potential of an exterior origin pin has a simple global formula. -/
theorem integral_gffKernel_exterior_origin (R : ℝ) (hR : 1 < R) (z : ℂ) :
    (∫ w, gffKernel z w ∂circleMeasure 0 (-Real.log R)) =
      -Real.log (max R ‖z‖) + Real.log (normPlus z) + Real.log R := by
  rw [integral_gffKernel_circleMeasure, integral_log_normPlus_circleMeasure_origin,
    neg_neg, Real.exp_log (zero_lt_one.trans hR), max_eq_right hR.le]
  simp only [zero_sub, norm_neg]

/-- The self-energy of the exterior origin pin is `log R`. -/
theorem circleSelfEnergy_exterior_origin (R : ℝ) (hR : 1 < R) :
    circleSelfEnergy 0 (-Real.log R) = Real.log R := by
  rw [circleSelfEnergy_eq, integral_log_normPlus_circleMeasure_origin,
    neg_neg, Real.exp_log (zero_lt_one.trans hR), max_eq_right hR.le]
  ring

/-- Exterior-pin covariance for global tests (see [KRV, (hatGformula)] and [KRV, (circleav)]). -/
theorem exteriorPinnedEvaluation_covariance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (R : ℝ) (hR : 1 < R) (f g : TestFn) :
    MemLp (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω f) 2 P ∧
    covariance (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω f)
      (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω g) P =
      (∫ x : ℂ, f x * (∫ y : ℂ, exteriorPinnedKernel R (by linarith) x y * g y)) := by
  let _ := hX.1
  refine ⟨exteriorPinnedEvaluation_memLp X Xc hX hc R (zero_lt_one.trans hR) f, ?_⟩
  have hf : covariance (fun ω => X ω f) (fun ω => Xc ω 0 (-Real.log R)) P = circleCross 0 (-Real.log R) f := by
    rw [covariance_comm]
    exact circleAverage_test_covariance P X Xc hX hc 0 (-Real.log R) f
  have hg := circleAverage_test_covariance P X Xc hX hc 0 (-Real.log R) g
  have hv : variance (fun ω => Xc ω 0 (-Real.log R)) P = Real.log R := by
    rw [← covariance_self (hc.2.1 0 (-Real.log R)).aemeasurable,
      circleAverage_covariance_self X Xc hX hc, circleSelfEnergy_exterior_origin R hR]
  rw [exteriorPinnedEvaluation_covariance_expansion X Xc hX hc R, hf, hg, hv]
  let p : ℂ → ℝ := fun z => ∫ w, gffKernel z w ∂circleMeasure 0 (-Real.log R)
  have he := gffCov_sub_potential_integral f g p (continuous_circleKernelPotential 0 (-Real.log R)) (Real.log R)
  calc
    _ = ∫ z, f z * (∫ w, (gffKernel z w - p z - p w + Real.log R) * g w) := by
      rw [← he]
      unfold circleCross
      dsimp [p]
      ring
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with z
      congr 1
      apply integral_congr_ae
      filter_upwards with w
      dsimp [p]
      rw [integral_gffKernel_exterior_origin R hR, integral_gffKernel_exterior_origin R hR]
      unfold gffKernel exteriorPinnedKernel
      rw [max_comm R ‖z‖, max_comm R ‖w‖]
      ring

/-- Separated exterior circles have a covariance independent of both nonnegative times. -/
theorem circleAverage_covariance_separated {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (x y : ℂ) (hx : 2 ≤ ‖x‖) (hy : 2 ≤ ‖y‖) (hsep : 2 ≤ ‖x - y‖)
    {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    covariance (fun ω => Xc ω x r) (fun ω => Xc ω y s) P =
      -Real.log ‖x - y‖ + Real.log ‖x‖ + Real.log ‖y‖ := by
  let _ := circleMeasure_isProbability x r
  have hpR := integral_log_normPlus_circleMeasure_exterior
    ((add_le_add le_rfl (exp_neg_le_one hr)).trans (by simpa only [one_add_one_eq_two] using hx))
  have hpS := integral_log_normPlus_circleMeasure_exterior
    ((add_le_add le_rfl (exp_neg_le_one hs)).trans (by simpa only [one_add_one_eq_two] using hy))
  rw [circleAverage_covariance_integral P X Xc hX hc]
  simp_rw [integral_gffKernel_circleMeasure, hpS]
  have heq : (fun z : ℂ => -Real.log (max (Real.exp (-s)) ‖y - z‖) +
      Real.log (normPlus z) + Real.log ‖y‖) =ᵐ[circleMeasure x r]
      fun z => -Real.log ‖y - z‖ + Real.log (normPlus z) + Real.log ‖y‖ := by
    filter_upwards [ae_norm_sub_center_circleMeasure x r] with z hz
    have htri : ‖x - y‖ ≤ Real.exp (-r) + ‖y - z‖ := by
      calc
        ‖x - y‖ = ‖(x - z) + (z - y)‖ := by congr 1; abel
        _ ≤ ‖x - z‖ + ‖z - y‖ := norm_add_le _ _
        _ = _ := by rw [norm_sub_rev x z, hz, norm_sub_rev z y]
    have hrad : Real.exp (-s) ≤ ‖y - z‖ := by
      linarith [exp_neg_le_one hr, exp_neg_le_one hs]
    rw [max_eq_right hrad]
  rw [integral_congr_ae heq]
  have hlog : Integrable (fun z => Real.log ‖y - z‖) (circleMeasure x r) := by
    simpa only [norm_sub_rev y] using integrable_log_norm_sub_circleMeasure x y r
  have hpin := integrable_log_normPlus_circleMeasure x r
  have hfirst := integral_add hlog.neg hpin
  have hsecond := integral_add (hlog.neg.add hpin) (integrable_const (Real.log ‖y‖))
  simp only [Pi.add_apply, Pi.neg_apply] at hfirst hsecond
  rw [hsecond, hfirst, integral_neg, integral_log_norm_rev_sub_circleMeasure,
    integral_const, probReal_univ, one_smul, hpR]
  have hrad : Real.exp (-r) ≤ ‖x - y‖ := by linarith [exp_neg_le_one hr]
  rw [max_eq_right hrad]

/-- Smaller exterior circles have the same pairing with tests outside their base disk. -/
theorem circleCross_exterior_add_eq (c : ℂ) (hc : 2 ≤ ‖c‖) (r₀ : ℝ) (hr₀ : 0 ≤ r₀)
    (t : ℝ) (ht : 0 ≤ t) (f : TestFn)
    (hs : tsupport f ⊆ (ball c (Real.exp (-r₀)))ᶜ) :
    circleCross c (r₀ + t) f = circleCross c r₀ f := by
  have hrt : 0 ≤ r₀ + t := add_nonneg hr₀ ht
  have hp0 := integral_log_normPlus_circleMeasure_exterior
    ((add_le_add le_rfl (exp_neg_le_one hr₀)).trans (by simpa only [one_add_one_eq_two] using hc))
  have hpt := integral_log_normPlus_circleMeasure_exterior
    ((add_le_add le_rfl (exp_neg_le_one hrt)).trans (by simpa only [one_add_one_eq_two] using hc))
  unfold circleCross
  simp_rw [integral_gffKernel_circleMeasure, hp0, hpt]
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : f z = 0
  · simp [hz]
  · have hzout := hs (subset_tsupport f hz)
    have hdist : Real.exp (-r₀) ≤ ‖c - z‖ := by
      simpa only [mem_compl_iff, mem_ball, dist_eq_norm, not_lt, norm_sub_rev z c] using hzout
    rw [max_eq_right hdist, max_eq_right ((exp_neg_add_le_exp_neg ht).trans hdist)]

/-- Every exterior center has the shifted radial finite-dimensional Brownian law. -/
theorem circleAverage_exterior_preBrownian {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (c : ℂ) (hout : 2 ≤ ‖c‖) (r₀ : ℝ) (hr₀ : 0 ≤ r₀) :
    IsPreBrownianReal (fun t : ℝ≥0 => fun ω => Xc ω c (r₀ + t) - Xc ω c r₀) P := by
  let _ := hX.1
  have hG := (circleAverage_isGaussianProcess P X Xc hX hc).1
  have hmean := (circleAverage_isGaussianProcess P X Xc hX hc).2
  have hinc := isGaussianProcess_sub_reindexed hG
    (fun t : ℝ≥0 => (c, r₀ + t)) (fun _ : ℝ≥0 => (c, r₀))
  apply preBrownian_of_gaussian_min_covariance _ hinc
  · intro t
    rw [integral_sub ((hc.2.1 c (r₀ + t)).integrable (by norm_num))
      ((hc.2.1 c r₀).integrable (by norm_num)), hmean, hmean, sub_self]
  · intro t u
    rw [covariance_fun_sub_fun_sub (hc.2.1 c (r₀ + t)) (hc.2.1 c r₀)
      (hc.2.1 c (r₀ + u)) (hc.2.1 c r₀),
      circleAverage_covariance_exterior P X Xc hX hc c hout (add_nonneg hr₀ t.coe_nonneg) (add_nonneg hr₀ u.coe_nonneg),
      circleAverage_covariance_exterior P X Xc hX hc c hout (add_nonneg hr₀ t.coe_nonneg) hr₀,
      circleAverage_covariance_exterior P X Xc hX hc c hout hr₀ (add_nonneg hr₀ u.coe_nonneg),
      circleAverage_covariance_exterior P X Xc hX hc c hout hr₀ hr₀, min_self]
    exact exterior_min_increment_covariance t.coe_nonneg u.coe_nonneg (2 * Real.log ‖c‖)

/-- Separated exterior radial increments have zero covariance at every pair of times. -/
theorem circleAverage_exterior_increment_covariance_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (x y : ℂ) (hx : 2 ≤ ‖x‖) (hy : 2 ≤ ‖y‖) (hsep : 2 ≤ ‖x - y‖)
    (r₀ : ℝ) (hr₀ : 0 ≤ r₀) (t u : ℝ≥0) :
    covariance (fun ω => Xc ω x (r₀ + t) - Xc ω x r₀)
      (fun ω => Xc ω y (r₀ + u) - Xc ω y r₀) P = 0 := by
  let _ := hX.1
  rw [covariance_fun_sub_fun_sub (hc.2.1 x (r₀ + t)) (hc.2.1 x r₀)
    (hc.2.1 y (r₀ + u)) (hc.2.1 y r₀),
    circleAverage_covariance_separated P X Xc hX hc x y hx hy hsep (add_nonneg hr₀ t.coe_nonneg) (add_nonneg hr₀ u.coe_nonneg),
    circleAverage_covariance_separated P X Xc hX hc x y hx hy hsep (add_nonneg hr₀ t.coe_nonneg) hr₀,
    circleAverage_covariance_separated P X Xc hX hc x y hx hy hsep hr₀ (add_nonneg hr₀ u.coe_nonneg),
    circleAverage_covariance_separated P X Xc hX hc x y hx hy hsep hr₀ hr₀]
  ring

/-- Sigma-algebra form of [KRV, Remark 2.2], including tangent disks. Function-valued independence
uses all coordinate cylinders. -/
theorem circleAverage_indebm {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (r₀ : ℝ) (hr₀ : 0 ≤ r₀)
    {n : ℕ} (c : Fin n → ℂ) (hout : ∀ i, 2 ≤ ‖c i‖)
    (hsep : ∀ i j, i ≠ j → 2 ≤ dist (c i) (c j)) :
    (∀ i, IsPreBrownianReal
      (fun t : ℝ≥0 => fun ω => Xc ω (c i) (r₀ + t) - Xc ω (c i) r₀) P) ∧
    iIndepFun (fun i => fun ω => fun t : ℝ≥0 => Xc ω (c i) (r₀ + t) - Xc ω (c i) r₀) P ∧
    IndepFun (fun ω => fun i => fun t : ℝ≥0 => Xc ω (c i) (r₀ + t) - Xc ω (c i) r₀)
      (fun ω => fun f : {f : TestFn // tsupport f ⊆ (⋃ i, ball (c i) (Real.exp (-r₀)))ᶜ} =>
        X ω f.val) P := by
  let _ := hX.1
  let T := (i : Fin n) × ℝ≥0
  let U : (i : Fin n) → ℝ≥0 → Ω → ℝ := fun i t ω => Xc ω (c i) (r₀ + t) - Xc ω (c i) r₀
  let p : T → ℂ × ℝ := fun s => (c s.1, r₀ + s.2)
  let q : T → ℂ × ℝ := fun s => (c s.1, r₀)
  have hG := (circleAverage_isGaussianProcess P X Xc hX hc).1
  have hinc : IsGaussianProcess (fun s : T => U s.1 s.2) P :=
    isGaussianProcess_sub_reindexed hG p q
  have hm i t : MemLp (U i t) 2 P := (hc.2.1 (c i) (r₀ + t)).sub (hc.2.1 (c i) r₀)
  have hzero i j (hij : i ≠ j) t u : covariance (U i t) (U j u) P = 0 :=
    circleAverage_exterior_increment_covariance_zero P X Xc hX hc (c i) (c j)
      (hout i) (hout j) (by simpa only [dist_eq_norm] using hsep i j hij) r₀ hr₀ t u
  refine ⟨fun i => circleAverage_exterior_preBrownian P X Xc hX hc (c i) (hout i) r₀ hr₀,
    hinc.iIndepFun_of_covariance_eq_zero (fun i t => (hm i t).aemeasurable) hzero, ?_⟩
  let E := {f : TestFn // tsupport f ⊆ (⋃ i, ball (c i) (Real.exp (-r₀)))ᶜ}
  have hboth := circleAverage_increment_tests_isGaussianProcess X Xc hX hc p q (fun f : E => f.val)
  have hflat : IndepFun (fun ω => fun s : T => U s.1 s.2 ω)
      (fun ω => fun f : E => X ω f.val) P := by
    apply hboth.indepFun_of_covariance_eq_zero
      (fun s => (hm s.1 s.2).aemeasurable)
      (fun f => (equatorGFF_test_memLp X hX f.val).aemeasurable)
    intro s f
    rw [covariance_fun_sub_left (hc.2.1 (c s.1) (r₀ + s.2)) (hc.2.1 (c s.1) r₀)
      (equatorGFF_test_memLp X hX f.val), circleAverage_test_covariance P X Xc hX hc,
      circleAverage_test_covariance P X Xc hX hc,
      circleCross_exterior_add_eq (c s.1) (hout s.1) r₀ hr₀ s.2 s.2.coe_nonneg f.val ?_, sub_self]
    intro z hz
    have hzout := f.property hz
    exact fun hzball => hzout (mem_iUnion.mpr ⟨s.1, hzball⟩)
  have hcurry : Measurable (fun F : T → ℝ => fun i : Fin n => fun t : ℝ≥0 => F ⟨i, t⟩) :=
    Measurable.of_eval (fun i => Measurable.of_eval (fun t => measurable_pi_apply (⟨i, t⟩ : T)))
  exact hflat.comp hcurry measurable_id

/-- Integrating the continuous one-circle potential separates the two pinning terms. -/
theorem integral_integral_gffKernel_eq_logmax (x y : ℂ) (r s : ℝ) :
    (∫ z, ∫ w, gffKernel z w ∂circleMeasure y s ∂circleMeasure x r) =
      -(∫ z, Real.log (max (Real.exp (-s)) ‖y - z‖) ∂circleMeasure x r) +
        (∫ z, Real.log (normPlus z) ∂circleMeasure x r) +
        (∫ w, Real.log (normPlus w) ∂circleMeasure y s) := by
  let _ := circleMeasure_isProbability x r
  simp_rw [integral_gffKernel_circleMeasure]
  have hlog : Continuous (fun z : ℂ => Real.log (max (Real.exp (-s)) ‖y - z‖)) :=
    (continuous_const.max (continuous_const.sub continuous_id).norm).log
      (fun _ => ne_of_gt ((Real.exp_pos _).trans_le (le_max_left _ _)))
  have hi := integrable_circleMeasure_of_circleIntegrable x r hlog.measurable hlog.continuousOn.circleIntegrable'
  have hp := integrable_log_normPlus_circleMeasure x r
  have hfirst := integral_add hi.neg hp
  have hsecond := integral_add (hi.neg.add hp)
    (integrable_const (∫ w, Real.log (normPlus w) ∂circleMeasure y s))
  simp only [Pi.add_apply, Pi.neg_apply] at hfirst hsecond
  rw [hsecond, hfirst, integral_neg, integral_const, probReal_univ, one_smul]

/-- Rotating the parameter by the center displacement's argument removes its phase. -/
theorem norm_circleMap_sub_phase (x y : ℂ) (a t : ℝ) :
    ‖circleMap x a (t + Complex.arg (x-y)) - y‖ =
      ‖(‖x-y‖ : ℂ)+(a : ℂ)*Complex.exp ((t : ℂ)*Complex.I)‖ := by
  have heq : circleMap x a (t+Complex.arg (x-y)) - y =
      Complex.exp ((Complex.arg (x-y) : ℂ)*Complex.I) *
        ((‖x-y‖ : ℂ)+(a : ℂ)*Complex.exp ((t : ℂ)*Complex.I)) := by
    rw [circleMap]
    push_cast
    rw [add_mul, Complex.exp_add]
    have hphase := Complex.norm_mul_exp_arg_mul_I (x-y)
    calc
      _ = (x-y) + (a : ℂ)*Complex.exp ((t : ℂ)*Complex.I)*
          Complex.exp ((Complex.arg (x-y) : ℂ)*Complex.I) := by ring
      _ = (‖x-y‖ : ℂ)*Complex.exp ((Complex.arg (x-y) : ℂ)*Complex.I) +
          (a : ℂ)*Complex.exp ((t : ℂ)*Complex.I)*
          Complex.exp ((Complex.arg (x-y) : ℂ)*Complex.I) :=
        congrArg (fun q : ℂ => q + (a : ℂ)*Complex.exp ((t : ℂ)*Complex.I)*
          Complex.exp ((Complex.arg (x-y) : ℂ)*Complex.I)) hphase.symm
      _ = _ := by ring
  rw [heq, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- Reflection in the real axis preserves the canonical circle-distance norm. -/
theorem norm_circleLogSection_reflection (d a t : ℝ) :
    ‖(d : ℂ)+(a : ℂ)*Complex.exp (((2*Real.pi-t : ℝ) : ℂ)*Complex.I)‖ =
      ‖(d : ℂ)+(a : ℂ)*Complex.exp ((t : ℂ)*Complex.I)‖ := by
  have h1 := norm_circleLogSection_sq d a (2*Real.pi-t)
  have h2 := norm_circleLogSection_sq d a t
  rw [Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi, one_mul, zero_mul, add_zero] at h1
  nlinarith [norm_nonneg ((d : ℂ)+(a : ℂ)*Complex.exp (((2*Real.pi-t : ℝ) : ℂ)*Complex.I)),
    norm_nonneg ((d : ℂ)+(a : ℂ)*Complex.exp ((t : ℂ)*Complex.I))]

/-- The full canonical clipped circle integral is twice its upper-semicircle integral. -/
theorem integral_clipped_circleLog_full (d a : ℝ) {b : ℝ} (hb : 0 < b) :
    (∫ t in 0..2*Real.pi, Real.log
      (max b ‖(d : ℂ)+(a : ℂ)*Complex.exp ((t : ℂ)*Complex.I)‖)) =
      2*(∫ t in 0..Real.pi, Real.log
        (max b ‖(d : ℂ)+(a : ℂ)*Complex.exp ((t : ℂ)*Complex.I)‖)) := by
  let f : ℝ → ℝ := fun t => Real.log
    (max b ‖(d : ℂ)+(a : ℂ)*Complex.exp ((t : ℂ)*Complex.I)‖)
  have hf : Continuous f := by
    apply Continuous.log (by fun_prop)
    intro t
    exact (hb.trans_le (le_max_left _ _)).ne'
  have hreflect t : f (2*Real.pi-t) = f t := by
    dsimp only [f]
    rw [norm_circleLogSection_reflection]
  have hi : (∫ t in Real.pi..2*Real.pi, f t) = ∫ t in 0..Real.pi, f t := by
    have h := intervalIntegral.integral_comp_sub_left f (a := 0) (b := Real.pi) (2*Real.pi)
    simp only [show 2*Real.pi-Real.pi = Real.pi by ring, sub_zero, hreflect] at h
    exact h.symm
  change (∫ t in 0..2*Real.pi, f t) = 2*(∫ t in 0..Real.pi, f t)
  rw [← intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable 0 Real.pi)
    (hf.intervalIntegrable Real.pi (2*Real.pi)), hi]
  ring

/-- Any radial clipped potential on a circle reduces to the canonical semicircle. -/
theorem integral_logmax_circleMeasure_eq_semicircle (x y : ℂ) (r : ℝ) {b : ℝ} (hb : 0 < b) :
    (∫ w, Real.log (max b ‖w-y‖) ∂circleMeasure x r) =
      (1/Real.pi)*(∫ t in 0..Real.pi, Real.log
        (max b ‖(‖x-y‖ : ℂ)+(Real.exp (-r) : ℂ)*Complex.exp ((t : ℂ)*Complex.I)‖)) := by
  have hf : Continuous (fun w : ℂ => Real.log (max b ‖w-y‖)) :=
    (continuous_const.max (continuous_id.sub continuous_const).norm).log
      (fun _ => (hb.trans_le (le_max_left _ _)).ne')
  rw [integral_circleMeasure_eq_circleAverage x r _ hf.measurable,
    Real.circleAverage_eq_integral_add (Complex.arg (x-y))]
  simp_rw [norm_circleMap_sub_phase]
  rw [integral_clipped_circleLog_full _ _ hb, smul_eq_mul]
  have hscalar (A : ℝ) : (2*Real.pi)⁻¹*(2*A) = (1/Real.pi)*A := by
    field_simp [Real.pi_ne_zero]
  exact hscalar _

/-- The distance to a pole on a circle is at most center distance plus radius. -/
theorem ae_norm_sub_le_center_add_circleMeasure (x y : ℂ) (r : ℝ) :
    ∀ᵐ w ∂circleMeasure x r, ‖w-y‖ ≤ ‖x-y‖ + Real.exp (-r) := by
  filter_upwards [ae_norm_sub_center_circleMeasure x r] with w hw
  calc
    _ = ‖(w-x)+(x-y)‖ := by congr 1; ring
    _ ≤ ‖w-x‖+‖x-y‖ := norm_add_le _ _
    _ = _ := by rw [hw]; ring

/-- The reverse triangle inequality supplies the nonintersecting-circle lower bound. -/
theorem ae_abs_center_sub_radius_le_circleMeasure (x y : ℂ) (r : ℝ) :
    ∀ᵐ w ∂circleMeasure x r, |‖x-y‖-Real.exp (-r)| ≤ ‖w-y‖ := by
  filter_upwards [ae_norm_sub_center_circleMeasure x r] with w hw
  have h := abs_norm_sub_norm_le (x-y) (x-w)
  rw [norm_sub_rev x w, hw] at h
  have heq : (x-y)-(x-w) = w-y := by ring
  rwa [heq] at h

/-- Every clipped one-circle logarithmic potential agrees with the literal formula
`DOZZ.circleLogPotential`. -/
theorem integral_logmax_circleMeasure_eq_closed (x y : ℂ) (r : ℝ) {b : ℝ} (hb : 0 < b) :
    (∫ w, Real.log (max b ‖w-y‖) ∂circleMeasure x r) =
      circleLogPotential ‖x-y‖₊ ⟨Real.exp (-r), Real.exp_pos _⟩ ⟨b, hb⟩ := by
  let _ := circleMeasure_isProbability x r
  by_cases hxy : x = y
  · subst y
    rw [sub_self, nnnorm_zero, circleLogPotential_zero]
    have heq : (fun w : ℂ => Real.log (max b ‖w-x‖)) =ᵐ[circleMeasure x r]
        fun _ => Real.log (max b (Real.exp (-r))) := by
      filter_upwards [ae_norm_sub_center_circleMeasure x r] with w hw
      rw [hw]
    rw [integral_congr_ae heq, integral_const, probReal_univ, one_smul, max_comm]
  have hd : ‖x-y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  by_cases hcontain : ‖x-y‖+Real.exp (-r) ≤ b
  · rw [circleLogPotential_of_add_le (d := ‖x-y‖₊)
      ⟨Real.exp (-r), Real.exp_pos _⟩ ⟨b, hb⟩ hcontain]
    have heq : (fun w : ℂ => Real.log (max b ‖w-y‖)) =ᵐ[circleMeasure x r]
        fun _ => Real.log b := by
      filter_upwards [ae_norm_sub_le_center_add_circleMeasure x y r] with w hw
      rw [max_eq_left (hw.trans hcontain)]
    rw [integral_congr_ae heq, integral_const, probReal_univ, one_smul]
  by_cases hnon : b ≤ |‖x-y‖-Real.exp (-r)|
  · rw [circleLogPotential_of_le_abs_sub (d := ‖x-y‖₊)
      ⟨Real.exp (-r), Real.exp_pos _⟩ ⟨b, hb⟩ hd hnon hcontain]
    have heq : (fun w : ℂ => Real.log (max b ‖w-y‖)) =ᵐ[circleMeasure x r]
        fun w => Real.log ‖w-y‖ := by
      filter_upwards [ae_abs_center_sub_radius_le_circleMeasure x y r] with w hw
      rw [max_eq_right (hnon.trans hw)]
    rw [integral_congr_ae heq, integral_log_norm_sub_circleMeasure, max_comm]
    simp only [coe_nnnorm]
  · rw [integral_logmax_circleMeasure_eq_semicircle x y r hb,
      clipped_circleLog_integral_intersection (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd))
        (Real.exp_pos _) hb (lt_of_not_ge hcontain) (lt_of_not_ge hnon)]
    simp only [circleLogPotential, coe_nnnorm, hd, hcontain, hnon, ↓reduceIte,
      circleLogSeriesTerm]

/-- The regular equator pin is the same clipped circle potential with unit clipping radius. -/
theorem integral_log_normPlus_circleMeasure_eq_closed (x : ℂ) (r : ℝ) :
    (∫ w, Real.log (normPlus w) ∂circleMeasure x r) =
      circleLogPotential ‖x‖₊ ⟨Real.exp (-r), Real.exp_pos _⟩ ⟨1, by norm_num⟩ := by
  simpa only [sub_zero, normPlus] using
    integral_logmax_circleMeasure_eq_closed x 0 r zero_lt_one

/-- The exact all-center circle-average covariance, including intersecting and tangent circles. -/
theorem circleAverage_covariance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (x y : ℂ) (r s : ℝ) :
    covariance (fun ω => Xc ω x r) (fun ω => Xc ω y s) P =
      -circleLogPotential ‖x - y‖₊
          ⟨Real.exp (-r), Real.exp_pos _⟩ ⟨Real.exp (-s), Real.exp_pos _⟩ +
        circleLogPotential ‖x‖₊ ⟨Real.exp (-r), Real.exp_pos _⟩ ⟨1, by norm_num⟩ +
        circleLogPotential ‖y‖₊ ⟨Real.exp (-s), Real.exp_pos _⟩ ⟨1, by norm_num⟩ := by
  rw [circleAverage_covariance_integral P X Xc hX hc x y r s,
    integral_integral_gffKernel_eq_logmax]
  simp_rw [norm_sub_rev y]
  rw [integral_logmax_circleMeasure_eq_closed x y r (Real.exp_pos _),
    integral_log_normPlus_circleMeasure_eq_closed x r,
    integral_log_normPlus_circleMeasure_eq_closed y s]

end DOZZ.Proofs

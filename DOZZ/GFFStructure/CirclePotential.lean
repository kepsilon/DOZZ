/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFFStructure.Defs
public import DOZZ.GFF.RadialEnergy
public import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Deterministic circle potentials

The circle measures `DOZZ.circleMeasure` are normalized probability measures. Their logarithmic
sections are integrable even when the pole is on the circle, and have the closed `log max`
potential.
-/

public section

open MeasureTheory Set Metric
open scoped ENNReal NNReal Interval

namespace DOZZ.Proofs

/-- Normalized arclength has total mass one, at every center and logarithmic radius. -/
theorem circleMeasure_isProbability (x : ℂ) (r : ℝ) :
    IsProbabilityMeasure (circleMeasure x r) := by
  refine ⟨?_⟩
  rw [circleMeasure, Measure.smul_apply]
  rw [Measure.map_apply (measurable_circleMap x (Real.exp (-r))) MeasurableSet.univ]
  simp only [preimage_univ, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * Real.pi)⁻¹),
    inv_mul_cancel₀ (by positivity : 2 * Real.pi ≠ 0)]
  exact ENNReal.ofReal_one

/-- Bochner integration against `DOZZ.circleMeasure` agrees with the real circle average. -/
theorem integral_circleMeasure_eq_circleAverage (x : ℂ) (r : ℝ)
    (f : ℂ → ℝ) (hf : Measurable f) :
    (∫ z, f z ∂circleMeasure x r) = Real.circleAverage f x (Real.exp (-r)) := by
  rw [circleMeasure, integral_smul_measure,
    integral_map (measurable_circleMap x (Real.exp (-r))).aemeasurable hf.aestronglyMeasurable,
    ← intervalIntegral.integral_of_le Real.two_pi_pos.le,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (2 * Real.pi)⁻¹), Real.circleAverage_def]

/-- Circle integrability transfers to the normalized measure `DOZZ.circleMeasure`. -/
theorem integrable_circleMeasure_of_circleIntegrable (x : ℂ) (r : ℝ) {f : ℂ → ℝ}
    (hf : Measurable f) (hcircle : CircleIntegrable f x (Real.exp (-r))) :
    Integrable f (circleMeasure x r) := by
  rw [circleMeasure]
  have hmap : Integrable f
      ((volume.restrict (Ioc 0 (2 * Real.pi))).map (circleMap x (Real.exp (-r)))) := by
    rw [integrable_map_measure hf.aestronglyMeasurable
      (measurable_circleMap x (Real.exp (-r))).aemeasurable]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mp hcircle
  exact hmap.smul_measure (by simp only [ENNReal.ofReal_ne_top, ne_eq, not_false_eq_true])

/-- A logarithmic pole on the support of a circle is still integrable. -/
theorem integrable_log_norm_sub_circleMeasure (x z : ℂ) (r : ℝ) :
    Integrable (fun w : ℂ => Real.log ‖w - z‖) (circleMeasure x r) :=
  integrable_circleMeasure_of_circleIntegrable x r (by fun_prop)
    (circleIntegrable_log_norm_sub_const (Real.exp (-r)))

/-- The scalar logarithmic potential of one circle, at an arbitrary pole. -/
theorem integral_log_norm_sub_circleMeasure (x z : ℂ) (r : ℝ) :
    (∫ w, Real.log ‖w - z‖ ∂circleMeasure x r) =
      Real.log (max (Real.exp (-r)) ‖x - z‖) := by
  rw [integral_circleMeasure_eq_circleAverage x r _ (by fun_prop),
    circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (Real.exp_ne_zero _),
    Real.posLog_eq_log_max_one (by positivity)]
  rw [← Real.log_mul (Real.exp_ne_zero _) (by positivity :
    max 1 ((Real.exp (-r))⁻¹ * ‖x - z‖) ≠ 0)]
  congr 1
  rw [mul_max_of_nonneg _ _ (Real.exp_pos _).le]
  simp only [mul_one, ← mul_assoc, mul_inv_cancel₀ (Real.exp_ne_zero _), one_mul]

/-- Reversing the pole subtraction leaves the logarithmic potential unchanged. -/
theorem integral_log_norm_rev_sub_circleMeasure (x z : ℂ) (r : ℝ) :
    (∫ w, Real.log ‖z - w‖ ∂circleMeasure x r) =
      Real.log (max (Real.exp (-r)) ‖x - z‖) := by
  simp_rw [norm_sub_rev z]
  exact integral_log_norm_sub_circleMeasure x z r

/-- The measure `DOZZ.circleMeasure` is supported on its geometric circle. -/
theorem ae_mem_sphere_circleMeasure (x : ℂ) (r : ℝ) :
    ∀ᵐ z ∂circleMeasure x r, z ∈ sphere x (Real.exp (-r)) := by
  rw [circleMeasure]
  apply Measure.ae_smul_measure
  rw [ae_map_iff (measurable_circleMap x (Real.exp (-r))).aemeasurable]
  · filter_upwards with θ
    rw [mem_sphere_iff_norm, circleMap_sub_center, norm_circleMap_zero,
      abs_of_pos (Real.exp_pos _)]
  · exact isClosed_sphere.measurableSet

/-- On a circle, every concentric distance is constant. -/
theorem ae_norm_sub_center_circleMeasure (x : ℂ) (r : ℝ) :
    (fun z => ‖z - x‖) =ᵐ[circleMeasure x r] fun _ => Real.exp (-r) := by
  filter_upwards [ae_mem_sphere_circleMeasure x r] with z hz
  exact mem_sphere_iff_norm.mp hz

/-- The average logarithmic distance between two concentric circles. -/
theorem integral_integral_log_norm_concentric (x : ℂ) (r s : ℝ) :
    (∫ z, ∫ w, Real.log ‖z - w‖ ∂circleMeasure x s ∂circleMeasure x r) =
      Real.log (max (Real.exp (-r)) (Real.exp (-s))) := by
  let _ := circleMeasure_isProbability x r
  simp_rw [integral_log_norm_rev_sub_circleMeasure]
  have heq : (fun z => Real.log (max (Real.exp (-s)) ‖x - z‖)) =ᵐ[circleMeasure x r]
      fun _ => Real.log (max (Real.exp (-s)) (Real.exp (-r))) := by
    filter_upwards [ae_norm_sub_center_circleMeasure x r] with z hz
    rw [norm_sub_rev x z, hz]
  rw [integral_congr_ae heq, integral_const, probReal_univ, one_smul, max_comm]

/-- In logarithmic-radius coordinates the concentric log interaction is `-min r s`. -/
theorem integral_integral_log_norm_concentric_eq_neg_min (x : ℂ) (r s : ℝ) :
    (∫ z, ∫ w, Real.log ‖z - w‖ ∂circleMeasure x s ∂circleMeasure x r) =
      -min r s := by
  rw [integral_integral_log_norm_concentric]
  rcases le_total r s with h | h
  · rw [max_eq_left (Real.exp_le_exp.mpr (neg_le_neg h)), Real.log_exp, min_eq_left h]
  · rw [max_eq_right (Real.exp_le_exp.mpr (neg_le_neg h)), Real.log_exp, min_eq_right h]

/-- The source closed circle potential agrees with the concentric deterministic value. -/
theorem circleLogPotential_zero (a b : {r : ℝ // 0 < r}) :
    circleLogPotential 0 a b = Real.log (max (a : ℝ) (b : ℝ)) := by
  simp only [circleLogPotential, NNReal.coe_zero, ↓reduceIte]

/-- The source closed circle potential for a circle contained inside the averaging radius. -/
theorem circleLogPotential_of_add_le {d : ℝ≥0} (a b : {r : ℝ // 0 < r})
    (h : (d : ℝ) + a ≤ b) : circleLogPotential d a b = Real.log b := by
  by_cases hd : (d : ℝ) = 0
  · have hab : (a : ℝ) ≤ b := by simpa only [hd, zero_add] using h
    simp only [circleLogPotential, hd, ↓reduceIte, max_eq_right hab]
  · simp only [circleLogPotential, hd, h, ↓reduceIte]

/-- The potential `DOZZ.circleLogPotential` away from intersecting circles reduces to `log max`. -/
theorem circleLogPotential_of_le_abs_sub {d : ℝ≥0} (a b : {r : ℝ // 0 < r})
    (hd : (d : ℝ) ≠ 0) (hb : (b : ℝ) ≤ |(d : ℝ) - a|)
    (hout : ¬ (d : ℝ) + a ≤ b) :
    circleLogPotential d a b = Real.log (max (d : ℝ) a) := by
  simp only [circleLogPotential, hd, hout, hb, ↓reduceIte]

/-- The equator pinning potential is continuous on the plane. -/
theorem continuous_log_normPlus : Continuous (fun z : ℂ => Real.log (normPlus z)) := by
  change Continuous (fun z : ℂ => Real.log (max 1 ‖z‖))
  exact (continuous_const.max continuous_norm).log fun z =>
    ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))

/-- The regular pinning term is integrable on every circle. -/
theorem integrable_log_normPlus_circleMeasure (x : ℂ) (r : ℝ) :
    Integrable (fun z : ℂ => Real.log (normPlus z)) (circleMeasure x r) :=
  integrable_circleMeasure_of_circleIntegrable x r continuous_log_normPlus.measurable
    continuous_log_normPlus.continuousOn.circleIntegrable'

/-- The pinning potential is constant along each origin-centered circle. -/
theorem ae_log_normPlus_circleMeasure_origin (r : ℝ) :
    (fun z => Real.log (normPlus z)) =ᵐ[circleMeasure 0 r]
      fun _ => Real.log (max 1 (Real.exp (-r))) := by
  filter_upwards [ae_norm_sub_center_circleMeasure 0 r] with z hz
  simp only [sub_zero] at hz
  simp only [normPlus, hz]

/-- Average of the regular pinning term on an origin-centered circle. -/
theorem integral_log_normPlus_circleMeasure_origin (r : ℝ) :
    (∫ z, Real.log (normPlus z) ∂circleMeasure 0 r) =
      Real.log (max 1 (Real.exp (-r))) := by
  let _ := circleMeasure_isProbability 0 r
  rw [integral_congr_ae (ae_log_normPlus_circleMeasure_origin r),
    integral_const, probReal_univ, one_smul]

/-- Origin circle pinning potential in logarithmic-radius coordinates. -/
theorem integral_log_normPlus_circleMeasure_origin_eq_max (r : ℝ) :
    (∫ z, Real.log (normPlus z) ∂circleMeasure 0 r) = max 0 (-r) := by
  rw [integral_log_normPlus_circleMeasure_origin]
  rcases le_total 0 r with h | h
  · rw [max_eq_left (by simpa only [Real.exp_zero] using
      Real.exp_le_exp.mpr (neg_nonpos.mpr h)), Real.log_one, max_eq_left (neg_nonpos.mpr h)]
  · rw [max_eq_right (by simpa only [Real.exp_zero] using
      Real.exp_le_exp.mpr (neg_nonneg.mpr h)), Real.log_exp, max_eq_right (neg_nonneg.mpr h)]

/-- Every section of the equator kernel is integrable against every circle. -/
theorem integrable_gffKernel_circleMeasure (x z : ℂ) (r : ℝ) :
    Integrable (fun w => gffKernel z w) (circleMeasure x r) := by
  let _ := circleMeasure_isProbability x r
  have hlog : Integrable (fun w => Real.log ‖z - w‖) (circleMeasure x r) := by
    simpa only [norm_sub_rev z] using integrable_log_norm_sub_circleMeasure x z r
  have hplus := integrable_log_normPlus_circleMeasure x r
  have hc : Integrable (fun _ : ℂ => Real.log (normPlus z)) (circleMeasure x r) :=
    integrable_const _
  exact (hlog.neg.add hc).add hplus

/-- A single circle average of the pinned kernel reduces to the scalar log potential. -/
theorem integral_gffKernel_circleMeasure (x z : ℂ) (r : ℝ) :
    (∫ w, gffKernel z w ∂circleMeasure x r) =
      -Real.log (max (Real.exp (-r)) ‖x - z‖) + Real.log (normPlus z) +
        (∫ w, Real.log (normPlus w) ∂circleMeasure x r) := by
  let _ := circleMeasure_isProbability x r
  have hlog : Integrable (fun w => Real.log ‖z - w‖) (circleMeasure x r) := by
    simpa only [norm_sub_rev z] using integrable_log_norm_sub_circleMeasure x z r
  have hplus := integrable_log_normPlus_circleMeasure x r
  have hc : Integrable (fun _ : ℂ => Real.log (normPlus z)) (circleMeasure x r) :=
    integrable_const _
  change (∫ w, -Real.log ‖z - w‖ + Real.log (normPlus z) + Real.log (normPlus w)
    ∂circleMeasure x r) = _
  have houter := integral_add (hlog.neg.add hc) hplus
  have hinner := integral_add hlog.neg hc
  simp only [Pi.add_apply, Pi.neg_apply] at houter hinner
  rw [houter, hinner, integral_neg, integral_log_norm_rev_sub_circleMeasure,
    integral_const, probReal_univ, one_smul]

/-- The full deterministic covariance of two origin-centered circles. -/
theorem integral_integral_gffKernel_origin (r s : ℝ) :
    (∫ z, ∫ w, gffKernel z w ∂circleMeasure 0 s ∂circleMeasure 0 r) =
      min r s + max 0 (-r) + max 0 (-s) := by
  let _ := circleMeasure_isProbability 0 r
  simp_rw [integral_gffKernel_circleMeasure]
  have hconst : (fun z : ℂ => -Real.log (max (Real.exp (-s)) ‖(0 : ℂ) - z‖) +
      Real.log (normPlus z) + ∫ w, Real.log (normPlus w) ∂circleMeasure 0 s)
      =ᵐ[circleMeasure 0 r] fun _ =>
        -Real.log (max (Real.exp (-s)) (Real.exp (-r))) +
        Real.log (max 1 (Real.exp (-r))) + ∫ w, Real.log (normPlus w) ∂circleMeasure 0 s := by
    filter_upwards [ae_norm_sub_center_circleMeasure 0 r, ae_log_normPlus_circleMeasure_origin r]
      with z hz hp
    rw [norm_sub_rev, hz, hp]
  rw [integral_congr_ae hconst, integral_const, probReal_univ, one_smul]
  have hmax : Real.log (max (Real.exp (-s)) (Real.exp (-r))) = -min r s := by
    rw [← integral_integral_log_norm_concentric 0 s r,
      integral_integral_log_norm_concentric_eq_neg_min, min_comm]
  have hp := integral_log_normPlus_circleMeasure_origin_eq_max r
  rw [integral_log_normPlus_circleMeasure_origin] at hp
  rw [hmax, hp, integral_log_normPlus_circleMeasure_origin_eq_max, neg_neg]

/-- Nonnegative origin times have the Brownian minimum covariance. -/
theorem integral_integral_gffKernel_origin_nonneg {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (∫ z, ∫ w, gffKernel z w ∂circleMeasure 0 s ∂circleMeasure 0 r) = min r s := by
  rw [integral_integral_gffKernel_origin, max_eq_left (neg_nonpos.mpr hr),
    max_eq_left (neg_nonpos.mpr hs), add_zero, add_zero]

/-- The outward origin half-line has the same Brownian minimum covariance. -/
theorem integral_integral_gffKernel_origin_nonpos {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (∫ z, ∫ w, gffKernel z w ∂circleMeasure 0 (-s) ∂circleMeasure 0 (-r)) = min r s := by
  rw [integral_integral_gffKernel_origin, neg_neg, neg_neg,
    max_eq_right hr, max_eq_right hs]
  rcases le_total r s with h | h
  · rw [min_eq_right (neg_le_neg h), min_eq_left h]
    ring
  · rw [min_eq_left (neg_le_neg h), min_eq_right h]
    ring

/-- Inward and outward origin circles have zero cross-covariance. -/
theorem integral_integral_gffKernel_origin_cross {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (∫ z, ∫ w, gffKernel z w ∂circleMeasure 0 (-s) ∂circleMeasure 0 r) = 0 := by
  rw [integral_integral_gffKernel_origin, neg_neg, max_eq_left (neg_nonpos.mpr hr),
    max_eq_right hs, min_eq_right (le_trans (neg_nonpos.mpr hs) hr)]
  ring

/-- On a circle that stays outside the unit disk, the pinning term equals `log norm`. -/
theorem ae_normPlus_eq_norm_circleMeasure {x : ℂ} {r : ℝ}
    (hout : 1 + Real.exp (-r) ≤ ‖x‖) :
    (fun z => normPlus z) =ᵐ[circleMeasure x r] fun z => ‖z‖ := by
  filter_upwards [ae_norm_sub_center_circleMeasure x r] with z hz
  have htri : ‖x‖ ≤ ‖z‖ + ‖z - x‖ := by
    simpa only [norm_sub_rev x z] using norm_le_norm_add_norm_sub z x
  have hn : 1 ≤ ‖z‖ := by linarith only [hout, htri, hz]
  exact max_eq_right hn

/-- The regular pinning circle average outside the unit disk, including tangency. -/
theorem integral_log_normPlus_circleMeasure_exterior {x : ℂ} {r : ℝ}
    (hout : 1 + Real.exp (-r) ≤ ‖x‖) :
    (∫ z, Real.log (normPlus z) ∂circleMeasure x r) = Real.log ‖x‖ := by
  have heq : (fun z => Real.log (normPlus z)) =ᵐ[circleMeasure x r]
      fun z => Real.log ‖z‖ := (ae_normPlus_eq_norm_circleMeasure hout).fun_comp Real.log
  rw [integral_congr_ae heq]
  have hmax : Real.exp (-r) ≤ ‖x‖ := le_trans (le_add_of_nonneg_left zero_le_one) hout
  have hpotential := integral_log_norm_sub_circleMeasure x 0 r
  simpa only [sub_zero, max_eq_right hmax] using hpotential

/-- The source circle potential at the equator radius is the origin pinning term. -/
theorem circleLogPotential_origin_equator (r : ℝ) :
    circleLogPotential 0 ⟨Real.exp (-r), Real.exp_pos _⟩ ⟨1, by norm_num⟩ = max 0 (-r) := by
  rw [circleLogPotential_zero, max_comm]
  exact (integral_log_normPlus_circleMeasure_origin r).symm.trans
    (integral_log_normPlus_circleMeasure_origin_eq_max r)

/-- The concentric source closed potential in logarithmic-radius coordinates. -/
theorem circleLogPotential_concentric (r s : ℝ) :
    circleLogPotential 0 ⟨Real.exp (-r), Real.exp_pos _⟩
      ⟨Real.exp (-s), Real.exp_pos _⟩ = -min r s := by
  rw [circleLogPotential_zero]
  exact (integral_integral_log_norm_concentric 0 r s).symm.trans
    (integral_integral_log_norm_concentric_eq_neg_min 0 r s)


/-- Separated circles are in the elementary branch of the source closed potential. -/
theorem circleLogPotential_of_radii_le_distance {d : ℝ≥0}
    (a b : {r : ℝ // 0 < r}) (hsep : (a : ℝ) + b ≤ d) :
    circleLogPotential d a b = Real.log d := by
  have hd : 0 < (d : ℝ) := lt_of_lt_of_le (add_pos a.2 b.2) hsep
  have ha : (a : ℝ) ≤ d := le_trans (le_add_of_nonneg_right b.2.le) hsep
  have hsub : 0 ≤ (d : ℝ) - a := sub_nonneg.mpr ha
  have hb : (b : ℝ) ≤ |(d : ℝ) - a| := by
    rw [abs_of_nonneg hsub]
    linarith only [hsep]
  have hout : ¬ (d : ℝ) + a ≤ b := by
    intro h
    linarith only [hsep, h, a.2]
  rw [circleLogPotential_of_le_abs_sub a b hd.ne' hb hout, max_eq_left ha]

/-- The radii used at nonnegative logarithmic times never exceed one. -/
theorem exp_neg_le_one {r : ℝ} (hr : 0 ≤ r) : Real.exp (-r) ≤ 1 := by
  simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (neg_nonpos.mpr hr)

/-- At exterior centers the source pinning potential is exactly `log norm`. -/
theorem circleLogPotential_equator_of_exterior {x : ℂ} {r : ℝ}
    (hx : 2 ≤ ‖x‖) (hr : 0 ≤ r) :
    circleLogPotential ‖x‖₊ ⟨Real.exp (-r), Real.exp_pos _⟩ ⟨1, by norm_num⟩ =
      Real.log ‖x‖ := by
  apply circleLogPotential_of_radii_le_distance
  change Real.exp (-r) + 1 ≤ ‖x‖
  exact le_trans (add_le_add (exp_neg_le_one hr) le_rfl) (by simpa only [one_add_one_eq_two] using hx)



/-- Exterior base radius `e^{-r₀}` and every smaller radius stay in the elementary geometry. -/
theorem exp_neg_add_le_exp_neg {r₀ t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-(r₀ + t)) ≤ Real.exp (-r₀) :=
  Real.exp_le_exp.mpr (neg_le_neg (le_add_of_nonneg_right ht))

/-- Difference of the exterior source covariances is the Brownian increment covariance. -/
theorem exterior_min_increment_covariance {r₀ t u : ℝ}
    (ht : 0 ≤ t) (hu : 0 ≤ u) (K : ℝ) :
    (min (r₀ + t) (r₀ + u) + K) - (min (r₀ + t) r₀ + K) -
      (min r₀ (r₀ + u) + K) + (r₀ + K) = min t u := by
  rw [min_eq_right (le_add_of_nonneg_right ht), min_eq_left (le_add_of_nonneg_right hu),
    ← add_min]
  ring

/-- The origin formula has variance `|r|` at every real logarithmic radius. -/
theorem origin_circle_variance_algebra (r : ℝ) :
    min r r + max 0 (-r) + max 0 (-r) = |r| := by
  rw [min_self]
  rcases le_total 0 r with h | h
  · rw [max_eq_left (neg_nonpos.mpr h), abs_of_nonneg h]
    ring
  · rw [max_eq_right (neg_nonneg.mpr h), abs_of_nonpos h]
    ring

/-- Continuous functions with fixed compact support have smooth test approximants with
controlled support and a uniform error bound. -/
theorem exists_testFn_uniform_approx {f : ℂ → ℝ} (hf : Continuous f)
    {R ε : ℝ} (hR : 0 < R) (hs : tsupport f ⊆ closedBall (0 : ℂ) R) (hε : 0 < ε) :
    ∃ g : TestFn, tsupport g ⊆ closedBall (0 : ℂ) (R + 1) ∧
      ∀ z, |g z - f z| < ε := by
  have hcompact : HasCompactSupport f := (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset isClosed_closure hs
  obtain ⟨g, hg, he⟩ := (hcompact.uniformContinuous_of_continuous hf).exists_contDiff_dist_le hε
  let b : ContDiffBump (0 : ℂ) := ⟨R, R + 1, hR, lt_add_one R⟩
  let gTest : TestFn := ⟨fun z => b z * g z, b.contDiff.mul hg,
    b.hasCompactSupport.mul_right, subset_univ _⟩
  have hs' : tsupport gTest ⊆ closedBall (0 : ℂ) (R + 1) := by
    apply Subset.trans (tsupport_mul_subset_left (f := fun z => b z) (g := g))
    exact b.tsupport_eq.subset
  refine ⟨gTest, hs', fun z => ?_⟩
  have hbf : b z * f z = f z := by
    by_cases hz : z ∈ tsupport f
    · rw [b.one_of_mem_closedBall (hs hz), one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]
  change |b z * g z - f z| < ε
  rw [← hbf, ← mul_sub, abs_mul, abs_of_nonneg b.nonneg]
  exact lt_of_le_of_lt (mul_le_of_le_one_left (abs_nonneg _) b.le_one)
    (by simpa only [Real.dist_eq] using he z)

/-- Translated and scaled continuous annular probability density around a circle. -/
@[expose] noncomputable def circleAnnularDensity (x : ℂ) (r : ℝ) (n : ℕ) (z : ℂ) : ℝ :=
  (Real.exp (-r))⁻¹ ^ 2 * DOZZ.annularProbabilityDensity n ((Real.exp (-r))⁻¹ • (z - x))
/-- The scaled annular approximant is continuous. -/
theorem continuous_circleAnnularDensity (x : ℂ) (r : ℝ) (n : ℕ) :
    Continuous (circleAnnularDensity x r n) :=
  by
  unfold circleAnnularDensity
  have h := DOZZ.continuous_annularProbabilityDensity n
  fun_prop
/-- All annular widths have a common compact support bound. -/
theorem support_circleAnnularDensity_subset (x : ℂ) (r : ℝ) (n : ℕ) :
    Function.support (circleAnnularDensity x r n) ⊆ closedBall (0 : ℂ) (‖x‖ + 2 * Real.exp (-r)) := by
  intro z hz
  have hρ : DOZZ.annularProbabilityDensity n ((Real.exp (-r))⁻¹ • (z - x)) ≠ 0 := by
    intro hzero
    exact hz (by simp only [circleAnnularDensity, hzero, mul_zero])
  have hscale : ‖(Real.exp (-r))⁻¹ • (z - x)‖ ≤ 2 := by
    have hb := DOZZ.annularProbabilityDensity_radius_bound n _ hρ
    have hn : (1 : ℝ) ≤ (n : ℝ) + 2 := by linarith only [Nat.cast_nonneg (α := ℝ) n]
    have hi : 1 / ((n : ℝ) + 2) ≤ 1 :=
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hn).trans_eq (one_div_one)
    have hnorm := (abs_lt.mp hb).2
    linarith only [hnorm, hi]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (Real.exp_pos _))] at hscale
  have hdist : ‖z - x‖ ≤ 2 * Real.exp (-r) := by
    have hmul := mul_le_mul_of_nonneg_left hscale (Real.exp_pos (-r)).le
    rw [← mul_assoc, mul_inv_cancel₀ (Real.exp_ne_zero _), one_mul] at hmul
    simpa only [mul_comm] using hmul
  have hn := norm_le_norm_add_norm_sub x z
  rw [mem_closedBall, dist_zero_right]
  have hd' : ‖x - z‖ ≤ 2 * Real.exp (-r) := by rwa [norm_sub_rev]
  exact hn.trans (add_le_add le_rfl hd')
/-- The continuous circle approximant has compact support. -/
theorem hasCompactSupport_circleAnnularDensity (x : ℂ) (r : ℝ) (n : ℕ) :
    HasCompactSupport (circleAnnularDensity x r n) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _)
    (support_circleAnnularDensity_subset x r n)
/-- The common radius bound also contains the closed support. -/
theorem tsupport_circleAnnularDensity_subset (x : ℂ) (r : ℝ) (n : ℕ) :
    tsupport (circleAnnularDensity x r n) ⊆ closedBall (0 : ℂ) (‖x‖ + 2 * Real.exp (-r)) :=
  closure_minimal (support_circleAnnularDensity_subset x r n) isClosed_closedBall
/-- The continuous circle approximant is integrable. -/
theorem integrable_circleAnnularDensity (x : ℂ) (r : ℝ) (n : ℕ) :
    Integrable (circleAnnularDensity x r n) :=
  (continuous_circleAnnularDensity x r n).integrable_of_hasCompactSupport
    (hasCompactSupport_circleAnnularDensity x r n)
/-- The translated, scaled circle approximant has total mass one. -/
theorem integral_circleAnnularDensity (x : ℂ) (r : ℝ) (n : ℕ) :
    (∫ z, circleAnnularDensity x r n z) = 1 := by
  unfold circleAnnularDensity
  rw [integral_const_mul]
  have ht : (∫ z : ℂ, DOZZ.annularProbabilityDensity n ((Real.exp (-r))⁻¹ • (z - x))) =
      ∫ z : ℂ, DOZZ.annularProbabilityDensity n ((Real.exp (-r))⁻¹ • z) :=
    integral_sub_right_eq_self (μ := (volume : Measure ℂ))
      (fun z : ℂ => DOZZ.annularProbabilityDensity n ((Real.exp (-r))⁻¹ • z)) x
  rw [ht, Measure.integral_comp_inv_smul_of_nonneg (μ := (volume : Measure ℂ))
    (DOZZ.annularProbabilityDensity n) (Real.exp_pos (-r)).le,
    Complex.finrank_real_complex, smul_eq_mul, DOZZ.integral_annularProbabilityDensity,
    mul_one]
  field_simp

/-- Smooth test approximants to the translated annuli, with a common compact support and
arbitrary positive prescribed uniform errors. No log-energy convergence is asserted here. -/
theorem exists_testFn_circleAnnular_approx (x : ℂ) (r : ℝ) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 < ε n) :
    ∃ f : ℕ → TestFn, ∀ n,
      tsupport (f n) ⊆ closedBall (0 : ℂ) (‖x‖ + 2 * Real.exp (-r) + 1) ∧
      ∀ z, |f n z - circleAnnularDensity x r n z| < ε n := by
  have hR : 0 < ‖x‖ + 2 * Real.exp (-r) :=
    add_pos_of_nonneg_of_pos (norm_nonneg _) (mul_pos zero_lt_two (Real.exp_pos _))
  have hn n := exists_testFn_uniform_approx (continuous_circleAnnularDensity x r n) hR
    (tsupport_circleAnnularDensity_subset x r n) (hε n)
  choose f hf using hn
  exact ⟨f, hf⟩

end DOZZ.Proofs

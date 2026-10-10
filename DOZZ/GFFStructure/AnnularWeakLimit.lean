/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GFFStructure.AnnularCircleEnergy
import Mathlib.Analysis.Convolution

/-!
# Weak limits of annular circle densities

Polar integration separates the angular average from the concentrating radial probability law.
This identifies mixed pairings with continuous circle potentials independently of density height.
-/

@[expose] public section

open Filter MeasureTheory Set Metric
open scoped Topology ENNReal Interval

namespace DOZZ.Proofs

/-- Integrable planar functions remain integrable after the polar Jacobian is included. -/
theorem integrable_polarJacobian {f : ℂ → ℝ} (hf : Measurable f) (hi : Integrable f) :
    Integrable (fun p : ℝ × ℝ => p.1 * f (Complex.polarCoord.symm p))
      (volume.restrict Complex.polarCoord.target) := by
  have hm : Measurable (fun p : ℝ × ℝ => p.1 * f (Complex.polarCoord.symm p)) := by
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  refine ⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_enorm).mpr ?_⟩
  calc
    _ = ∫⁻ p in Complex.polarCoord.target,
        ENNReal.ofReal p.1 * ‖f (Complex.polarCoord.symm p)‖ₑ := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem Complex.polarCoord.open_target.measurableSet] with p hp
      simp only [enorm_mul, Real.enorm_eq_ofReal hp.1.le]
    _ = ∫⁻ z, ‖f z‖ₑ := Complex.lintegral_comp_polarCoord_symm (fun z => ‖f z‖ₑ)
    _ < ⊤ := hi.hasFiniteIntegral

/-- The annular integral is a mixture of circle averages with the radial law
`DOZZ.annularRadiusLaw`. -/
theorem integral_annular_mul_eq_radial_average (n : ℕ) (h : ℂ → ℝ) (hh : Continuous h) :
    (∫ z, DOZZ.annularProbabilityDensity n z * h z) =
      ∫ t in Ioi (0 : ℝ), DOZZ.annularRadiusLaw n t * Real.circleAverage h 0 t := by
  let F : ℂ → ℝ := fun z => DOZZ.annularProbabilityDensity n z * h z
  have hFc : Continuous F := (DOZZ.continuous_annularProbabilityDensity n).mul hh
  have hFi : Integrable F := hFc.integrable_of_hasCompactSupport
    (DOZZ.hasCompactSupport_annularProbabilityDensity n).mul_right
  have hp := integrable_polarJacobian hFc.measurable hFi
  have ht : (volume : Measure (ℝ × ℝ)).restrict Complex.polarCoord.target =
      (volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-Real.pi) Real.pi)) := by
    rw [Complex.polarCoord_target, Measure.prod_restrict, Measure.volume_eq_prod]
  change (∫ z, F z) = _
  rw [← Complex.integral_comp_polarCoord_symm F]
  simp only [smul_eq_mul]
  rw [ht] at hp
  rw [polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict]
  rw [integral_prod _ hp]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t htpos
  have hpolar (θ : ℝ) : Complex.polarCoord.symm (t, θ) = circleMap 0 t θ := by
    simp only [Complex.polarCoord_symm_apply, circleMap, zero_add]
    rw [Complex.exp_mul_I]
    push_cast
    ring
  calc
    _ = ∫ θ in Ioo (-Real.pi) Real.pi,
        (t * DOZZ.annularProbabilityRadial n t) * h (circleMap 0 t θ) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro θ _
      simp only [F, DOZZ.annularProbabilityDensity_eq_radial,
        hpolar, norm_circleMap_zero, abs_of_pos htpos]
      ring
    _ = (t * DOZZ.annularProbabilityRadial n t) *
        (2 * Real.pi * Real.circleAverage h 0 t) := by
      rw [integral_const_mul, DOZZ.integral_circleAngle_eq_twoPi_mul_circleAverage]
    _ = _ := by unfold DOZZ.annularRadiusLaw; ring

/-- A globally bounded continuous function has circle averages continuous in radius. -/
theorem continuous_circleAverage_radius (h : ℂ → ℝ) (hh : Continuous h)
    {M : ℝ} (hb : ∀ z, ‖h z‖ ≤ M) : Continuous (fun t : ℝ => Real.circleAverage h 0 t) := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 (2 * Real.pi))
  have hμ : IsFiniteMeasure μ := by
    dsimp [μ]
    exact isFiniteMeasure_restrict.mpr (by simp only [Real.volume_Ioc]; finiteness)
  let _ := hμ
  have hc : Continuous (fun t : ℝ => ∫ θ, h (circleMap 0 t θ) ∂μ) := by
    apply continuous_of_dominated
      (fun t => (hh.measurable.comp (measurable_circleMap 0 t)).aestronglyMeasurable)
      (fun t => Filter.Eventually.of_forall (fun θ => hb (circleMap 0 t θ)))
      (integrable_const M)
    filter_upwards with θ
    apply hh.comp
    simp only [circleMap]
    fun_prop
  have heq (t : ℝ) : Real.circleAverage h 0 t =
      (2 * Real.pi)⁻¹ * (∫ θ, h (circleMap 0 t θ) ∂μ) := by
    rw [Real.circleAverage_def, intervalIntegral.integral_of_le Real.two_pi_pos.le]
    rfl
  simp_rw [heq]
  exact hc.const_mul _

/-- The radial annular probability laws concentrate at radius one. -/
theorem tendsto_integral_annularRadiusLaw_mul (a : ℝ → ℝ) (ha : Continuous a) :
    Tendsto (fun n => ∫ t in Ioi (0 : ℝ), DOZZ.annularRadiusLaw n t * a t)
      atTop (𝓝 (a 1)) := by
  have hδ : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 (0 : ℝ)) := by
    convert (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
      (tendsto_add_atTop_nat 2) using 1
    ext n
    simp [Nat.cast_add]
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨η, hη, hηbound⟩ := Metric.continuousAt_iff.mp (ha.continuousAt (x := 1)) (ε / 2) (half_pos hε)
  obtain ⟨N, hN⟩ := (eventually_atTop.mp (hδ.eventually (gt_mem_nhds hη)))
  refine ⟨N, fun n hn => ?_⟩
  have hρi := DOZZ.integrable_annularRadiusLawOn n
  have hai : Integrable (fun t => DOZZ.annularRadiusLaw n t * a t)
      (volume.restrict (Ioi (0 : ℝ))) :=
    (((DOZZ.continuous_annularRadiusLaw n).mul ha).integrable_of_hasCompactSupport
      (DOZZ.hasCompactSupport_annularRadiusLaw n).mul_right).restrict
  have herror : |(∫ t in Ioi (0 : ℝ), DOZZ.annularRadiusLaw n t * a t) - a 1| ≤ ε / 2 := by
    have hval : (∫ t in Ioi (0 : ℝ), DOZZ.annularRadiusLaw n t * a t) - a 1 =
        ∫ t in Ioi (0 : ℝ), DOZZ.annularRadiusLaw n t * (a t - a 1) := by
      have hconst : (∫ t in Ioi (0 : ℝ), DOZZ.annularRadiusLaw n t * a 1) = a 1 := by
        rw [integral_mul_const, DOZZ.integral_annularRadiusLaw, one_mul]
      calc
        _ = (∫ t in Ioi (0 : ℝ), DOZZ.annularRadiusLaw n t * a t) -
            (∫ t in Ioi (0 : ℝ), DOZZ.annularRadiusLaw n t * a 1) := by rw [hconst]
        _ = _ := by
          rw [← integral_sub hai (hρi.mul_const (a 1))]
          congr 1
          funext t
          ring
    rw [hval]
    calc
      _ ≤ ∫ t in Ioi (0 : ℝ), |DOZZ.annularRadiusLaw n t * (a t - a 1)| :=
        abs_integral_le_integral_abs
      _ ≤ ∫ t in Ioi (0 : ℝ), (ε / 2) * DOZZ.annularRadiusLaw n t := by
        have hi : Integrable (fun t => DOZZ.annularRadiusLaw n t * (a t - a 1))
            (volume.restrict (Ioi (0 : ℝ))) := by
          convert hai.sub (hρi.mul_const (a 1)) using 1
          ext t
          simp only [Pi.sub_apply]
          ring
        apply integral_mono_ae hi.norm (hρi.const_mul (ε / 2))
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        by_cases hz : DOZZ.annularRadiusLaw n t = 0
        · simp [hz]
        · have hprofile : DOZZ.annularProfile n t ≠ 0 := by
            intro h
            apply hz
            simp [DOZZ.annularRadiusLaw, DOZZ.annularProbabilityRadial, h]
          have hdist : dist t 1 < η := by
            rw [Real.dist_eq]
            exact (DOZZ.annularProfile_radius_bound n t hprofile).trans (hN n hn)
          have hsmall : |a t - a 1| ≤ ε / 2 := by
            simpa only [Real.dist_eq] using (hηbound hdist).le
          rw [Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (DOZZ.annularRadiusLaw_nonneg n ht)]
          exact (mul_le_mul_of_nonneg_left hsmall (DOZZ.annularRadiusLaw_nonneg n ht)).trans_eq
            (mul_comm _ _)
      _ = ε / 2 := by rw [integral_const_mul, DOZZ.integral_annularRadiusLaw, mul_one]
  rw [Real.dist_eq]
  exact herror.trans_lt (half_lt_self hε)

/-- Continuous bounded functions converge under the unit-annulus approximations to arclength. -/
theorem tendsto_integral_annular_mul (h : ℂ → ℝ) (hh : Continuous h)
    {M : ℝ} (hb : ∀ z, ‖h z‖ ≤ M) :
    Tendsto (fun n => ∫ z, DOZZ.annularProbabilityDensity n z * h z)
      atTop (𝓝 (Real.circleAverage h 0 1)) := by
  simp_rw [integral_annular_mul_eq_radial_average _ h hh]
  exact tendsto_integral_annularRadiusLaw_mul _ (continuous_circleAverage_radius h hh hb)

/-- The angular change of variables transports a unit-circle average to the circle of center `x` and
radius `e^{-r}`. -/
theorem circleAverage_affine_unit (x : ℂ) (r : ℝ) (h : ℂ → ℝ) :
    Real.circleAverage (fun z => h (Real.exp (-r) • z + x)) 0 1 =
      Real.circleAverage h x (Real.exp (-r)) := by
  unfold Real.circleAverage
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  simp only [circleMap, zero_add, Complex.ofReal_one, one_mul, Complex.real_smul]
  congr 1
  ring

/-- Translated and scaled annuli converge to their circle for bounded continuous functions. -/
theorem tendsto_integral_circleAnnular_mul_bounded (x : ℂ) (r : ℝ)
    (h : ℂ → ℝ) (hh : Continuous h) {M : ℝ} (hb : ∀ z, ‖h z‖ ≤ M) :
    Tendsto (fun n => ∫ z, circleAnnularDensity x r n z * h z)
      atTop (𝓝 (∫ z, h z ∂circleMeasure x r)) := by
  simp_rw [integral_circleAnnularDensity_mul]
  rw [integral_circleMeasure_eq_circleAverage x r h hh.measurable,
    ← circleAverage_affine_unit x r h]
  apply tendsto_integral_annular_mul
    (fun z => h (Real.exp (-r) • z + x)) (by fun_prop)
    (fun z => hb _)

/-- A fixed ball contains the geometric circle as well as all its annular approximants. -/
theorem ae_mem_closedBall_circleMeasure (x : ℂ) (r : ℝ) :
    ∀ᵐ z ∂circleMeasure x r, z ∈ closedBall (0 : ℂ) (‖x‖ + 2 * Real.exp (-r)) := by
  filter_upwards [ae_norm_sub_center_circleMeasure x r] with z hz
  rw [mem_closedBall, dist_zero_right]
  calc
    ‖z‖ = ‖(z - x) + x‖ := by rw [sub_add_cancel]
    _ ≤ ‖z - x‖ + ‖x‖ := norm_add_le _ _
    _ ≤ ‖x‖ + 2 * Real.exp (-r) := by rw [hz]; linarith [Real.exp_pos (-r)]

/-- A common compact cutoff removes the global boundedness premise. Every continuous
potential therefore converges under the transported annular densities. -/
theorem tendsto_integral_circleAnnular_mul (x : ℂ) (r : ℝ)
    (h : ℂ → ℝ) (hh : Continuous h) :
    Tendsto (fun n => ∫ z, circleAnnularDensity x r n z * h z)
      atTop (𝓝 (∫ z, h z ∂circleMeasure x r)) := by
  let R := ‖x‖ + 2 * Real.exp (-r)
  have hR : 0 < R := by dsimp [R]; positivity
  let b : ContDiffBump (0 : ℂ) := ⟨R, R + 1, hR, lt_add_one R⟩
  let g : ℂ → ℝ := fun z => b z * h z
  have hg : Continuous g := b.continuous.mul hh
  have hgc : HasCompactSupport g := b.hasCompactSupport.mul_right
  obtain ⟨M, hM⟩ := hgc.exists_bound_of_continuous hg
  have hlim := tendsto_integral_circleAnnular_mul_bounded x r g hg hM
  have heq n : (fun z => circleAnnularDensity x r n z * g z) =
      fun z => circleAnnularDensity x r n z * h z := by
    funext z
    by_cases hz : circleAnnularDensity x r n z = 0
    · simp [hz]
    · have hball := support_circleAnnularDensity_subset x r n hz
      simp only [g, b.one_of_mem_closedBall hball, one_mul]
  have hae : g =ᵐ[circleMeasure x r] h := by
    filter_upwards [ae_mem_closedBall_circleMeasure x r] with z hz
    simp only [g, b.one_of_mem_closedBall hz, one_mul]
  simpa only [heq, integral_congr_ae hae] using hlim

/-- A common-support uniform approximation preserves weak convergence to the circle,
regardless of the heights of the continuous annular probability densities. -/
theorem tendsto_integral_testFn_mul_of_circleAnnular_approx
    (x : ℂ) (r : ℝ) (f : ℕ → TestFn) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 ≤ ε n) (hεlim : Tendsto ε atTop (𝓝 0))
    {R : ℝ} (hR : 0 < R)
    (hs : ∀ n, Function.support (f n) ⊆ closedBall (0 : ℂ) R)
    (hρs : ∀ n, Function.support (circleAnnularDensity x r n) ⊆ closedBall (0 : ℂ) R)
    (he : ∀ n z, |f n z - circleAnnularDensity x r n z| ≤ ε n)
    (k : ℂ → ℝ) (hk : Continuous k) :
    Tendsto (fun n => ∫ z, f n z * k z) atTop (𝓝 (∫ z, k z ∂circleMeasure x r)) := by
  let b : ContDiffBump (0 : ℂ) := ⟨R, R + 1, hR, lt_add_one R⟩
  let D : ℝ := ∫ z, |b z * k z|
  have hbi : Integrable (fun z => b z * k z) :=
    (b.continuous.mul hk).integrable_of_hasCompactSupport b.hasCompactSupport.mul_right
  have hfi n : Integrable (fun z => f n z * k z) :=
    ((f n).continuous.mul hk).integrable_of_hasCompactSupport (f n).hasCompactSupport.mul_right
  have hρi n : Integrable (fun z => circleAnnularDensity x r n z * k z) :=
    ((continuous_circleAnnularDensity x r n).mul hk).integrable_of_hasCompactSupport
      (hasCompactSupport_circleAnnularDensity x r n).mul_right
  have hbound n : |(∫ z, f n z * k z) - (∫ z, circleAnnularDensity x r n z * k z)| ≤ ε n * D := by
    let e : ℂ → ℝ := fun z => f n z - circleAnnularDensity x r n z
    have hes : Function.support e ⊆ closedBall (0 : ℂ) R := by
      intro z hz
      by_contra h
      have hf0 : f n z = 0 := by
        by_contra hne
        exact h (hs n hne)
      have hρ0 : circleAnnularDensity x r n z = 0 := by
        by_contra hne
        exact h (hρs n hne)
      exact hz (by simp [e, hf0, hρ0])
    have hei : Integrable (fun z => e z * k z) := by
      convert (hfi n).sub (hρi n) using 1
      ext z
      simp only [e, Pi.sub_apply]
      ring
    have hb := abs_integral_weighted_le volume e b k (ε n) hei hbi (fun _ => b.nonneg)
      (fun z => abs_le_bump_of_support hR (hε n) e hes (he n) z)
    have hval : (∫ z, f n z * k z) - (∫ z, circleAnnularDensity x r n z * k z) =
        ∫ z, e z * k z := by
      rw [← integral_sub (hfi n) (hρi n)]
      congr 1
      funext z
      dsimp [e]
      ring
    rw [hval]
    exact hb
  have hzero : Tendsto
      (fun n => (∫ z, f n z * k z) - (∫ z, circleAnnularDensity x r n z * k z))
      atTop (𝓝 0) := by
    have hlim : Tendsto (fun n => ε n * D) atTop (𝓝 0) := by
      simpa using hεlim.mul_const D
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using hlim.neg) hlim
    · intro n
      exact (abs_le.mp (hbound n)).1
    · intro n
      exact (abs_le.mp (hbound n)).2
  have hsum := hzero.add (tendsto_integral_circleAnnular_mul x r k hk)
  simpa only [sub_add_cancel, zero_add] using hsum

/-- Actual smooth energy approximants also converge against every continuous potential. -/
theorem exists_testFn_circleEnergyGap_and_integral_tendsto (x : ℂ) (r : ℝ) :
    ∃ f : ℕ → TestFn,
      Tendsto (fun n => circleEnergyGap x r (f n)) atTop (𝓝 0) ∧
      ∀ k : ℂ → ℝ, Continuous k → Tendsto (fun n => ∫ z, f n z * k z) atTop
        (𝓝 (∫ z, k z ∂circleMeasure x r)) := by
  obtain ⟨f, hs, he, hg⟩ := exists_testFn_circleEnergyGap_tendsto_zero x r
  refine ⟨f, hg, ?_⟩
  intro k hk
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    convert (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
      (tendsto_add_atTop_nat 2) using 1
    ext n
    simp [ε, Nat.cast_add]
  exact tendsto_integral_testFn_mul_of_circleAnnular_approx x r f ε
    (fun n => by dsimp [ε]; positivity) hεlim
    (R := ‖x‖ + 2 * Real.exp (-r) + 1) (by positivity)
    (fun n => (subset_tsupport _).trans (hs n))
    (fun n => (support_circleAnnularDensity_subset x r n).trans
      (closedBall_subset_closedBall (le_add_of_nonneg_right zero_le_one)))
    (fun n z => (he n z).le) k hk

/-- The same smooth tests simultaneously approximate every mixed circle pairing. -/
theorem exists_testFn_circleEnergyGap_and_cross_tendsto (x : ℂ) (r : ℝ) :
    ∃ f : ℕ → TestFn,
      Tendsto (fun n => circleEnergyGap x r (f n)) atTop (𝓝 0) ∧
      ∀ y s, Tendsto (fun n => circleCross y s (f n)) atTop
        (𝓝 (∫ z, ∫ w, gffKernel z w ∂circleMeasure y s ∂circleMeasure x r)) := by
  obtain ⟨f, hg, hw⟩ := exists_testFn_circleEnergyGap_and_integral_tendsto x r
  exact ⟨f, hg, fun y s => hw _ (continuous_circleKernelPotential y s)⟩


/-- The planar logarithmic singularity is locally integrable, from the stronger local
square-integrability estimate `DOZZ.integrable_log_norm_sq_on_ball`. -/
theorem locallyIntegrable_logNorm :
    LocallyIntegrable (fun z : ℂ => Real.log ‖z‖) volume := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  obtain ⟨R, _, hbound⟩ := hK.isBounded.exists_pos_norm_lt
  have hsub : K ⊆ ball (0 : ℂ) R := fun z hz => by
    simpa only [mem_ball, dist_zero_right] using hbound z hz
  have hfinite : IsFiniteMeasure (volume.restrict (ball (0 : ℂ) R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let _ := hfinite
  have hm : MemLp (fun z : ℂ => Real.log ‖z‖) 2
      (volume.restrict (ball (0 : ℂ) R)) :=
    DOZZ.memLp_two_of_integrable_norm_sq
      (Real.measurable_log.comp measurable_norm).aestronglyMeasurable
      (by simpa only [IntegrableOn, Real.norm_eq_abs, sq_abs] using DOZZ.integrable_log_norm_sq_on_ball R)
  have hi : IntegrableOn (fun z : ℂ => Real.log ‖z‖) (ball (0 : ℂ) R) volume :=
    hm.integrable (by norm_num)
  exact hi.mono_set hsub

/-- The potential of a smooth compact test is continuous despite the logarithmic singularity. -/
theorem continuous_testKernelPotential (f : TestFn) :
    Continuous (fun z : ℂ => ∫ w, gffKernel z w * f w) := by
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  have hloc : LocallyIntegrable (fun z : ℂ => -Real.log ‖z‖) volume :=
    locallyIntegrable_logNorm.neg
  have hrawc := f.hasCompactSupport.continuous_convolution_left
    (L := L) f.continuous hloc
  have hraw (z : ℂ) : Integrable (fun w => f w * (-Real.log ‖z - w‖)) :=
    f.hasCompactSupport.convolutionExists_left (L := L) f.continuous hloc z
  have hfi : Integrable f (volume : Measure ℂ) :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hpin : Integrable (fun w => f w * Real.log (normPlus w)) :=
    (f.continuous.mul continuous_log_normPlus).integrable_of_hasCompactSupport
      f.hasCompactSupport.mul_right
  have heq (z : ℂ) : (∫ w, gffKernel z w * f w) =
      (∫ w, f w * (-Real.log ‖z - w‖)) +
        Real.log (normPlus z) * (∫ w, f w) + (∫ w, f w * Real.log (normPlus w)) := by
    have hpoint w : gffKernel z w * f w =
        (f w * (-Real.log ‖z - w‖) + Real.log (normPlus z) * f w) +
          f w * Real.log (normPlus w) := by
      unfold gffKernel
      ring
    simp_rw [hpoint]
    have hfirst := integral_add (hraw z) (hfi.const_mul (Real.log (normPlus z)))
    have hsecond := integral_add ((hraw z).add (hfi.const_mul (Real.log (normPlus z)))) hpin
    simp only [Pi.add_apply] at hfirst hsecond
    rw [hsecond, hfirst, integral_const_mul]
  simp_rw [heq]
  have hrawc' : Continuous (fun z : ℂ => ∫ w, f w * (-Real.log ‖z - w‖)) := hrawc
  exact (hrawc'.add (continuous_log_normPlus.mul_const (∫ w, f w))).add continuous_const

/-- Every section of the pinned kernel weighted by a smooth compact test is integrable. -/
theorem integrable_testKernel_section (f : TestFn) (z : ℂ) :
    Integrable (fun w => gffKernel z w * f w) := by
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  have hloc := locallyIntegrable_logNorm.neg
  have hraw : Integrable (fun w => f w * (-Real.log ‖z - w‖)) :=
    f.hasCompactSupport.convolutionExists_left (L := L) f.continuous hloc z
  have hfi : Integrable f (volume : Measure ℂ) := f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hpin : Integrable (fun w => f w * Real.log (normPlus w)) :=
    (f.continuous.mul continuous_log_normPlus).integrable_of_hasCompactSupport f.hasCompactSupport.mul_right
  convert ((hraw.add (hfi.const_mul (Real.log (normPlus z)))).add hpin) using 1
  ext w
  simp only [Pi.add_apply, gffKernel]
  ring

end DOZZ.Proofs

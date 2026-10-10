/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.InverseLimit
public import DOZZ.GMC.SharpMoments.LocationTransfer
public import DOZZ.GMC.SharpMoments.ReverseJensen
public import DOZZ.GMC.FieldChaosConvexPower
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Inverse moments uniform in the coupling constant

Where the circle covariance is nonnegative, the field `γ X_r` has entrywise smaller covariance
than `g X_r` for `γ ≤ g`; writing the `γ`-chaos as the `g`-chaos of `(γ/g) X_r`, the convex Kahane
comparison bounds every inverse moment at `γ` by the one at `g`. With the coarse-cutoff Jensen
bound, exact scaling and the location transfer, this gives inverse moments of cutoff masses of
nonempty open sets, uniformly in the cutoff and in `γ` on compact subsets of `(0,2)`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- A constant multiple of the circle field is a jointly measurable centered Gaussian field. -/
theorem circleAverage_smul_isCenteredGaussianField
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (r c : ℝ) :
    IsCenteredGaussianField P (fun ω x => c * Xc ω x r) :=
  ⟨(hXc.1 r).const_mul c, fun _ x => isCenteredJointlyGaussian_coord_mul P _
    (circleAverage_finite_family_jointly_gaussian P X hX Xc hXc (fun i => (x i, r)))
    (fun _ => c)⟩

/-- The `γ`-chaos is the `g`-chaos of the circle field scaled by `γ / g`. -/
theorem regularizedGMC_apply_eq_fieldChaosMass_scaled
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ g r : ℝ) (hg : g ≠ 0)
    (A : Set ℂ) (hA : MeasurableSet A) (ω : Ω) :
    regularizedGMC P Xc γ r ω A =
      fieldChaosMass P (fun ω x => γ / g * Xc ω x r) (gmcReferenceMeasure.restrict A)
        (fun _ => 1) g ω := by
  rw [regularizedGMC_apply_eq_fieldChaosMass P X hX Xc hXc γ r A hA ω]
  unfold fieldChaosMass
  apply lintegral_congr
  intro x
  congr 3
  have hsq : (fun ω' => (γ / g * Xc ω' x r) ^ 2) = fun ω' => (γ / g) ^ 2 * Xc ω' x r ^ 2 := by
    funext ω'
    ring
  rw [hsq, integral_const_mul]
  field_simp

/-- Inverse moments are monotone in `γ` on a set where the circle covariance is nonnegative. -/
theorem regularizedGMC_inverse_moment_le_of_gamma_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ g r : ℝ) (hγ : 0 < γ)
    (hγg : γ ≤ g) (A : Set ℂ) (hA : MeasurableSet A) (hAtop : gmcReferenceMeasure A ≠ ⊤)
    (hnn : ∀ x ∈ A, ∀ y ∈ A, 0 ≤ ∫ ω, Xc ω x r * Xc ω y r ∂P) (q : ℝ) (hq : 0 ≤ q) :
    ∫⁻ ω, (regularizedGMC P Xc γ r ω A) ^ (-q) ∂P ≤
      ∫⁻ ω, (regularizedGMC P Xc g r ω A) ^ (-q) ∂P := by
  have hg : 0 < g := lt_of_lt_of_le hγ hγg
  set c : ℝ := γ / g with hc
  have hc0 : 0 ≤ c := div_nonneg hγ.le hg.le
  have hc1 : c ≤ 1 := (div_le_one hg).mpr hγg
  have hc2 : c ^ 2 ≤ 1 := pow_le_one₀ hc0 hc1
  set ν : Measure ℂ := gmcReferenceMeasure.restrict A with hν
  have hνfin : IsFiniteMeasure ν := by
    rw [hν]
    exact isFiniteMeasure_restrict.mpr hAtop
  have hΦ := circleAverage_smul_isCenteredGaussianField P X hX Xc hXc r c
  have hΨ := circleAverage_isCenteredGaussianField P X hX Xc hXc r
  have hmemA : ∀ᵐ x ∂ν, x ∈ A := by
    rw [hν]
    exact ae_restrict_mem hA
  have hcov : ∀ᵐ q ∂ν.prod ν,
      ∫ ω, c * Xc ω q.1 r * (c * Xc ω q.2 r) ∂P ≤ ∫ ω, Xc ω q.1 r * Xc ω q.2 r ∂P := by
    have hprod : ν.prod ν = (gmcReferenceMeasure.prod gmcReferenceMeasure).restrict (A ×ˢ A) := by
      have : IsFiniteMeasure gmcReferenceMeasure := ⟨gmcReferenceMeasure_univ_ne_top.lt_top⟩
      rw [hν, Measure.prod_restrict]
    rw [hprod]
    filter_upwards [ae_restrict_mem (hA.prod hA)] with q hq
    have hfun : (fun ω => c * Xc ω q.1 r * (c * Xc ω q.2 r)) =
        fun ω => c ^ 2 * (Xc ω q.1 r * Xc ω q.2 r) := by
      funext ω
      ring
    rw [hfun, integral_const_mul]
    have h0 := hnn q.1 hq.1 q.2 hq.2
    exact mul_le_of_le_one_left h0 hc2
  have hdiag : ∀ᵐ x ∂ν, ∫ ω, (c * Xc ω x r) ^ 2 ∂P ≤ ∫ ω, Xc ω x r ^ 2 ∂P := by
    filter_upwards [] with x
    have hfun : (fun ω => (c * Xc ω x r) ^ 2) = fun ω => c ^ 2 * Xc ω x r ^ 2 := by
      funext ω
      ring
    rw [hfun, integral_const_mul]
    have h0 : 0 ≤ ∫ ω, Xc ω x r ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
    exact mul_le_of_le_one_left h0 hc2
  have hk := kahane_field_power_convex P P (fun ω x => c * Xc ω x r) (fun ω x => Xc ω x r)
    hΦ hΨ ν (fun _ => 1) measurable_const ⟨1, fun _ => le_rfl⟩ g (-q) (Or.inl (by linarith))
    hcov hdiag
  have hleft : ∀ ω, regularizedGMC P Xc γ r ω A =
      fieldChaosMass P (fun ω x => c * Xc ω x r) ν (fun _ => 1) g ω :=
    fun ω => regularizedGMC_apply_eq_fieldChaosMass_scaled P X hX Xc hXc γ g r hg.ne' A hA ω
  have hright : ∀ ω, regularizedGMC P Xc g r ω A =
      fieldChaosMass P (fun ω x => Xc ω x r) ν (fun _ => 1) g ω :=
    fun ω => regularizedGMC_apply_eq_fieldChaosMass P X hX Xc hXc g r A hA ω
  simp only [hleft, hright]
  exact hk

/-- The circle covariance is nonnegative on the reference disk at cutoffs `r ≥ 1`. -/
theorem circleField_covariance_nonneg_reference
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (r : ℝ) (hr : 1 ≤ r)
    (x : ℂ) (hx : x ∈ Metric.ball (0 : ℂ) (1 / 8)) (y : ℂ) (hy : y ∈ Metric.ball (0 : ℂ) (1 / 8)) :
    0 ≤ ∫ ω, Xc ω x r * Xc ω y r ∂P := by
  apply circleField_covariance_nonneg P X hX Xc hXc x y r
  rw [Metric.mem_ball, dist_zero_right] at hx hy
  have hxy : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
  have he : Real.exp (-r) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
  have he1 : Real.exp (-1) ≤ 3 / 8 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
    have := Real.exp_one_gt_d9
    linarith
  linarith

/-- Coarse cutoffs: Jensen's bound on inverse moments, uniformly in `γ ≤ 2`. -/
theorem regularizedGMC_inverse_moment_le_coarse_uniform
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (ρ T : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hT : 0 ≤ T) (q : ℝ) (hq : 0 < q) (r : ℝ) (hr : 0 ≤ r)
    (hrT : r ≤ T) :
    ∫⁻ ω, (regularizedGMC P Xc γ r ω (Metric.ball 0 ρ)) ^ (-q) ∂P ≤
      gmcReferenceMeasure (Metric.ball (0 : ℂ) ρ) ^ (-q) *
        ENNReal.ofReal (Real.exp (4 * (q ^ 2 + q) / 2 * (T + gmcCircleChartRemainder ρ))) := by
  have hA0 : gmcReferenceMeasure (Metric.ball (0 : ℂ) ρ) ≠ 0 :=
    (gmc_reference_ball_intensity_pos hρ hρ1).ne'
  have hAtop : gmcReferenceMeasure (Metric.ball (0 : ℂ) ρ) ≠ ⊤ :=
    ne_top_of_le_ne_top gmcReferenceMeasure_univ_ne_top (measure_mono (Set.subset_univ _))
  have hV : ∀ x ∈ Metric.ball (0 : ℂ) ρ,
      gaussianVariance P (fun ω => Xc ω x r) ≤ T + gmcCircleChartRemainder ρ := by
    intro x hx
    rw [Metric.mem_ball, dist_zero_right] at hx
    exact gmcCircle_variance_le_coarse_chart P X hX Xc hXc ρ r T hρ.le hr hrT x hx.le
  have h := regularizedGMC_inverse_moment_le_variance P X hX Xc hXc γ r q
    (T + gmcCircleChartRemainder ρ) hq (Metric.ball 0 ρ) Metric.isOpen_ball.measurableSet hA0
    hAtop hV
  have hVnn : 0 ≤ T + gmcCircleChartRemainder ρ :=
    add_nonneg hT (gmcCircleChartRemainder_nonneg hρ.le)
  have hγsq : γ ^ 2 ≤ 4 := (pow_le_pow_left₀ hγ.le hγ2.le 2).trans (by norm_num)
  have hexp : γ ^ 2 * (q ^ 2 + q) / 2 * (T + gmcCircleChartRemainder ρ) ≤
      4 * (q ^ 2 + q) / 2 * (T + gmcCircleChartRemainder ρ) := by
    have hq2 : 0 ≤ q ^ 2 + q := by positivity
    have : γ ^ 2 * (q ^ 2 + q) / 2 ≤ 4 * (q ^ 2 + q) / 2 := by
      linarith only [mul_le_mul_of_nonneg_right hγsq hq2]
    exact mul_le_mul_of_nonneg_right this hVnn
  refine h.trans ?_
  gcongr _ * ENNReal.ofReal (Real.exp ?_)

/-- Inverse moments of the reference disk mass, uniformly in the cutoff and in `γ` on a compact
subset of `(0,2)`. -/
theorem regularizedGMC_reference_inverse_moment_uniform_gamma
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (Γ : Set ℝ) (hΓ : IsCompact Γ) (hΓ2 : Γ ⊆ Set.Ioo (0 : ℝ) 2) (q : ℝ) (hq : 0 < q) :
    ∃ K : ℝ, ∀ γ ∈ Γ, ∀ r : ℝ, 0 ≤ r →
      ∫⁻ ω, (regularizedGMC P Xc γ r ω (Metric.ball 0 (1 / 8))) ^ (-q) ∂P ≤
        ENNReal.ofReal K := by
  rcases Γ.eq_empty_or_nonempty with hempty | hne
  · exact ⟨0, fun γ hγ => by simp [hempty] at hγ⟩
  set g : ℝ := sSup Γ with hgdef
  have hgΓ : g ∈ Γ := hΓ.sSup_mem hne
  have hg := hΓ2 hgΓ
  obtain ⟨K₁, hK₁⟩ := regularizedGMC_reference_inverse_moment_uniform P X hX Xc hXc g hg.1 hg.2
    q hq
  set B : ℝ≥0∞ := gmcReferenceMeasure (Metric.ball (0 : ℂ) (1 / 8)) ^ (-q) *
    ENNReal.ofReal (Real.exp (4 * (q ^ 2 + q) / 2 * (1 + gmcCircleChartRemainder (1 / 8))))
    with hB
  have hBtop : B ≠ ⊤ := by
    have hA0 : gmcReferenceMeasure (Metric.ball (0 : ℂ) (1 / 8)) ≠ 0 :=
      (gmc_reference_ball_intensity_pos (by norm_num) (by norm_num)).ne'
    have hAtop : gmcReferenceMeasure (Metric.ball (0 : ℂ) (1 / 8)) ≠ ⊤ :=
      ne_top_of_le_ne_top gmcReferenceMeasure_univ_ne_top (measure_mono (Set.subset_univ _))
    rw [hB]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_ne_zero hA0 hAtop) ENNReal.ofReal_ne_top
  refine ⟨max K₁ B.toReal, fun γ hγ r hr => ?_⟩
  have hγ' := hΓ2 hγ
  have hγg : γ ≤ g := le_csSup hΓ.bddAbove hγ
  by_cases hr1 : 1 ≤ r
  · have hcmp := regularizedGMC_inverse_moment_le_of_gamma_le P X hX Xc hXc γ g r hγ'.1 hγg
      (Metric.ball 0 (1 / 8)) Metric.isOpen_ball.measurableSet
      (ne_top_of_le_ne_top gmcReferenceMeasure_univ_ne_top (measure_mono (Set.subset_univ _)))
      (fun x hx y hy => circleField_covariance_nonneg_reference P X hX Xc hXc r hr1 x hx y hy)
      q hq.le
    exact hcmp.trans ((hK₁ r hr).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
  · have hbase := regularizedGMC_inverse_moment_le_coarse_uniform P X hX Xc hXc γ hγ'.1 hγ'.2
      (1 / 8) 1 (by norm_num) (by norm_num) zero_le_one q hq r hr (le_of_lt (lt_of_not_ge hr1))
    refine hbase.trans ?_
    rw [← hB]
    calc B = ENNReal.ofReal B.toReal := (ENNReal.ofReal_toReal hBtop).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (le_max_right _ _)

/-- Inverse moments of every small centered disk, uniformly in the cutoff and in `γ`. -/
theorem regularizedGMC_ball_inverse_moment_uniform_gamma
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (Γ : Set ℝ) (hΓ : IsCompact Γ) (hΓ2 : Γ ⊆ Set.Ioo (0 : ℝ) 2) (q : ℝ) (hq : 0 < q)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8) :
    ∃ K : ℝ, ∀ γ ∈ Γ, ∀ t : ℝ, 0 ≤ t →
      ∫⁻ ω, (regularizedGMC P Xc γ t ω (Metric.ball 0 ρ)) ^ (-q) ∂P ≤ ENNReal.ofReal K := by
  obtain ⟨K₀, hK₀⟩ := regularizedGMC_reference_inverse_moment_uniform_gamma P X hX Xc hXc Γ hΓ
    hΓ2 q hq
  set t₁ : ℝ := max 1 (Real.log (1 / (7 * ρ))) with ht₁
  set B : ℝ≥0∞ := gmcReferenceMeasure (Metric.ball (0 : ℂ) ρ) ^ (-q) *
    ENNReal.ofReal (Real.exp (4 * (q ^ 2 + q) / 2 * (t₁ + gmcCircleChartRemainder ρ))) with hB
  have hA0 : gmcReferenceMeasure (Metric.ball (0 : ℂ) ρ) ≠ 0 :=
    (gmc_reference_ball_intensity_pos hρ (by linarith)).ne'
  have hBtop : B ≠ ⊤ := by
    have hAtop : gmcReferenceMeasure (Metric.ball (0 : ℂ) ρ) ≠ ⊤ :=
      ne_top_of_le_ne_top gmcReferenceMeasure_univ_ne_top (measure_mono (Set.subset_univ _))
    rw [hB]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_ne_zero hA0 hAtop) ENNReal.ofReal_ne_top
  set F : ℝ := (8 * ρ) ^ (-(4 * q + 2 * q ^ 2)) with hF
  refine ⟨max (F * max K₀ 0) B.toReal, fun γ hγ t ht => ?_⟩
  have hγ' := hΓ2 hγ
  by_cases htbig : t₁ ≤ t
  · have ht1 : 1 ≤ t := (le_max_left _ _).trans htbig
    have htlog : Real.log (1 / (7 * ρ)) ≤ t := (le_max_right _ _).trans htbig
    have hexp7 : Real.exp (-t) ≤ 7 * ρ := by
      have h := Real.exp_le_exp.mpr (neg_le_neg htlog)
      rwa [Real.exp_neg (Real.log _), Real.exp_log (by positivity), one_div, inv_inv] at h
    have hexp1 : Real.exp (-t) ≤ 1 / 2 := by
      have h1 : Real.exp (-t) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
      have h2 : Real.exp (-1) ≤ 1 / 2 := by
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
        have := Real.add_one_le_exp (1 : ℝ)
        linarith
      linarith
    have hscale := regularizedGMC_local_ball_moment_scale P X hX γ Xc hXc 0 (s := ρ) (R := 1 / 8)
      (t := t) hρ hρ8 (by norm_num) (by norm_num) (by simp; linarith)
      (by
        have : Real.exp (-t) * (1 / 8 / ρ) ≤ 7 / 8 := by
          calc Real.exp (-t) * (1 / 8 / ρ) ≤ 7 * ρ * (1 / 8 / ρ) :=
                mul_le_mul_of_nonneg_right hexp7 (by positivity)
            _ = 7 / 8 := by field_simp
        linarith)
      (by simp; linarith) (-q)
    have hsrc : 0 ≤ t + Real.log (ρ / (1 / 8)) := by
      have h8 : Real.log (ρ / (1 / 8)) = Real.log (8 * ρ) := by congr 1; field_simp
      rw [h8]
      have hlog : Real.log (1 / (7 * ρ)) + Real.log (8 * ρ) = Real.log (8 / 7) := by
        rw [← Real.log_mul (by positivity) (by positivity)]
        congr 1
        field_simp
      have h87 : 0 ≤ Real.log (8 / 7) := Real.log_nonneg (by norm_num)
      linarith
    change gmcMassMoment P (regularizedGMC P Xc γ t) (Metric.ball 0 ρ) (-q) ≤ _
    rw [hscale]
    have hfac : ENNReal.ofReal ((ρ / (1 / 8)) ^ (2 * -q + γ ^ 2 * -q / 2 - γ ^ 2 * (-q) ^ 2 / 2)) ≤
        ENNReal.ofReal F := by
      apply ENNReal.ofReal_le_ofReal
      rw [hF, show ρ / (1 / 8) = 8 * ρ by field_simp]
      apply Real.rpow_le_rpow_of_exponent_ge (by positivity) (by linarith)
      have hγsq : γ ^ 2 ≤ 4 := (pow_le_pow_left₀ hγ'.1.le hγ'.2.le 2).trans (by norm_num)
      linarith only [mul_le_mul_of_nonneg_right hγsq hq.le,
        mul_le_mul_of_nonneg_right hγsq (sq_nonneg q)]
    calc ENNReal.ofReal ((ρ / (1 / 8)) ^ (2 * -q + γ ^ 2 * -q / 2 - γ ^ 2 * (-q) ^ 2 / 2)) *
          gmcMassMoment P (regularizedGMC P Xc γ (t + Real.log (ρ / (1 / 8))))
            (Metric.ball 0 (1 / 8)) (-q)
        ≤ ENNReal.ofReal F * ENNReal.ofReal (max K₀ 0) := by
          gcongr
          exact (hK₀ γ hγ _ hsrc).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
      _ = ENNReal.ofReal (F * max K₀ 0) := by
          rw [← ENNReal.ofReal_mul (by rw [hF]; positivity)]
      _ ≤ ENNReal.ofReal (max (F * max K₀ 0) B.toReal) :=
          ENNReal.ofReal_le_ofReal (le_max_left _ _)
  · have hbase := regularizedGMC_inverse_moment_le_coarse_uniform P X hX Xc hXc γ hγ'.1 hγ'.2
      ρ t₁ hρ (by linarith) (le_trans zero_le_one (le_max_left _ _)) q hq t ht
      (le_of_lt (lt_of_not_ge htbig))
    refine hbase.trans ?_
    rw [← hB]
    calc B = ENNReal.ofReal B.toReal := (ENNReal.ofReal_toReal hBtop).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (le_max_right _ _)

/-- Every inverse moment of the circle-average cutoff mass of a nonempty open set is bounded
uniformly in the cutoff and in `γ` on compact subsets of `(0,2)`. -/
theorem equatorGFF_regularizedGMC_inverse_moment_uniform
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (Γ : Set ℝ) (hΓ : IsCompact Γ) (hΓ2 : Γ ⊆ Set.Ioo (0 : ℝ) 2)
    (O : Set ℂ) (hO : IsOpen O) (hOne : O.Nonempty) (q : ℝ) (hq : 0 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ ∈ Γ, ∀ r : ℝ, 0 ≤ r →
      (∫⁻ ω, ENNReal.rpow (regularizedGMC P Xc γ r ω O) (-q) ∂P) ≤ ENNReal.ofReal C := by
  obtain ⟨z, hz⟩ := hOne
  obtain ⟨ρ₀, hρ₀, hballO⟩ := Metric.isOpen_iff.mp hO z hz
  set ρ : ℝ := min ρ₀ (1 / 8) with hρdef
  have hρ : 0 < ρ := lt_min hρ₀ (by norm_num)
  have hρ8 : ρ ≤ 1 / 8 := min_le_right _ _
  have hsub : Metric.ball z ρ ⊆ O := (Metric.ball_subset_ball (min_le_left _ _)).trans hballO
  obtain ⟨K, hK⟩ := regularizedGMC_ball_inverse_moment_uniform_gamma P X hX Xc hXc Γ hΓ hΓ2 q hq
    ρ hρ hρ8
  set R : ℝ := ‖z‖ + ρ with hRdef
  have hR : 0 ≤ R := by positivity
  set E : ℝ := Real.exp (4 * (2 * (Real.log 3 + 2 * Real.log (1 + R))) / 2 * (q ^ 2 + q)) *
    ((1 + R) ^ 4) ^ q with hEdef
  have hE : 0 < E := by
    rw [hEdef]
    exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (by positivity) _)
  refine ⟨E * max K 1, mul_pos hE (lt_of_lt_of_le zero_lt_one (le_max_right _ _)),
    fun γ hγ r hr => ?_⟩
  have hγ' := hΓ2 hγ
  -- shrink `O` to the ball
  have hmono : (∫⁻ ω, ENNReal.rpow (regularizedGMC P Xc γ r ω O) (-q) ∂P) ≤
      ∫⁻ ω, (regularizedGMC P Xc γ r ω (Metric.ball z ρ)) ^ (-q) ∂P := by
    apply lintegral_mono
    intro ω
    exact ennreal_rpow_antitone_of_nonpos (measure_mono hsub) (by linarith)
  -- transfer the ball to the origin
  have htr := cutoff_translate_moment_le P X hX Xc hXc γ r hr z 0 ρ R hR le_rfl (by simp [hRdef])
    (fun _ => 1) measurable_const 1 (fun _ => le_rfl) (-q)
  have hone : ∀ (c : ℂ) (ω : Ω), (∫⁻ x in Metric.ball c ρ, ((fun _ : ℂ => (1 : ℝ≥0)) (x - c) :
      ℝ≥0∞) ∂regularizedGMC P Xc γ r ω) = regularizedGMC P Xc γ r ω (Metric.ball c ρ) := by
    intro c ω
    simp
  simp only [hone] at htr
  have habs1 : |(-q) ^ 2 - -q| = q ^ 2 + q := by
    rw [show (-q) ^ 2 - -q = q ^ 2 + q by ring]
    exact abs_of_nonneg (by positivity)
  have habs2 : |-q| = q := by rw [abs_neg, abs_of_pos hq]
  rw [habs1, habs2] at htr
  have hfactor : ENNReal.ofReal (Real.exp (γ ^ 2 * (2 * (Real.log 3 + 2 * Real.log (1 + R))) / 2 *
      (q ^ 2 + q))) * ENNReal.ofReal ((1 + R) ^ 4) ^ q ≤ ENNReal.ofReal E := by
    have hγsq : γ ^ 2 ≤ 4 := (pow_le_pow_left₀ hγ'.1.le hγ'.2.le 2).trans (by norm_num)
    rw [hEdef, ENNReal.ofReal_mul (Real.exp_pos _).le,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) hq.le]
    gcongr ENNReal.ofReal (Real.exp ?_) * _
    have hlog : 0 ≤ 2 * (Real.log 3 + 2 * Real.log (1 + R)) := by
      have h3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
      have h1 : 0 ≤ Real.log (1 + R) := Real.log_nonneg (by linarith)
      positivity
    have hq2 : 0 ≤ q ^ 2 + q := by positivity
    have := mul_le_mul_of_nonneg_right hγsq hlog
    linarith only [mul_le_mul_of_nonneg_right this hq2]
  calc (∫⁻ ω, ENNReal.rpow (regularizedGMC P Xc γ r ω O) (-q) ∂P)
      ≤ ∫⁻ ω, (regularizedGMC P Xc γ r ω (Metric.ball z ρ)) ^ (-q) ∂P := hmono
    _ ≤ _ := htr
    _ ≤ ENNReal.ofReal E * ENNReal.ofReal (max K 1) := by
        gcongr
        exact (hK γ hγ r hr).trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    _ = ENNReal.ofReal (E * max K 1) := (ENNReal.ofReal_mul hE.le).symm

end DOZZ.Proofs

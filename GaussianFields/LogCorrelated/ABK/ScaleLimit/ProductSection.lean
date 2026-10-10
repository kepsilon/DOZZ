/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import GaussianFields.LogCorrelated.ABK.Covariance
public import GaussianFields.LogCorrelated.ABK.RegularizedCovariance
public import GaussianFields.LogCorrelated.ABK.SingularIntegrability

/-!
# GaussianFields ABK scale product section

Port of the corresponding GaussianFields source module.
-/

public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace NNReal ProbabilityTheory Topology

namespace GaussianFields


/-- Scalar inequality used to bound a product by square masses. -/
theorem abs_mul_le_half_sq_add_sq (a b : ℝ) :
    |a * b| ≤ (a ^ (2 : Nat) + b ^ (2 : Nat)) / 2 := by
  have htwo_pos : (0 : ℝ) < 2 := by norm_num
  by_cases h : 0 ≤ a * b
  · rw [abs_of_nonneg h, le_div_iff₀ htwo_pos]
    nlinarith [two_mul_le_add_sq a b]
  · have hneg : a * b < 0 := lt_of_not_ge h
    rw [abs_of_neg hneg, le_div_iff₀ htwo_pos]
    nlinarith [two_mul_le_add_sq a (-b)]

/-- The fixed-scale product section of two unnormalized ABK kernels. -/
@[expose]
noncomputable def abkScaleProductSection {d : Nat}
    (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d) (r : ℝ) : ℝ :=
  ∫ y : Vec d,
    abkLogKernelProd 1 ζ ψ (r, y) *
      abkLogKernelProd 1 ζ φ (r, y)
    ∂(volume : Measure (Vec d))

/-- Abel-regularized scale product section. -/
@[expose]
noncomputable def abkRegularizedScaleProductSection {d : Nat}
    (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d) (α r : ℝ) : ℝ :=
  if 0 < r then
    r ^ (-α) * abkScaleProductSection ζ ψ φ r
  else
    0

/-- The product section is a.e. strongly measurable in the scale variable. -/
theorem aestronglyMeasurable_abkScaleProductSection {d : Nat}
    (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d) :
    AEStronglyMeasurable (abkScaleProductSection ζ ψ φ) (volume : Measure ℝ) := by
  let μ : Measure (ℝ × Vec d) :=
    (volume : Measure ℝ).prod (volume : Measure (Vec d))
  have hψ :
      AEStronglyMeasurable (abkLogKernelProd 1 ζ ψ) μ :=
    aestronglyMeasurable_abkLogKernelProd 1 ζ ψ μ
  have hφ :
      AEStronglyMeasurable (abkLogKernelProd 1 ζ φ) μ :=
    aestronglyMeasurable_abkLogKernelProd 1 ζ φ μ
  have hprod :
      AEStronglyMeasurable
        (fun p : ℝ × Vec d =>
          abkLogKernelProd 1 ζ ψ p * abkLogKernelProd 1 ζ φ p) μ :=
    hψ.mul hφ
  change AEStronglyMeasurable
    (fun r : ℝ =>
      ∫ y : Vec d,
        abkLogKernelProd 1 ζ ψ (r, y) * abkLogKernelProd 1 ζ φ (r, y)
        ∂(volume : Measure (Vec d)))
    (volume : Measure ℝ)
  exact hprod.integral_prod_right'

/-- The Abel-regularized product section is a.e. strongly measurable for nonzero `α`. -/
theorem aestronglyMeasurable_abkRegularizedScaleProductSection_of_ne {d : Nat}
    (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d) {α : ℝ} (_hα : α ≠ 0) :
    AEStronglyMeasurable (abkRegularizedScaleProductSection ζ ψ φ α)
      (volume : Measure ℝ) := by
  let S : Set ℝ := Set.Ioi 0
  have hS : MeasurableSet S := measurableSet_Ioi
  have hbase :
      AEStronglyMeasurable (abkScaleProductSection ζ ψ φ) (volume : Measure ℝ) :=
    aestronglyMeasurable_abkScaleProductSection ζ ψ φ
  have hpow :
      AEStronglyMeasurable (fun r : ℝ => r ^ (-α))
        ((volume : Measure ℝ).restrict S) := by
    refine ContinuousOn.aestronglyMeasurable ?_ hS
    exact continuous_id.continuousOn.rpow_const fun r hr =>
      Or.inl (ne_of_gt hr)
  have hpos :
      AEStronglyMeasurable
        (fun r : ℝ => r ^ (-α) * abkScaleProductSection ζ ψ φ r)
        ((volume : Measure ℝ).restrict S) :=
    hpow.mul hbase.restrict
  have hzero :
      AEStronglyMeasurable (fun _ : ℝ => (0 : ℝ))
        ((volume : Measure ℝ).restrict Sᶜ) :=
    aestronglyMeasurable_const
  have hpiece :
      AEStronglyMeasurable
        (S.piecewise
          (fun r : ℝ => r ^ (-α) * abkScaleProductSection ζ ψ φ r)
          (fun _ : ℝ => 0))
        (volume : Measure ℝ) :=
    AEStronglyMeasurable.piecewise hS hpos hzero
  refine hpiece.congr ?_
  filter_upwards with r
  by_cases hr : r ∈ S
  · have hrpos : 0 < r := by simpa [S] using hr
    simp [abkRegularizedScaleProductSection, Set.piecewise_eq_of_mem, hr, hrpos]
  · have hrpos : ¬ 0 < r := by simpa [S] using hr
    simp [abkRegularizedScaleProductSection, Set.piecewise_eq_of_notMem, hr, hrpos]

/-- Near `α = 0+`, the Abel-regularized product sections are a.e. strongly measurable. -/
theorem eventually_aestronglyMeasurable_abkRegularizedScaleProductSection {d : Nat}
    (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d) :
    ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ),
      AEStronglyMeasurable (abkRegularizedScaleProductSection ζ ψ φ α)
        (volume : Measure ℝ) := by
  filter_upwards [self_mem_nhdsWithin] with α hα
  exact aestronglyMeasurable_abkRegularizedScaleProductSection_of_ne
    ζ ψ φ hα.ne'

/-- Pointwise Abel limit of the regularized scale sections. -/
theorem tendsto_abkRegularizedScaleProductSection_at {d : Nat}
    (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d) (r : ℝ) :
    Tendsto (fun α : ℝ => abkRegularizedScaleProductSection ζ ψ φ α r)
      (𝓝[>] (0 : ℝ)) (𝓝 (abkScaleProductSection ζ ψ φ r)) := by
  by_cases hr : 0 < r
  · have hr_ne : r ≠ 0 := ne_of_gt hr
    have hpow :
        Tendsto (fun α : ℝ => r ^ (-α)) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
      have hcont :
          ContinuousAt (fun α : ℝ => r ^ (-α)) 0 := by
        exact ContinuousAt.comp (x := (0 : ℝ)) (f := fun α : ℝ => -α)
          (g := fun t : ℝ => r ^ t)
          (by
            simpa using
              (Real.continuousAt_const_rpow (a := r) (b := (0 : ℝ)) hr_ne))
          (continuousAt_neg (x := (0 : ℝ)))
      simpa [Real.rpow_zero] using hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hlim := hpow.const_mul (abkScaleProductSection ζ ψ φ r)
    simpa [abkRegularizedScaleProductSection, hr, mul_comm] using hlim
  · have hzero :
        (fun α : ℝ => abkRegularizedScaleProductSection ζ ψ φ α r) =
          fun _ : ℝ => 0 := by
      funext α
      simp [abkRegularizedScaleProductSection, hr]
    have hsection_zero : abkScaleProductSection ζ ψ φ r = 0 := by
      unfold abkScaleProductSection
      refine integral_eq_zero_of_ae ?_
      filter_upwards with y
      simp [abkLogKernelProd, hr]
    rw [hzero, hsection_zero]
    exact tendsto_const_nhds

/-- A.e. pointwise Abel limit of the regularized scale sections. -/
theorem ae_tendsto_abkRegularizedScaleProductSection {d : Nat}
    (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d) :
    ∀ᵐ r : ℝ ∂(volume : Measure ℝ),
      Tendsto (fun α : ℝ => abkRegularizedScaleProductSection ζ ψ φ α r)
        (𝓝[>] (0 : ℝ)) (𝓝 (abkScaleProductSection ζ ψ φ r)) := by
  exact Filter.Eventually.of_forall
    (tendsto_abkRegularizedScaleProductSection_at ζ ψ φ)

/-- At a positive fixed scale, an ABK product-kernel spatial section is continuous. -/
theorem continuous_abkLogKernelProd_section_of_pos {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) {r : ℝ} (hr : 0 < r) :
    Continuous (fun y : Vec d => abkLogKernelProd normalization ζ ψ (r, y)) := by
  let c : ℝ := normalization * r ^ (-(((d : ℝ) + 1) / 2))
  have hfun :
      (fun y : Vec d => abkLogKernelProd normalization ζ ψ (r, y)) =
        fun y : Vec d => c * abkSpatialConvolution ζ ψ r y := by
    funext y
    simp [abkLogKernelProd, hr, c]
  rw [hfun]
  exact continuous_const.mul (continuous_abkSpatialConvolution ζ ψ hr.ne')

/-- At a positive fixed scale, an ABK product-kernel spatial section has compact support. -/
theorem hasCompactSupport_abkLogKernelProd_section_of_pos {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (fun y : Vec d => abkLogKernelProd normalization ζ ψ (r, y)) := by
  let c : ℝ := normalization * r ^ (-(((d : ℝ) + 1) / 2))
  have hfun :
      (fun y : Vec d => abkLogKernelProd normalization ζ ψ (r, y)) =
        fun y : Vec d => c * abkSpatialConvolution ζ ψ r y := by
    funext y
    simp [abkLogKernelProd, hr, c]
  rw [hfun]
  exact (hasCompactSupport_abkSpatialConvolution ζ ψ hr).mul_left

/-- The fixed-scale product of two ABK product-kernel sections is integrable. -/
theorem integrable_abkLogKernelProd_mul_section {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d) (r : ℝ) :
    Integrable
      (fun y : Vec d =>
        abkLogKernelProd normalization ζ ψ (r, y) *
          abkLogKernelProd normalization ζ φ (r, y))
      (volume : Measure (Vec d)) := by
  by_cases hr : 0 < r
  · have hcont :
        Continuous
          (fun y : Vec d =>
            abkLogKernelProd normalization ζ ψ (r, y) *
              abkLogKernelProd normalization ζ φ (r, y)) :=
      (continuous_abkLogKernelProd_section_of_pos normalization ζ ψ hr).mul
        (continuous_abkLogKernelProd_section_of_pos normalization ζ φ hr)
    have hcs :
        HasCompactSupport
          (fun y : Vec d =>
            abkLogKernelProd normalization ζ ψ (r, y) *
              abkLogKernelProd normalization ζ φ (r, y)) :=
      (hasCompactSupport_abkLogKernelProd_section_of_pos normalization ζ φ hr).mul_left
    exact hcont.integrable_of_hasCompactSupport hcs
  · have hzero :
        (fun y : Vec d =>
          abkLogKernelProd normalization ζ ψ (r, y) *
            abkLogKernelProd normalization ζ φ (r, y)) =
          fun _ : Vec d => 0 := by
      funext y
      simp [abkLogKernelProd, hr]
    rw [hzero]
    exact integrable_zero (Vec d) ℝ (volume : Measure (Vec d))

/-- At a positive scale, the unnormalized product section is the self-convolution spatial
pairing with the ABK scale power. -/
theorem abkScaleProductSection_eq_selfConvolution_integral_of_pos {d : Nat}
    (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d) {r : ℝ} (hr : 0 < r) :
    abkScaleProductSection ζ ψ φ r =
      r ^ (-((d : ℝ) + 1)) *
        (∫ x : Vec d,
          ψ x *
            (∫ z : Vec d,
              φ z * abkScaledCutoffSelfConvolution ζ r (x - z)
              ∂(volume : Measure (Vec d)))
          ∂(volume : Measure (Vec d))) := by
  unfold abkScaleProductSection
  have hinner :
      (∫ y : Vec d,
          abkLogKernelProd 1 ζ ψ (r, y) *
            abkLogKernelProd 1 ζ φ (r, y)
          ∂(volume : Measure (Vec d))) =
        r ^ (-((d : ℝ) + 1)) *
          (∫ y : Vec d,
            abkSpatialConvolution ζ ψ r y *
              abkSpatialConvolution ζ φ r y
            ∂(volume : Measure (Vec d))) := by
    calc
      (∫ y : Vec d,
          abkLogKernelProd 1 ζ ψ (r, y) *
            abkLogKernelProd 1 ζ φ (r, y)
          ∂(volume : Measure (Vec d)))
          = ∫ y : Vec d,
              r ^ (-((d : ℝ) + 1)) *
                (abkSpatialConvolution ζ ψ r y *
                  abkSpatialConvolution ζ φ r y)
              ∂(volume : Measure (Vec d)) := by
            refine integral_congr_ae ?_
            filter_upwards with y
            rw [abkLogKernelProd_mul, ite_eq_left hr]
            ring_nf
      _ = r ^ (-((d : ℝ) + 1)) *
            (∫ y : Vec d,
              abkSpatialConvolution ζ ψ r y *
                abkSpatialConvolution ζ φ r y
              ∂(volume : Measure (Vec d))) := by
            rw [integral_const_mul]
  rw [hinner]
  rw [integral_abkSpatialConvolution_mul_abkSpatialConvolution_eq_selfConvolution_integral
    ζ ψ φ hr]

/-- The unnormalized product section vanishes at nonpositive scale. -/
theorem abkScaleProductSection_eq_zero_of_not_pos {d : Nat}
    (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d) {r : ℝ} (hr : ¬ 0 < r) :
    abkScaleProductSection ζ ψ φ r = 0 := by
  unfold abkScaleProductSection
  refine integral_eq_zero_of_ae ?_
  filter_upwards with y
  simp [abkLogKernelProd, hr]

/-- The scaled cutoff self-convolution is nonnegative. -/
theorem abkScaledCutoffSelfConvolution_nonneg {d : Nat}
    (ζ : ABKCutoff d) (r : ℝ) (x : Vec d) :
    0 ≤ abkScaledCutoffSelfConvolution ζ r x := by
  unfold abkScaledCutoffSelfConvolution
  exact integral_nonneg fun y =>
    mul_nonneg (ζ.nonneg _) (ζ.nonneg _)

/-- If the separation is larger than twice the positive scale, the scaled self-convolution
vanishes. -/
theorem abkScaledCutoffSelfConvolution_eq_zero_of_two_mul_lt_norm {d : Nat}
    (ζ : ABKCutoff d) {r : ℝ} (hr : 0 < r) {x : Vec d}
    (hx : 2 * r < euclideanNorm x) :
    abkScaledCutoffSelfConvolution ζ r x = 0 := by
  rw [abkScaledCutoffSelfConvolution_eq_pow_mul ζ hr x]
  rw [abkCutoffSelfConvolution_eq_zero_of_two_lt_norm ζ]
  · simp
  · have hnorm : euclideanNorm (r⁻¹ • x) = r⁻¹ * euclideanNorm x := by
      rw [euclideanNorm_smul, abs_of_pos (inv_pos.mpr hr)]
    rw [hnorm]
    rw [lt_inv_mul_iff₀ hr]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hx

/-- The scaled self-convolution is bounded by the volume of the scaled cutoff support. -/
theorem abkScaledCutoffSelfConvolution_le_volume_closedBall {d : Nat}
    (ζ : ABKCutoff d) {r : ℝ} (hr : 0 < r) (x : Vec d) :
    abkScaledCutoffSelfConvolution ζ r x ≤
      ((volume : Measure (Vec d)) {y : Vec d | euclideanNorm y ≤ r}).toReal := by
  let S : Set (Vec d) := {y : Vec d | euclideanNorm y ≤ r}
  have hS_meas : MeasurableSet S := measurableSet_euclideanClosedBall r
  have hS_finite : (volume : Measure (Vec d)) S ≠ ∞ := by
    have hvol_le : (volume : Measure (Vec d)) S ≤ ENNReal.ofReal ((2 * r) ^ d) :=
      volume_euclideanClosedBall_le (d := d) hr.le
    exact (hvol_le.trans_lt ENNReal.ofReal_lt_top).ne
  have hkernel_int :
      Integrable
        (fun y : Vec d =>
          abkScaledCutoff ζ r y * abkScaledCutoff ζ r (x - y))
        (volume : Measure (Vec d)) := by
    have hcont :
        Continuous
          (fun y : Vec d =>
            abkScaledCutoff ζ r y * abkScaledCutoff ζ r (x - y)) :=
      (continuous_abkScaledCutoff ζ r).mul
        ((continuous_abkScaledCutoff ζ r).comp (continuous_const.sub continuous_id))
    have hcs :
        HasCompactSupport
          (fun y : Vec d =>
            abkScaledCutoff ζ r y * abkScaledCutoff ζ r (x - y)) :=
      (hasCompactSupport_abkScaledCutoff ζ hr.ne').mul_right
    exact hcont.integrable_of_hasCompactSupport hcs
  have hind_int :
      Integrable (S.indicator fun _ : Vec d => (1 : ℝ))
        (volume : Measure (Vec d)) :=
    (integrableOn_const (C := (1 : ℝ)) (μ := volume) hS_finite).integrable_indicator
      hS_meas
  have hpoint :
      (fun y : Vec d =>
        abkScaledCutoff ζ r y * abkScaledCutoff ζ r (x - y)) ≤ᶠ[ae (volume : Measure (Vec d))]
        S.indicator (fun _ : Vec d => (1 : ℝ)) := by
    filter_upwards with y
    by_cases hyS : y ∈ S
    · have hleft_le : abkScaledCutoff ζ r y ≤ 1 := ζ.le_one _
      have hright_le : abkScaledCutoff ζ r (x - y) ≤ 1 := ζ.le_one _
      have hleft_nonneg : 0 ≤ abkScaledCutoff ζ r y := ζ.nonneg _
      have hright_nonneg : 0 ≤ abkScaledCutoff ζ r (x - y) := ζ.nonneg _
      rw [Set.indicator_of_mem hyS]
      calc
        abkScaledCutoff ζ r y * abkScaledCutoff ζ r (x - y)
            ≤ 1 * 1 := mul_le_mul hleft_le hright_le hright_nonneg zero_le_one
        _ = 1 := by norm_num
    · have hleft_zero : abkScaledCutoff ζ r y = 0 := by
        by_contra hne
        exact hyS (euclideanNorm_le_of_abkScaledCutoff_ne_zero ζ hr hne)
      rw [Set.indicator_of_notMem hyS, hleft_zero, zero_mul]
  calc
    abkScaledCutoffSelfConvolution ζ r x
        = ∫ y : Vec d,
            abkScaledCutoff ζ r y * abkScaledCutoff ζ r (x - y)
            ∂(volume : Measure (Vec d)) := rfl
    _ ≤ ∫ y : Vec d, S.indicator (fun _ : Vec d => (1 : ℝ)) y
          ∂(volume : Measure (Vec d)) :=
        integral_mono_ae hkernel_int hind_int hpoint
    _ = ((volume : Measure (Vec d)) S).toReal := by
        rw [integral_indicator_const, MeasureTheory.measureReal_def, smul_eq_mul]
        · ring
        · exact hS_meas

/-- A concrete polynomial upper bound for the scaled self-convolution. -/
theorem abkScaledCutoffSelfConvolution_le_pow {d : Nat}
    (ζ : ABKCutoff d) {r : ℝ} (hr : 0 < r) (x : Vec d) :
    abkScaledCutoffSelfConvolution ζ r x ≤ (2 * r) ^ d := by
  have hvol :=
    abkScaledCutoffSelfConvolution_le_volume_closedBall ζ hr x
  have hmeasure :
      ((volume : Measure (Vec d)) {y : Vec d | euclideanNorm y ≤ r}).toReal ≤
        (2 * r) ^ d := by
    have hvol_le :
        (volume : Measure (Vec d)) {y : Vec d | euclideanNorm y ≤ r} ≤
          ENNReal.ofReal ((2 * r) ^ d) :=
      volume_euclideanClosedBall_le (d := d) hr.le
    have htop : ENNReal.ofReal ((2 * r) ^ d) ≠ ∞ := ENNReal.ofReal_ne_top
    have hnonneg : 0 ≤ (2 * r) ^ d := by positivity
    simpa [ENNReal.toReal_ofReal hnonneg] using
      ENNReal.toReal_mono htop hvol_le
  exact hvol.trans hmeasure

/-- The tail `r^{-1-α}` is integrable on `[c,∞)` for `α,c>0`. -/
theorem integrable_indicator_Ici_rpow_neg_one_sub {α c : ℝ}
    (hα : 0 < α) (hc : 0 < c) :
    Integrable
      ((Set.Ici c).indicator (fun r : ℝ => r ^ (-(1 + α))))
      (volume : Measure ℝ) := by
  have htail :
      IntegrableOn (fun r : ℝ => r ^ (-(1 + α))) (Set.Ioi c)
        (volume : Measure ℝ) :=
    integrableOn_Ioi_rpow_of_lt (by linarith : -(1 + α) < -1) hc
  exact (htail.congr_set_ae Ioi_ae_eq_Ici.symm).integrable_indicator measurableSet_Ici

/-- Integral of the tail `r^{-1-α}` on `[c,∞)`. -/
theorem integral_indicator_Ici_rpow_neg_one_sub {α c : ℝ}
    (hα : 0 < α) (hc : 0 < c) :
    (∫ r : ℝ,
        (Set.Ici c).indicator (fun r : ℝ => r ^ (-(1 + α))) r
        ∂(volume : Measure ℝ)) =
      c ^ (-α) / α := by
  have htail :
      IntegrableOn (fun r : ℝ => r ^ (-(1 + α))) (Set.Ici c)
    (volume : Measure ℝ) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -(1 + α) < -1) hc).congr_set_ae
      Ioi_ae_eq_Ici.symm
  rw [integral_indicator measurableSet_Ici]
  rw [integral_Ici_eq_integral_Ioi]
  rw [integral_Ioi_rpow_of_lt (by linarith : -(1 + α) < -1) hc]
  field_simp [hα.ne']
  ring_nf

end GaussianFields

end

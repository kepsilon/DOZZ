/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import GaussianFields.LogCorrelated.ABK.ScaleSpace

/-!
# GaussianFields ABK test functions and convolution

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped Convolution ENNReal InnerProductSpace NNReal ProbabilityTheory Topology

namespace GaussianFields

/-! ## ABK kernels -/

/-- The scaled cutoff `ζ_r(x) = ζ(x / r)`, written using scalar multiplication. -/
@[expose]
noncomputable def abkScaledCutoff {d : Nat} (ζ : ABKCutoff d) (r : ℝ)
    (x : Vec d) : ℝ :=
  ζ (r⁻¹ • x)

/-- The scaled ABK cutoff is continuous. -/
theorem continuous_abkScaledCutoff {d : Nat} (ζ : ABKCutoff d) (r : ℝ) :
    Continuous (abkScaledCutoff ζ r) := by
  unfold abkScaledCutoff
  exact ζ.continuous.comp (continuous_const_smul (r⁻¹))

/-- At nonzero scale, the scaled ABK cutoff has compact support. -/
theorem hasCompactSupport_abkScaledCutoff {d : Nat} (ζ : ABKCutoff d) {r : ℝ}
    (hr : r ≠ 0) :
    HasCompactSupport (abkScaledCutoff ζ r) := by
  change HasCompactSupport (fun x : Vec d => ζ (r⁻¹ • x))
  exact ζ.hasCompactSupport.comp_smul (c := r⁻¹) (inv_ne_zero hr)

/-- Compact support of `ψ` gives integrability of the first radial moment `|x| |ψ x|`. -/
theorem integrable_euclideanNorm_mul_abs_meanZeroTestFunction {d : Nat}
    (ψ : MeanZeroTestFunction d) :
    Integrable (fun x : Vec d => euclideanNorm x * |ψ x|)
      (volume : Measure (Vec d)) := by
  have hcont : Continuous (fun x : Vec d => euclideanNorm x * |ψ x|) :=
    (continuous_euclideanNorm (d := d)).mul ψ.continuous.abs
  have hcomp : HasCompactSupport (fun x : Vec d => euclideanNorm x * |ψ x|) :=
    ψ.hasCompactSupport.abs.mul_left
  exact hcont.integrable_of_hasCompactSupport hcomp

/-- A compactly supported mean-zero test function is supported in some local Euclidean ball. -/
theorem exists_support_subset_euclideanClosedBall_meanZeroTestFunction {d : Nat}
    (ψ : MeanZeroTestFunction d) :
    ∃ R, 0 ≤ R ∧ Function.support ψ ⊆ {x : Vec d | euclideanNorm x ≤ R} := by
  rcases ψ.hasCompactSupport.exists_pos_le_norm with ⟨R, hR_pos, hvanish⟩
  refine ⟨(d : ℝ) * R, mul_nonneg (Nat.cast_nonneg d) hR_pos.le, ?_⟩
  intro x hx
  have hnorm_le : ‖x‖ ≤ R := by
    by_contra hnot
    exact hx (hvanish x (le_of_not_ge hnot))
  calc
    euclideanNorm x ≤ (d : ℝ) * ‖x‖ := euclideanNorm_le_card_mul_norm x
    _ ≤ (d : ℝ) * R := mul_le_mul_of_nonneg_left hnorm_le (Nat.cast_nonneg d)

/-- Compactly supported continuous test functions are uniformly bounded. -/
theorem exists_abs_meanZeroTestFunction_le {d : Nat} (ψ : MeanZeroTestFunction d) :
    ∃ M, 0 ≤ M ∧ ∀ x : Vec d, |ψ x| ≤ M := by
  rcases ψ.continuous.bounded_above_of_compact_support ψ.hasCompactSupport with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right C 0, ?_⟩
  intro x
  calc
    |ψ x| = ‖ψ x‖ := by rw [Real.norm_eq_abs]
    _ ≤ C := hC x
    _ ≤ max C 0 := le_max_left C 0

/-- Scaling the ABK cutoff divides its Lipschitz constant by `|r|`. -/
theorem abkScaledCutoff_lipschitz_bound {d : Nat} (ζ : ABKCutoff d) :
    ∃ L, 0 ≤ L ∧
      ∀ r x y,
        |abkScaledCutoff ζ r x - abkScaledCutoff ζ r y| ≤
          L * |r|⁻¹ * euclideanNorm (x - y) := by
  rcases ζ.lipschitz with ⟨L, hL_nonneg, hL⟩
  refine ⟨L, hL_nonneg, ?_⟩
  intro r x y
  have hsub : r⁻¹ • x - r⁻¹ • y = r⁻¹ • (x - y) := by
    ext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  calc
    |abkScaledCutoff ζ r x - abkScaledCutoff ζ r y|
        = |ζ (r⁻¹ • x) - ζ (r⁻¹ • y)| := rfl
    _ ≤ L * euclideanNorm (r⁻¹ • x - r⁻¹ • y) := hL _ _
    _ = L * |r|⁻¹ * euclideanNorm (x - y) := by
      rw [hsub, euclideanNorm_smul, abs_inv]
      ring

/-- If the scaled cutoff is nonzero at positive scale `r`, then the original point lies in the
Euclidean ball of radius `r`. -/
theorem euclideanNorm_le_of_abkScaledCutoff_ne_zero {d : Nat} (ζ : ABKCutoff d)
    {r : ℝ} (hr : 0 < r) {x : Vec d} (hx : abkScaledCutoff ζ r x ≠ 0) :
    euclideanNorm x ≤ r := by
  have hsupp : r⁻¹ • x ∈ Function.support ζ := hx
  have hunit : euclideanNorm (r⁻¹ • x) ≤ 1 := ζ.support_subset_unitBall hsupp
  have hscaled : euclideanNorm (r⁻¹ • x) = r⁻¹ * euclideanNorm x := by
    rw [euclideanNorm_smul, abs_of_pos (inv_pos.mpr hr)]
  have hunit' : r⁻¹ * euclideanNorm x ≤ 1 := by
    simpa [hscaled] using hunit
  calc
    euclideanNorm x = r * (r⁻¹ * euclideanNorm x) := by
      field_simp [hr.ne']
    _ ≤ r * 1 := mul_le_mul_of_nonneg_left hunit' hr.le
    _ = r := by ring

/-- The ABK spatial convolution `(ζ_r * ψ)(y)`. -/
@[expose]
noncomputable def abkSpatialConvolution {d : Nat} (ζ : ABKCutoff d)
    (ψ : MeanZeroTestFunction d) (r : ℝ) (y : Vec d) : ℝ :=
  ∫ x : Vec d, abkScaledCutoff ζ r (y - x) * ψ x

/-- The ABK convolution integrand is jointly strongly measurable in scale, space, and the
integration variable. -/
theorem stronglyMeasurable_abkSpatialConvolution_integrand_prod {d : Nat}
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) :
    StronglyMeasurable
      (fun q : (ℝ × Vec d) × Vec d =>
        abkScaledCutoff ζ q.1.1 (q.1.2 - q.2) * ψ q.2) := by
  unfold abkScaledCutoff
  exact (ζ.continuous.measurable.comp (by fun_prop)).stronglyMeasurable.mul
    (ψ.continuous.measurable.comp (by fun_prop)).stronglyMeasurable

/-- The ABK spatial convolution is jointly strongly measurable in scale and space. -/
theorem stronglyMeasurable_abkSpatialConvolution_prod {d : Nat}
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) :
    StronglyMeasurable
      (fun p : ℝ × Vec d => abkSpatialConvolution ζ ψ p.1 p.2) := by
  simpa [abkSpatialConvolution] using
    (stronglyMeasurable_abkSpatialConvolution_integrand_prod ζ ψ).integral_prod_right'

/-- The hand-written ABK spatial convolution is Mathlib convolution with the same kernel. -/
theorem abkSpatialConvolution_eq_convolution {d : Nat} (ζ : ABKCutoff d)
    (ψ : MeanZeroTestFunction d) (r : ℝ) (y : Vec d) :
    abkSpatialConvolution ζ ψ r y =
      ((ψ : Vec d → ℝ) ⋆[ContinuousLinearMap.mul ℝ ℝ, (volume : Measure (Vec d))]
        abkScaledCutoff ζ r) y := by
  rw [abkSpatialConvolution, convolution_def]
  refine integral_congr_ae ?_
  filter_upwards with x
  simp [ContinuousLinearMap.mul_apply', mul_comm]

/-- At nonzero scale, the ABK spatial convolution is continuous in the spatial variable. -/
theorem continuous_abkSpatialConvolution {d : Nat} (ζ : ABKCutoff d)
    (ψ : MeanZeroTestFunction d) {r : ℝ} (hr : r ≠ 0) :
    Continuous (fun y : Vec d => abkSpatialConvolution ζ ψ r y) := by
  have hconv :
      Continuous
        (((ψ : Vec d → ℝ) ⋆[ContinuousLinearMap.mul ℝ ℝ, (volume : Measure (Vec d))]
          abkScaledCutoff ζ r)) :=
    (hasCompactSupport_abkScaledCutoff ζ hr).continuous_convolution_right
      (ContinuousLinearMap.mul ℝ ℝ) ψ.integrable.locallyIntegrable
      (continuous_abkScaledCutoff ζ r)
  refine hconv.congr ?_
  intro y
  exact (abkSpatialConvolution_eq_convolution ζ ψ r y).symm

/-- The integrand defining `(ζ_r * ψ)(y)` is integrable. -/
theorem integrable_abkSpatialConvolution_integrand {d : Nat} (ζ : ABKCutoff d)
    (ψ : MeanZeroTestFunction d) (r : ℝ) (y : Vec d) :
    Integrable (fun x : Vec d => abkScaledCutoff ζ r (y - x) * ψ x)
      (volume : Measure (Vec d)) := by
  refine Integrable.mono' ψ.integrable.norm ?_ ?_
  · have hcont :
        Continuous (fun x : Vec d => abkScaledCutoff ζ r (y - x) * ψ x) := by
      unfold abkScaledCutoff
      have hinner : Continuous fun x : Vec d => r⁻¹ • (y - x) := by
        fun_prop
      exact (ζ.continuous.comp hinner).mul ψ.continuous
    exact hcont.aestronglyMeasurable
  · filter_upwards with x
    have hz_nonneg : 0 ≤ ζ (r⁻¹ • (y - x)) := ζ.nonneg _
    have hz_le_one : ζ (r⁻¹ • (y - x)) ≤ 1 := ζ.le_one _
    calc
      ‖abkScaledCutoff ζ r (y - x) * ψ x‖
          = |ζ (r⁻¹ • (y - x)) * ψ x| := by
            rfl
      _ = |ζ (r⁻¹ • (y - x))| * |ψ x| := abs_mul _ _
      _ = ζ (r⁻¹ • (y - x)) * |ψ x| := by
            rw [abs_of_nonneg hz_nonneg]
      _ ≤ 1 * |ψ x| := by
            exact mul_le_mul_of_nonneg_right hz_le_one (abs_nonneg (ψ x))
      _ = |ψ x| := by ring
      _ = ‖ψ x‖ := by rw [Real.norm_eq_abs]

/-- Mean-zero cancellation form of the ABK convolution.  This is the identity used for the
large-scale estimate. -/
theorem abkSpatialConvolution_eq_integral_sub_scaledCutoff {d : Nat} (ζ : ABKCutoff d)
    (ψ : MeanZeroTestFunction d) (r : ℝ) (y : Vec d) :
    abkSpatialConvolution ζ ψ r y =
      ∫ x : Vec d,
        (abkScaledCutoff ζ r (y - x) - abkScaledCutoff ζ r y) * ψ x := by
  let A : Vec d → ℝ := fun x => abkScaledCutoff ζ r (y - x) * ψ x
  let B : Vec d → ℝ := fun x => abkScaledCutoff ζ r y * ψ x
  have hA : Integrable A (volume : Measure (Vec d)) :=
    integrable_abkSpatialConvolution_integrand ζ ψ r y
  have hB : Integrable B (volume : Measure (Vec d)) :=
    ψ.integrable.const_mul (abkScaledCutoff ζ r y)
  have hrewrite :
      (fun x : Vec d =>
        (abkScaledCutoff ζ r (y - x) - abkScaledCutoff ζ r y) * ψ x) =
        fun x => A x - B x := by
    funext x
    simp [A, B]
    ring
  calc
    abkSpatialConvolution ζ ψ r y = ∫ x : Vec d, A x := rfl
    _ = ∫ x : Vec d, A x - B x := by
          rw [integral_sub hA hB, integral_const_mul, ψ.integral_eq_zero, mul_zero, sub_zero]
    _ = ∫ x : Vec d,
        (abkScaledCutoff ζ r (y - x) - abkScaledCutoff ζ r y) * ψ x := by
          rw [hrewrite]

/-- The cancellation-form integrand is integrable. -/
theorem integrable_abkSpatialConvolution_cancellation_integrand {d : Nat}
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) (r : ℝ) (y : Vec d) :
    Integrable
      (fun x : Vec d =>
        (abkScaledCutoff ζ r (y - x) - abkScaledCutoff ζ r y) * ψ x)
      (volume : Measure (Vec d)) := by
  let A : Vec d → ℝ := fun x => abkScaledCutoff ζ r (y - x) * ψ x
  let B : Vec d → ℝ := fun x => abkScaledCutoff ζ r y * ψ x
  have hA : Integrable A (volume : Measure (Vec d)) :=
    integrable_abkSpatialConvolution_integrand ζ ψ r y
  have hB : Integrable B (volume : Measure (Vec d)) :=
    ψ.integrable.const_mul (abkScaledCutoff ζ r y)
  have hrewrite :
      (fun x : Vec d =>
        (abkScaledCutoff ζ r (y - x) - abkScaledCutoff ζ r y) * ψ x) =
        fun x => A x - B x := by
    funext x
    simp [A, B]
    ring
  rw [hrewrite]
  exact hA.sub hB

/-- Mean-zero cancellation and Lipschitz regularity give a uniform large-scale pointwise bound. -/
theorem abs_abkSpatialConvolution_le_scaled_moment {d : Nat}
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) :
    ∃ L, 0 ≤ L ∧ ∀ r y,
      |abkSpatialConvolution ζ ψ r y| ≤
        L * |r|⁻¹ *
          ∫ x : Vec d, euclideanNorm x * |ψ x| := by
  rcases abkScaledCutoff_lipschitz_bound ζ with ⟨L, hL_nonneg, hL⟩
  refine ⟨L, hL_nonneg, ?_⟩
  intro r y
  let F : Vec d → ℝ :=
    fun x => (abkScaledCutoff ζ r (y - x) - abkScaledCutoff ζ r y) * ψ x
  have hF_int : Integrable F (volume : Measure (Vec d)) :=
    integrable_abkSpatialConvolution_cancellation_integrand ζ ψ r y
  have hmoment_int :
      Integrable (fun x : Vec d => euclideanNorm x * |ψ x|)
        (volume : Measure (Vec d)) :=
    integrable_euclideanNorm_mul_abs_meanZeroTestFunction ψ
  have hconst_nonneg : 0 ≤ L * |r|⁻¹ :=
    mul_nonneg hL_nonneg (inv_nonneg.mpr (abs_nonneg r))
  have hpoint :
      ∀ x : Vec d,
        ‖F x‖ ≤ L * |r|⁻¹ * (euclideanNorm x * |ψ x|) := by
    intro x
    have hdiff : (y - x) - y = -x := by
      ext i
      simp only [Pi.sub_apply, Pi.neg_apply]
      ring
    have hnorm : euclideanNorm ((y - x) - y) = euclideanNorm x := by
      rw [hdiff, euclideanNorm_neg]
    have hζ := hL r (y - x) y
    calc
      ‖F x‖
          = |(abkScaledCutoff ζ r (y - x) - abkScaledCutoff ζ r y) * ψ x| := by
            rfl
      _ = |abkScaledCutoff ζ r (y - x) - abkScaledCutoff ζ r y| * |ψ x| := by
            rw [abs_mul]
      _ ≤ (L * |r|⁻¹ * euclideanNorm ((y - x) - y)) * |ψ x| := by
            exact mul_le_mul_of_nonneg_right hζ (abs_nonneg (ψ x))
      _ = L * |r|⁻¹ * (euclideanNorm x * |ψ x|) := by
            rw [hnorm]
            ring
  have hintegral_bound :
      ∫ x : Vec d, ‖F x‖ ∂(volume : Measure (Vec d)) ≤
        ∫ x : Vec d, L * |r|⁻¹ * (euclideanNorm x * |ψ x|)
          ∂(volume : Measure (Vec d)) := by
    exact integral_mono hF_int.norm (hmoment_int.const_mul (L * |r|⁻¹)) hpoint
  calc
    |abkSpatialConvolution ζ ψ r y|
        = ‖abkSpatialConvolution ζ ψ r y‖ := by rw [Real.norm_eq_abs]
    _ = ‖∫ x : Vec d, F x ∂(volume : Measure (Vec d))‖ := by
          rw [abkSpatialConvolution_eq_integral_sub_scaledCutoff ζ ψ r y]
    _ ≤ ∫ x : Vec d, ‖F x‖ ∂(volume : Measure (Vec d)) :=
          norm_integral_le_integral_norm F
    _ ≤ ∫ x : Vec d, L * |r|⁻¹ * (euclideanNorm x * |ψ x|)
          ∂(volume : Measure (Vec d)) := hintegral_bound
    _ = L * |r|⁻¹ *
          ∫ x : Vec d, euclideanNorm x * |ψ x| := by
          rw [integral_const_mul]

/-- If `ψ` is supported in a Euclidean ball of radius `R`, then at positive scale the ABK
convolution vanishes outside a controlled ball.  The harmless factor `d` comes from comparing the
local Euclidean norm with Mathlib's product sup norm. -/
theorem abkSpatialConvolution_eq_zero_of_euclideanNorm_gt {d : Nat}
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) {R r : ℝ}
    (hψ_support : Function.support ψ ⊆ {x : Vec d | euclideanNorm x ≤ R})
    (hr : 0 < r) {y : Vec d}
    (hy : (d : ℝ) * (R + r) < euclideanNorm y) :
    abkSpatialConvolution ζ ψ r y = 0 := by
  unfold abkSpatialConvolution
  refine integral_eq_zero_of_ae ?_
  filter_upwards with x
  by_cases hψx : ψ x = 0
  · simp [hψx]
  · have hcut_zero : abkScaledCutoff ζ r (y - x) = 0 := by
      by_contra hcut
      have hx_support : x ∈ Function.support ψ := hψx
      have hx_norm : euclideanNorm x ≤ R := hψ_support hx_support
      have hcut_norm : euclideanNorm (y - x) ≤ r :=
        euclideanNorm_le_of_abkScaledCutoff_ne_zero ζ hr hcut
      have hy_decomp : x + (y - x) = y := by
        ext i
        simp only [Pi.add_apply, Pi.sub_apply]
        ring
      have hy_le : euclideanNorm y ≤ (d : ℝ) * (R + r) := by
        calc
          euclideanNorm y = euclideanNorm (x + (y - x)) := by rw [hy_decomp]
          _ ≤ (d : ℝ) * ‖x + (y - x)‖ :=
                euclideanNorm_le_card_mul_norm (x + (y - x))
          _ ≤ (d : ℝ) * (‖x‖ + ‖y - x‖) := by
                exact mul_le_mul_of_nonneg_left (norm_add_le x (y - x))
                  (Nat.cast_nonneg d)
          _ ≤ (d : ℝ) * (R + r) := by
                refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg d)
                exact add_le_add ((norm_le_euclideanNorm x).trans hx_norm)
                  ((norm_le_euclideanNorm (y - x)).trans hcut_norm)
      exact (not_lt_of_ge hy_le) hy
    simp [hcut_zero]

/-- Support form of `abkSpatialConvolution_eq_zero_of_euclideanNorm_gt`. -/
theorem support_abkSpatialConvolution_subset_euclideanClosedBall {d : Nat}
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) {R r : ℝ}
    (hψ_support : Function.support ψ ⊆ {x : Vec d | euclideanNorm x ≤ R})
    (hr : 0 < r) :
    Function.support (fun y : Vec d => abkSpatialConvolution ζ ψ r y) ⊆
      {y : Vec d | euclideanNorm y ≤ (d : ℝ) * (R + r)} := by
  intro y hy
  by_contra hnot
  exact hy (abkSpatialConvolution_eq_zero_of_euclideanNorm_gt ζ ψ hψ_support hr
    (lt_of_not_ge hnot))

/-- The local Euclidean ball is contained in the product closed ball, giving a concrete volume
upper bound. -/
theorem volume_euclideanClosedBall_le {d : Nat} {A : ℝ} (hA_nonneg : 0 ≤ A) :
    volume {y : Vec d | euclideanNorm y ≤ A} ≤
      ENNReal.ofReal ((2 * A) ^ d) := by
  have hsubset :
      {y : Vec d | euclideanNorm y ≤ A} ⊆ Metric.closedBall (0 : Vec d) A := by
    intro y hy
    have hynorm : ‖y‖ ≤ A := (norm_le_euclideanNorm y).trans hy
    simpa [Metric.mem_closedBall, dist_eq_norm] using hynorm
  calc
    volume {y : Vec d | euclideanNorm y ≤ A}
        ≤ volume (Metric.closedBall (0 : Vec d) A) := measure_mono hsubset
    _ = ENNReal.ofReal ((2 * A) ^ d) := by
          rw [Real.volume_pi_closedBall (0 : Vec d) hA_nonneg, Fintype.card_fin]

/-- Local Euclidean closed balls are measurable. -/
theorem measurableSet_euclideanClosedBall {d : Nat} (A : ℝ) :
    MeasurableSet {y : Vec d | euclideanNorm y ≤ A} :=
  (isClosed_le continuous_euclideanNorm continuous_const).measurableSet

/-- Local Euclidean closed balls are compact. -/
theorem isCompact_euclideanClosedBall {d : Nat} (A : ℝ) :
    IsCompact {y : Vec d | euclideanNorm y ≤ A} := by
  have hclosed : IsClosed {y : Vec d | euclideanNorm y ≤ A} :=
    isClosed_le continuous_euclideanNorm continuous_const
  have hsubset :
      {y : Vec d | euclideanNorm y ≤ A} ⊆ Metric.closedBall (0 : Vec d) A := by
    intro y hy
    have hynorm : ‖y‖ ≤ A := (norm_le_euclideanNorm y).trans hy
    simpa [Metric.mem_closedBall, dist_eq_norm] using hynorm
  exact (isCompact_closedBall (0 : Vec d) A).of_isClosed_subset hclosed hsubset

/-- At positive scale, the ABK spatial convolution has compact support. -/
theorem hasCompactSupport_abkSpatialConvolution {d : Nat}
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (fun y : Vec d => abkSpatialConvolution ζ ψ r y) := by
  rcases exists_support_subset_euclideanClosedBall_meanZeroTestFunction ψ with
    ⟨R, _hR_nonneg, hψ_support⟩
  let A : ℝ := (d : ℝ) * (R + r)
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_euclideanClosedBall (d := d) A) ?_
  simpa [A] using
    support_abkSpatialConvolution_subset_euclideanClosedBall ζ ψ hψ_support hr

/-- At positive scale, the square of the ABK spatial convolution is integrable. -/
theorem integrable_sq_abkSpatialConvolution {d : Nat}
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) {r : ℝ} (hr : 0 < r) :
    Integrable (fun y : Vec d => (abkSpatialConvolution ζ ψ r y) ^ (2 : Nat))
      (volume : Measure (Vec d)) := by
  have hcont : Continuous (fun y : Vec d => abkSpatialConvolution ζ ψ r y) :=
    continuous_abkSpatialConvolution ζ ψ hr.ne'
  have hcont_sq :
      Continuous (fun y : Vec d => (abkSpatialConvolution ζ ψ r y) ^ (2 : Nat)) :=
    hcont.pow 2
  have hcs : HasCompactSupport (fun y : Vec d => abkSpatialConvolution ζ ψ r y) :=
    hasCompactSupport_abkSpatialConvolution ζ ψ hr
  have hcs_sq :
      HasCompactSupport
        (fun y : Vec d =>
          abkSpatialConvolution ζ ψ r y * abkSpatialConvolution ζ ψ r y) :=
    hcs.mul_left
  exact hcont_sq.integrable_of_hasCompactSupport (by
    simpa [pow_two] using hcs_sq)

end GaussianFields

end

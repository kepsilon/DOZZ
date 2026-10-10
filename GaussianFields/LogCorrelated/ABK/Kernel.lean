/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import GaussianFields.LogCorrelated.ABK.ConvolutionBounds

/-!
# GaussianFields ABK scale kernel

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped Convolution ENNReal InnerProductSpace NNReal ProbabilityTheory Topology

namespace GaussianFields

/-- The ABK deterministic product-coordinate kernel before composing with the scale-space split. -/
@[expose]
noncomputable def abkLogKernelProd {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) : ℝ × Vec d → ℝ :=
  fun p =>
    if 0 < p.1 then
      normalization *
        p.1 ^ (-(((d : ℝ) + 1) / 2)) *
          abkSpatialConvolution ζ ψ p.1 p.2
    else
      0

/-- Every spatial section of the squared ABK product kernel is integrable. -/
theorem integrable_sq_abkLogKernelProd_section {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) (r : ℝ) :
    Integrable
      (fun y : Vec d => (abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat))
      (volume : Measure (Vec d)) := by
  by_cases hr : 0 < r
  · let a : ℝ := normalization * r ^ (-(((d : ℝ) + 1) / 2))
    have hspatial : Integrable
        (fun y : Vec d => (abkSpatialConvolution ζ ψ r y) ^ (2 : Nat))
        (volume : Measure (Vec d)) :=
      integrable_sq_abkSpatialConvolution ζ ψ hr
    have hsection :
        (fun y : Vec d =>
          (abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)) =
          fun y : Vec d =>
            a ^ (2 : Nat) * (abkSpatialConvolution ζ ψ r y) ^ (2 : Nat) := by
      funext y
      simp [abkLogKernelProd, hr, a, mul_pow]
    rw [hsection]
    exact hspatial.const_mul (a ^ (2 : Nat))
  · have hsection :
        (fun y : Vec d =>
          (abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)) =
          fun _ : Vec d => 0 := by
      funext y
      simp [abkLogKernelProd, hr]
    rw [hsection]
    exact integrable_zero (Vec d) ℝ (volume : Measure (Vec d))

/-- The ABK product-coordinate kernel is a.e.-strongly measurable for any ambient measure. -/
theorem aestronglyMeasurable_abkLogKernelProd {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) (μ : Measure (ℝ × Vec d)) :
    AEStronglyMeasurable (abkLogKernelProd normalization ζ ψ) μ := by
  let S : Set (ℝ × Vec d) := {p | 0 < p.1}
  have hS : MeasurableSet S := measurableSet_lt measurable_const measurable_fst
  let a : ℝ := -(((d : ℝ) + 1) / 2)
  let F : ℝ × Vec d → ℝ := fun p =>
    normalization * p.1 ^ a * abkSpatialConvolution ζ ψ p.1 p.2
  have hconv :
      StronglyMeasurable
        (fun p : ℝ × Vec d => abkSpatialConvolution ζ ψ p.1 p.2) :=
    stronglyMeasurable_abkSpatialConvolution_prod ζ ψ
  have hpow :
      AEStronglyMeasurable (fun p : ℝ × Vec d => p.1 ^ a) (μ.restrict S) := by
    refine ContinuousOn.aestronglyMeasurable ?_ hS
    exact continuous_fst.continuousOn.rpow_const fun p hp => Or.inl (ne_of_gt hp)
  have hF : AEStronglyMeasurable F (μ.restrict S) := by
    exact (aestronglyMeasurable_const.mul hpow).mul hconv.aestronglyMeasurable.restrict
  have hzero :
      AEStronglyMeasurable (fun _ : ℝ × Vec d => (0 : ℝ)) (μ.restrict Sᶜ) :=
    aestronglyMeasurable_const
  have hpiece :
      AEStronglyMeasurable (S.piecewise F (fun _ : ℝ × Vec d => 0)) μ :=
    AEStronglyMeasurable.piecewise hS hF hzero
  refine hpiece.congr ?_
  filter_upwards with p
  by_cases hp : p ∈ S
  · have hp_pos : 0 < p.1 := by simpa [S] using hp
    simp [Set.piecewise_eq_of_mem, hp, S, F, abkLogKernelProd, hp_pos, a]
  · have hpn : ¬ 0 < p.1 := by simpa [S] using hp
    simp [Set.piecewise_eq_of_notMem, hp, abkLogKernelProd, hpn]

/-- The square of the ABK product-coordinate kernel is a.e.-strongly measurable. -/
theorem aestronglyMeasurable_sq_abkLogKernelProd {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) (μ : Measure (ℝ × Vec d)) :
    AEStronglyMeasurable
      (fun p : ℝ × Vec d => (abkLogKernelProd normalization ζ ψ p) ^ (2 : Nat)) μ := by
  exact (aestronglyMeasurable_abkLogKernelProd normalization ζ ψ μ).pow 2 |>.congr
    (ae_of_all _ fun _ => rfl)

/-- The scale-to-spatial-square-mass map of the ABK product kernel is a.e.-strongly measurable. -/
theorem aestronglyMeasurable_integral_norm_sq_abkLogKernelProd_section {d : Nat}
    (normalization : ℝ) (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) :
    AEStronglyMeasurable
      (fun r : ℝ =>
        ∫ y : Vec d, ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)‖
          ∂(volume : Measure (Vec d)))
      (volume : Measure ℝ) := by
  have hsq :
      AEStronglyMeasurable
        (fun p : ℝ × Vec d => ‖(abkLogKernelProd normalization ζ ψ p) ^ (2 : Nat)‖)
        ((volume : Measure ℝ).prod (volume : Measure (Vec d))) :=
    (aestronglyMeasurable_sq_abkLogKernelProd normalization ζ ψ
      ((volume : Measure ℝ).prod (volume : Measure (Vec d)))).norm
  simpa using hsq.integral_prod_right'

theorem abkLogKernelProd_mul {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ φ : MeanZeroTestFunction d) (p : ℝ × Vec d) :
    abkLogKernelProd normalization ζ ψ p *
        abkLogKernelProd normalization ζ φ p =
      if 0 < p.1 then
        normalization ^ (2 : Nat) * p.1 ^ (-((d : ℝ) + 1)) *
          (abkSpatialConvolution ζ ψ p.1 p.2 *
            abkSpatialConvolution ζ φ p.1 p.2)
      else
        0 := by
  by_cases hr : 0 < p.1
  · have hr_nonneg : 0 ≤ p.1 := hr.le
    have hpref :
        (p.1 ^ (-(((d : ℝ) + 1) / 2))) ^ (2 : Nat) =
          p.1 ^ (-((d : ℝ) + 1)) := by
      let a : ℝ := -(((d : ℝ) + 1) / 2)
      change (p.1 ^ a) ^ (2 : Nat) = p.1 ^ (-((d : ℝ) + 1))
      calc
        (p.1 ^ a) ^ (2 : Nat)
            = p.1 ^ (a * ((2 : Nat) : ℝ)) :=
              (Real.rpow_mul_natCast hr_nonneg a 2).symm
        _ = p.1 ^ (-((d : ℝ) + 1)) := by
              congr 1
              dsimp [a]
              ring
    simp only [abkLogKernelProd, ite_eq_left hr]
    rw [← hpref]
    ring
  · simp [abkLogKernelProd, hr]

/-- At a positive scale, the product-kernel square integral is the spatial convolution square
integral multiplied by the deterministic prefactor squared. -/
theorem integral_norm_sq_abkLogKernelProd_section_eq {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) {r : ℝ} (hr : 0 < r) :
    (∫ y : Vec d, ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)‖
      ∂(volume : Measure (Vec d))) =
      (normalization * r ^ (-(((d : ℝ) + 1) / 2))) ^ (2 : Nat) *
        ∫ y : Vec d, ‖(abkSpatialConvolution ζ ψ r y) ^ (2 : Nat)‖
          ∂(volume : Measure (Vec d)) := by
  let b : ℝ := normalization * r ^ (-(((d : ℝ) + 1) / 2))
  have hfun :
      (fun y : Vec d => ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)‖) =
        fun y : Vec d => b ^ (2 : Nat) *
          ‖(abkSpatialConvolution ζ ψ r y) ^ (2 : Nat)‖ := by
    funext y
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    simp only [abkLogKernelProd, ite_eq_left hr]
    change |(b * abkSpatialConvolution ζ ψ r y) ^ (2 : Nat)| =
      b ^ (2 : Nat) * |(abkSpatialConvolution ζ ψ r y) ^ (2 : Nat)|
    rw [mul_pow, abs_mul, abs_of_nonneg (sq_nonneg b)]
  rw [hfun, integral_const_mul]

/-- Small-scale product-kernel bound, obtained from the compact-support spatial estimate and the
ABK prefactor power count. -/
theorem integral_norm_sq_abkLogKernelProd_le_small {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) :
    ∃ C, 0 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      Integrable (fun y : Vec d => (abkSpatialConvolution ζ ψ r y) ^ (2 : Nat))
        (volume : Measure (Vec d)) →
      (∫ y : Vec d, ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)‖
        ∂(volume : Measure (Vec d))) ≤ C * r ^ ((d : ℝ) - 1) := by
  rcases integral_norm_sq_abkSpatialConvolution_le_small ζ ψ with ⟨Csp, hCsp_nonneg, hsp⟩
  refine ⟨normalization ^ (2 : Nat) * Csp,
    mul_nonneg (sq_nonneg normalization) hCsp_nonneg, ?_⟩
  intro r hr_pos hr_le_one hsection_int
  let a : ℝ := -(((d : ℝ) + 1) / 2)
  have hcoef_nonneg : 0 ≤ (normalization * r ^ a) ^ (2 : Nat) :=
    sq_nonneg (normalization * r ^ a)
  have hspatial := hsp r hr_pos hr_le_one hsection_int
  calc
    (∫ y : Vec d, ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)‖
        ∂(volume : Measure (Vec d)))
        = (normalization * r ^ a) ^ (2 : Nat) *
            ∫ y : Vec d, ‖(abkSpatialConvolution ζ ψ r y) ^ (2 : Nat)‖
              ∂(volume : Measure (Vec d)) := by
          simpa [a] using integral_norm_sq_abkLogKernelProd_section_eq
            (d := d) normalization ζ ψ hr_pos
    _ ≤ (normalization * r ^ a) ^ (2 : Nat) *
          (Csp * r ^ (2 * d)) := by
          exact mul_le_mul_of_nonneg_left hspatial hcoef_nonneg
    _ = (normalization ^ (2 : Nat) * Csp) * r ^ ((d : ℝ) - 1) := by
          calc
            (normalization * r ^ a) ^ (2 : Nat) * (Csp * r ^ (2 * d))
                = (normalization ^ (2 : Nat) * Csp) *
                    ((r ^ a) ^ (2 : Nat) * r ^ (2 * d)) := by
                  ring
            _ = (normalization ^ (2 : Nat) * Csp) * r ^ ((d : ℝ) - 1) := by
                  dsimp [a]
                  rw [abk_smallScale_power_identity (d := d) hr_pos]

/-- Large-scale product-kernel bound, obtained from the mean-zero spatial estimate and the ABK
prefactor power count. -/
theorem integral_norm_sq_abkLogKernelProd_le_large {d : Nat} (normalization : ℝ)
    (ζ : ABKCutoff d) (ψ : MeanZeroTestFunction d) :
    ∃ C, 0 ≤ C ∧ ∀ r : ℝ, 1 ≤ r →
      Integrable (fun y : Vec d => (abkSpatialConvolution ζ ψ r y) ^ (2 : Nat))
        (volume : Measure (Vec d)) →
      (∫ y : Vec d, ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)‖
        ∂(volume : Measure (Vec d))) ≤ C * r ^ (-3 : ℝ) := by
  rcases integral_norm_sq_abkSpatialConvolution_le_large ζ ψ with ⟨Csp, hCsp_nonneg, hsp⟩
  refine ⟨normalization ^ (2 : Nat) * Csp,
    mul_nonneg (sq_nonneg normalization) hCsp_nonneg, ?_⟩
  intro r hr hsection_int
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  let a : ℝ := -(((d : ℝ) + 1) / 2)
  have hcoef_nonneg : 0 ≤ (normalization * r ^ a) ^ (2 : Nat) :=
    sq_nonneg (normalization * r ^ a)
  have hspatial := hsp r hr hsection_int
  calc
    (∫ y : Vec d, ‖(abkLogKernelProd normalization ζ ψ (r, y)) ^ (2 : Nat)‖
        ∂(volume : Measure (Vec d)))
        = (normalization * r ^ a) ^ (2 : Nat) *
            ∫ y : Vec d, ‖(abkSpatialConvolution ζ ψ r y) ^ (2 : Nat)‖
              ∂(volume : Measure (Vec d)) := by
          simpa [a] using integral_norm_sq_abkLogKernelProd_section_eq
            (d := d) normalization ζ ψ hr_pos
    _ ≤ (normalization * r ^ a) ^ (2 : Nat) *
          (Csp * r ^ d * |r|⁻¹ ^ (2 : Nat)) := by
          exact mul_le_mul_of_nonneg_left hspatial hcoef_nonneg
    _ = (normalization ^ (2 : Nat) * Csp) * r ^ (-3 : ℝ) := by
          calc
            (normalization * r ^ a) ^ (2 : Nat) *
                (Csp * r ^ d * |r|⁻¹ ^ (2 : Nat))
                = (normalization ^ (2 : Nat) * Csp) *
                    ((r ^ a) ^ (2 : Nat) * r ^ d * |r|⁻¹ ^ (2 : Nat)) := by
                  ring
            _ = (normalization ^ (2 : Nat) * Csp) * r ^ (-3 : ℝ) := by
                  dsimp [a]
                  rw [abk_largeScale_power_identity (d := d) hr_pos]

/-- The scale shell `(a,b] × R^d` in product coordinates. -/
@[expose]
def abkScaleShell {d : Nat} (a b : ℝ) : Set (ℝ × Vec d) :=
  {p | p.1 ∈ Set.Ioc a b}

theorem measurableSet_abkScaleShell {d : Nat} (a b : ℝ) :
    MeasurableSet (abkScaleShell (d := d) a b) :=
  measurableSet_Ioc.preimage continuous_fst.measurable

end GaussianFields

end

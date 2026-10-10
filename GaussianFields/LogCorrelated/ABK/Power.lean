/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import GaussianFields.LogCorrelated.ABK.Dilation
public import GaussianFields.LogCorrelated.ABK.Radial

/-!
# GaussianFields.LogCorrelated/ABK/Power

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory
open scoped ENNReal Topology

namespace GaussianFields


/-- After the cutoff self-convolution scaling, the ABK power-decomposition
integrand has exponent `-(1+α)`. -/
theorem abk_powerDecomposition_integrand_eq {d : Nat} (ζ : ABKCutoff d)
    {α r : ℝ} (hr : 0 < r) (x : Vec d) :
    r ^ (-(1 + (d : ℝ) + α)) * abkScaledCutoffSelfConvolution ζ r x =
      r ^ (-(1 + α)) * abkCutoffSelfConvolution ζ (r⁻¹ • x) := by
  rw [abkScaledCutoffSelfConvolution_eq_pow_mul ζ hr x]
  have hpow :
      r ^ (-(1 + (d : ℝ) + α)) * r ^ d = r ^ (-(1 + α)) := by
    have hr_nat : r ^ d = r ^ (d : ℝ) := by
      rw [Real.rpow_natCast]
    rw [hr_nat, ← Real.rpow_add hr]
    congr 1
    ring
  calc
    r ^ (-(1 + (d : ℝ) + α)) *
        (r ^ d * abkCutoffSelfConvolution ζ (r⁻¹ • x))
        = (r ^ (-(1 + (d : ℝ) + α)) * r ^ d) *
            abkCutoffSelfConvolution ζ (r⁻¹ • x) := by ring
    _ = r ^ (-(1 + α)) * abkCutoffSelfConvolution ζ (r⁻¹ • x) := by rw [hpow]

/-- At the unit radial point, the power-decomposition integral is exactly
`M_α^{-1}` by definition. -/
theorem abk_powerDecomposition_unit_integral_eq_mAlphaInv {d : Nat}
    (ζ : ABKCutoff d) (α : ℝ) :
    (∫ r in Set.Ioi (0 : ℝ),
        r ^ (-(1 + (d : ℝ) + α)) *
          abkScaledCutoffSelfConvolution ζ r (abkRadialPoint d 1)
        ∂(volume : Measure ℝ)) =
      abkMAlphaInv ζ α := by
  unfold abkMAlphaInv
  refine integral_congr_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
  have hrad : r⁻¹ • abkRadialPoint d 1 = abkRadialPoint d r⁻¹ := by
    ext i
    simp [abkRadialPoint, smul_eq_mul]
  rw [← hrad]
  exact abk_powerDecomposition_integrand_eq ζ hr (abkRadialPoint d 1)

/-- Unit-radius normalized form of the ABK power decomposition. -/
theorem abk_powerDecomposition_unit_normalized {d : Nat}
    (ζ : ABKCutoff d) {α : ℝ} (hα : abkMAlphaInv ζ α ≠ 0) :
    abkMAlpha ζ α *
      (∫ r in Set.Ioi (0 : ℝ),
        r ^ (-(1 + (d : ℝ) + α)) *
          abkScaledCutoffSelfConvolution ζ r (abkRadialPoint d 1)
        ∂(volume : Measure ℝ)) =
      1 := by
  rw [abk_powerDecomposition_unit_integral_eq_mAlphaInv ζ α]
  unfold abkMAlpha
  exact inv_mul_cancel₀ hα

/-- Reciprocal-change-of-variables form of `M_α^{-1}`:
`∫ r^{-1-α} (ζ*ζ)(1/r) dr = ∫ t^{α-1} (ζ*ζ)(t) dt`. -/
theorem abkMAlphaInv_eq_integral_rpow_selfConvolution {d : Nat}
    (ζ : ABKCutoff d) (α : ℝ) :
    abkMAlphaInv ζ α =
      ∫ t in Set.Ioi (0 : ℝ),
        t ^ (α - 1) * abkCutoffSelfConvolution ζ (abkRadialPoint d t)
        ∂(volume : Measure ℝ) := by
  let G : ℝ → ℝ := fun t =>
    t ^ (α - 1) * abkCutoffSelfConvolution ζ (abkRadialPoint d t)
  have hsubst := integral_comp_rpow_Ioi G (by norm_num : (-1 : ℝ) ≠ 0)
  unfold abkMAlphaInv
  rw [← hsubst]
  refine integral_congr_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
  have hr_pos : 0 < r := hr
  have hpow :
      r ^ (-(1 + α)) = r ^ (-2 : ℝ) * (r⁻¹) ^ (α - 1) := by
    calc
      r ^ (-(1 + α)) = r ^ ((-2 : ℝ) + -(α - 1)) := by
        congr 1
        ring
      _ = r ^ (-2 : ℝ) * r ^ (-(α - 1)) := by
        rw [Real.rpow_add hr_pos]
      _ = r ^ (-2 : ℝ) * (r⁻¹) ^ (α - 1) := by
        rw [Real.inv_rpow hr_pos.le, ← Real.rpow_neg hr_pos.le]
  change
    r ^ (-(1 + α)) *
        abkCutoffSelfConvolution ζ (abkRadialPoint d r⁻¹) =
      ((|(-1 : ℝ)| * r ^ ((-1 : ℝ) - 1)) *
        ((r ^ (-1 : ℝ)) ^ (α - 1) *
          abkCutoffSelfConvolution ζ (abkRadialPoint d (r ^ (-1 : ℝ)))))
  rw [hpow, Real.rpow_neg_one]
  norm_num
  ring

/-- One-dimensional scale substitution in the ABK radial power-decomposition integral. -/
theorem abkMAlphaInv_radial_scale {d : Nat} (ζ : ABKCutoff d) (α : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ r in Set.Ioi (0 : ℝ),
        r ^ (-(1 + α)) *
          abkCutoffSelfConvolution ζ (abkRadialPoint d (ρ * r⁻¹))
        ∂(volume : Measure ℝ)) =
      ρ ^ (-α) * abkMAlphaInv ζ α := by
  let G : ℝ → ℝ := fun s =>
    s ^ (-(1 + α)) * abkCutoffSelfConvolution ζ (abkRadialPoint d s⁻¹)
  let H : ℝ → ℝ := fun r =>
    r ^ (-(1 + α)) * abkCutoffSelfConvolution ζ (abkRadialPoint d (ρ * r⁻¹))
  have hb : 0 < ρ⁻¹ := inv_pos.mpr hρ
  have hcv := integral_comp_mul_left_Ioi G 0 hb
  have hcv' :
      (∫ r in Set.Ioi (0 : ℝ), G (ρ⁻¹ * r) ∂(volume : Measure ℝ)) =
        ρ * abkMAlphaInv ζ α := by
    simpa [G, abkMAlphaInv, smul_eq_mul, hρ.ne'] using hcv
  have hpoint :
      ∀ᵐ r ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        G (ρ⁻¹ * r) = ρ ^ (1 + α) * H r := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    have hr : 0 < r := hr
    have hmul_pos : 0 < ρ⁻¹ * r := mul_pos hb hr
    have hinv : (ρ⁻¹ * r)⁻¹ = ρ * r⁻¹ := by
      field_simp [hρ.ne', hr.ne']
    have hpow :
        (ρ⁻¹ * r) ^ (-(1 + α)) =
          ρ ^ (1 + α) * r ^ (-(1 + α)) := by
      have hρpow : (ρ⁻¹) ^ (-(1 + α)) = ρ ^ (1 + α) := by
        rw [Real.inv_rpow hρ.le, Real.rpow_neg hρ.le, inv_inv]
      calc
        (ρ⁻¹ * r) ^ (-(1 + α))
            = (ρ⁻¹) ^ (-(1 + α)) * r ^ (-(1 + α)) := by
              rw [Real.mul_rpow (inv_nonneg.mpr hρ.le) hr.le]
        _ = ρ ^ (1 + α) * r ^ (-(1 + α)) := by
              rw [hρpow]
    change
      (ρ⁻¹ * r) ^ (-(1 + α)) *
          abkCutoffSelfConvolution ζ (abkRadialPoint d ((ρ⁻¹ * r)⁻¹)) =
        ρ ^ (1 + α) *
          (r ^ (-(1 + α)) *
            abkCutoffSelfConvolution ζ (abkRadialPoint d (ρ * r⁻¹)))
    rw [hpow, hinv]
    ring
  have hInt :
      (∫ r in Set.Ioi (0 : ℝ), G (ρ⁻¹ * r) ∂(volume : Measure ℝ)) =
        ρ ^ (1 + α) *
          (∫ r in Set.Ioi (0 : ℝ), H r ∂(volume : Measure ℝ)) := by
    rw [← integral_const_mul]
    exact integral_congr_ae hpoint
  have hscale_ne : ρ ^ (1 + α) ≠ 0 :=
    (Real.rpow_pos_of_pos hρ (1 + α)).ne'
  have hpow_coef : (ρ ^ (1 + α))⁻¹ * ρ = ρ ^ (-α) := by
    rw [Real.rpow_add hρ 1 α, Real.rpow_one]
    calc
      (ρ * ρ ^ α)⁻¹ * ρ = (ρ ^ α)⁻¹ := by
        field_simp [hρ.ne', (Real.rpow_pos_of_pos hρ α).ne']
      _ = ρ ^ (-α) := by
        rw [Real.rpow_neg hρ.le]
  calc
    (∫ r in Set.Ioi (0 : ℝ), H r ∂(volume : Measure ℝ))
        = (ρ ^ (1 + α))⁻¹ *
            (∫ r in Set.Ioi (0 : ℝ), G (ρ⁻¹ * r) ∂(volume : Measure ℝ)) := by
          rw [hInt]
          field_simp [hscale_ne]
    _ = (ρ ^ (1 + α))⁻¹ * (ρ * abkMAlphaInv ζ α) := by
          rw [hcv']
    _ = ρ ^ (-α) * abkMAlphaInv ζ α := by
          rw [← mul_assoc, hpow_coef]

/-- Radial-point form of the ABK power-decomposition integral at radius `ρ`. -/
theorem abk_powerDecomposition_radial_integral_eq {d : Nat}
    (ζ : ABKCutoff d) (α : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ r in Set.Ioi (0 : ℝ),
        r ^ (-(1 + (d : ℝ) + α)) *
          abkScaledCutoffSelfConvolution ζ r (abkRadialPoint d ρ)
        ∂(volume : Measure ℝ)) =
      ρ ^ (-α) * abkMAlphaInv ζ α := by
  rw [← abkMAlphaInv_radial_scale ζ α hρ]
  refine integral_congr_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
  have hrad : r⁻¹ • abkRadialPoint d ρ = abkRadialPoint d (ρ * r⁻¹) := by
    ext i
    simp [abkRadialPoint, smul_eq_mul, mul_comm]
  rw [← hrad]
  exact abk_powerDecomposition_integrand_eq ζ hr (abkRadialPoint d ρ)

/-- Normalized radial-point form of the ABK power decomposition. -/
theorem abk_powerDecomposition_radial_normalized {d : Nat}
    (ζ : ABKCutoff d) {α ρ : ℝ} (hρ : 0 < ρ) (hα : abkMAlphaInv ζ α ≠ 0) :
    abkMAlpha ζ α *
      (∫ r in Set.Ioi (0 : ℝ),
        r ^ (-(1 + (d : ℝ) + α)) *
          abkScaledCutoffSelfConvolution ζ r (abkRadialPoint d ρ)
        ∂(volume : Measure ℝ)) =
      ρ ^ (-α) := by
  rw [abk_powerDecomposition_radial_integral_eq ζ α hρ]
  unfold abkMAlpha
  field_simp [hα]

/-- Full vector form of the ABK power-decomposition integral. -/
theorem abk_powerDecomposition_integral_eq {d : Nat} (hd : 0 < d)
    (ζ : ABKCutoff d) (α : ℝ) {x : Vec d} (hx : 0 < euclideanNorm x) :
    (∫ r in Set.Ioi (0 : ℝ),
        r ^ (-(1 + (d : ℝ) + α)) *
          abkScaledCutoffSelfConvolution ζ r x
        ∂(volume : Measure ℝ)) =
      (euclideanNorm x) ^ (-α) * abkMAlphaInv ζ α := by
  rw [← abkMAlphaInv_radial_scale ζ α hx]
  refine integral_congr_ae ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
  have hr_pos : 0 < r := hr
  have hinv_nonneg : 0 ≤ r⁻¹ := inv_nonneg.mpr hr_pos.le
  have hrep_nonneg : 0 ≤ euclideanNorm x * r⁻¹ :=
    mul_nonneg (euclideanNorm_nonneg x) hinv_nonneg
  have hnorm :
      euclideanNorm (r⁻¹ • x) =
        euclideanNorm (abkRadialPoint d (euclideanNorm x * r⁻¹)) := by
    rw [euclideanNorm_inv_smul, abs_of_nonneg hinv_nonneg,
      euclideanNorm_abkRadialPoint_of_nonneg hd hrep_nonneg]
    ring
  rw [abk_powerDecomposition_integrand_eq ζ hr_pos x]
  rw [abkCutoffSelfConvolution_radial ζ hnorm]

/-- Normalized full vector form of the ABK power decomposition. -/
theorem abk_powerDecomposition_normalized {d : Nat} (hd : 0 < d)
    (ζ : ABKCutoff d) {α : ℝ} (hα : abkMAlphaInv ζ α ≠ 0)
    {x : Vec d} (hx : 0 < euclideanNorm x) :
    abkMAlpha ζ α *
      (∫ r in Set.Ioi (0 : ℝ),
        r ^ (-(1 + (d : ℝ) + α)) *
          abkScaledCutoffSelfConvolution ζ r x
        ∂(volume : Measure ℝ)) =
      (euclideanNorm x) ^ (-α) := by
  rw [abk_powerDecomposition_integral_eq hd ζ α hx]
  unfold abkMAlpha
  field_simp [hα]

end GaussianFields

end

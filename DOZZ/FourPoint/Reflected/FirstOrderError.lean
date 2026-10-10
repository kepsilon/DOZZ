/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.FirstOrderFreezing
public import DOZZ.FourPoint.Reflected.RadialTilt
public import DOZZ.FourPoint.Reflected.Remainder
import Mathlib.Tactic
/-! # The actual Gaussian-weighted first-order Pareto error has a strictly higher power -/
public section
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The first-order radial likelihood times the actual outer inverse moment has the freezing
power needed for the inner-limit comparison, on the full punctured complex filter. -/
theorem reflected_first_order_radial_error_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (α₁ α₂ α₃ ξ h : ℝ) (hh : 0 ≤ h) (hξ : 0 < ξ) (hξ₁ : ξ < 1)
    (hα₁ : α₁ < Q γ) (hreflect : Q γ - α₁ < γ / 2)
    (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ z : ℂ in nhdsWithin 0 {z : ℂ | z ≠ 0},
      (∫⁻ ω, ENNReal.ofReal (Real.exp
        (γ * Xc ω 0 (-Real.log ‖z‖ + h) - γ * (Q γ - α₁) * (-Real.log ‖z‖ + h) -
          γ ^ 2 / 2 * (-Real.log ‖z‖))) *
        gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^
          (-((α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ + 1)) ∂P) ≤
      ENNReal.ofReal (C * ‖z‖ ^ (γ * (Q γ - α₁) +
        (1 - ξ) * ((α₁ + γ / 2 - Q γ) ^ 2 / 2))) := by
  let ν := Q γ - α₁
  let κ := γ * ν
  let δ := (α₁ + γ / 2 - Q γ) ^ 2 / 2
  let q := (α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ + 1
  obtain ⟨C₀, ε₀, hC₀, hε₀, hb⟩ := reflected_shifted_outer_freezing_bound
    P X hX γ hγ hγ₂ M hM α₁ α₂ α₃ hα₁ hreflect hs
  let D := Real.exp (-γ * ν * h + γ ^ 2 / 2 * h)
  let C := D * C₀
  have hD : 0 < D := Real.exp_pos _
  refine ⟨C, mul_pos hD hC₀, ?_⟩
  let l := nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}
  have hn : Tendsto (fun z : ℂ => ‖z‖) l (nhds 0) := by
    simpa only [norm_zero] using (continuous_norm.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
  have ht (s : ℝ) (hs : 0 < s) : Tendsto (fun z : ℂ => ‖z‖ ^ s) l (nhds 0) := by
    simpa only [Function.comp_def, Real.zero_rpow hs.ne'] using
      ((Real.continuous_rpow_const hs.le).tendsto (0 : ℝ)).comp hn
  filter_upwards [hn.eventually (gt_mem_nhds zero_lt_one),
    (ht (1 - ξ) (sub_pos.mpr hξ₁)).eventually (gt_mem_nhds hε₀),
    (ht ξ hξ).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    self_mem_nhdsWithin] with z hz hzε hzξ hz0
  have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hrad : 0 < ‖z‖ ^ (1 - ξ) := Real.rpow_pos_of_pos hp _
  have hsep : ‖z‖ ≤ ‖z‖ ^ (1 - ξ) / 2 := by
    have he : ‖z‖ = ‖z‖ ^ (1 - ξ) * ‖z‖ ^ ξ := by
      rw [← Real.rpow_add hp, sub_add_cancel, Real.rpow_one]
    calc
      _ = _ := he
      _ ≤ ‖z‖ ^ (1 - ξ) * (1 / 2) := mul_le_mul_of_nonneg_left hzξ.le hrad.le
      _ = _ := by ring
  have hm : 0 ≤ -Real.log ‖z‖ + h := by
    have hl := Real.log_nonpos hp.le hz.le
    linarith only [hl, hh]
  have hr : ‖z‖ ≤ ‖z‖ ^ (1 - ξ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hp hz.le
      (by linarith only [hξ] : 1 - ξ ≤ 1)
  have hout : Real.exp (-(-Real.log ‖z‖ + h)) ≤ ‖z‖ ^ (1 - ξ) := by
    apply le_trans _ hr
    have he : -(-Real.log ‖z‖ + h) ≤ Real.log ‖z‖ := by linarith only [hh]
    simpa only [Real.exp_log hp] using Real.exp_le_exp.mpr he
  have heβ (ω : Ω) : Real.exp
      (γ * Xc ω 0 (-Real.log ‖z‖ + h) - γ * ν * (-Real.log ‖z‖ + h) -
        γ ^ 2 / 2 * (-Real.log ‖z‖)) =
      (D * ‖z‖ ^ κ) * Real.exp
        (γ * Xc ω 0 (-Real.log ‖z‖ + h) - (-Real.log ‖z‖ + h) * γ ^ 2 / 2) := by
    rw [reflected_radial_first_order_tilt_identity]
    have he : Real.exp (-γ * ν * (-Real.log ‖z‖ + h) + γ ^ 2 / 2 * h) = D * ‖z‖ ^ κ := by
      rw [← reflected_log_radius_power κ ‖z‖ hp, ← Real.exp_add]
      congr 1
      ring
    rw [he]
    congr 2
    ring
  have hscale : 0 ≤ D * ‖z‖ ^ κ := mul_nonneg hD.le (Real.rpow_nonneg hp.le _)
  have htilt := reflected_outerMass_circle_tilt P X hX γ hγ hγ₂ M hM Xc hXc
    γ (-Real.log ‖z‖ + h) α₁ α₂ α₃ ξ q hm z hrad hout
  calc
    _ = ENNReal.ofReal (D * ‖z‖ ^ κ) *
        (∫⁻ ω, ENNReal.ofReal (Real.exp (γ * Xc ω 0 (-Real.log ‖z‖ + h) -
          (-Real.log ‖z‖ + h) * γ ^ 2 / 2)) *
          gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^ (-q) ∂P) := by
      change (∫⁻ ω, ENNReal.ofReal (Real.exp
        (γ * Xc ω 0 (-Real.log ‖z‖ + h) - γ * ν * (-Real.log ‖z‖ + h) -
          γ ^ 2 / 2 * (-Real.log ‖z‖))) *
        gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^ (-q) ∂P) = _
      calc
        _ = ∫⁻ ω, ENNReal.ofReal (D * ‖z‖ ^ κ) *
            (ENNReal.ofReal (Real.exp (γ * Xc ω 0 (-Real.log ‖z‖ + h) -
              (-Real.log ‖z‖ + h) * γ ^ 2 / 2)) *
              gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^ (-q)) ∂P := by
          apply lintegral_congr
          intro ω
          rw [heβ, ENNReal.ofReal_mul hscale, mul_assoc]
        _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (D * ‖z‖ ^ κ) *
        (∫⁻ ω, gammaHalfOuterMass γ (α₁ + γ) α₂ α₃ (M ω) z ξ ^ (-q) ∂P) := by rw [htilt]
    _ ≤ ENNReal.ofReal (D * ‖z‖ ^ κ) * ENNReal.ofReal (C₀ * (‖z‖ ^ (1 - ξ)) ^ δ) :=
      mul_le_mul' le_rfl (hb z ξ hrad hzε hsep)
    _ = _ := by
      rw [← ENNReal.ofReal_mul hscale, ← Real.rpow_mul hp.le]
      have hpow := Real.rpow_add hp κ ((1 - ξ) * δ)
      rw [hpow]
      congr 1
      dsimp only [C]
      ring

/-- The actual first-order expectation is negligible at the reflected leading scale. -/
theorem reflected_first_order_radial_error_littleO
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (α₁ α₂ α₃ ξ h : ℝ) (hh : 0 ≤ h) (hξ : 0 < ξ) (hξ₁ : ξ < 1)
    (hα₁ : α₁ < Q γ) (hreflect : Q γ - α₁ < γ / 2)
    (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃) :
    IsComplexLittleOAtZero (γ * (Q γ - α₁)) (fun z =>
      (((∫⁻ ω, ENNReal.ofReal (Real.exp
        (γ * Xc ω 0 (-Real.log ‖z‖ + h) - γ * (Q γ - α₁) * (-Real.log ‖z‖ + h) -
          γ ^ 2 / 2 * (-Real.log ‖z‖))) *
        gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^
          (-((α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ + 1)) ∂P).toReal : ℝ) : ℂ)) := by
  obtain ⟨C, hC, hb⟩ := reflected_first_order_radial_error_bound P X hX γ hγ hγ₂ M hM Xc hXc
    α₁ α₂ α₃ ξ h hh hξ hξ₁ hα₁ hreflect hs
  have hpos : 0 < α₁ + γ / 2 - Q γ := by linarith only [hreflect]
  have hδ : 0 < (α₁ + γ / 2 - Q γ) ^ 2 / 2 := div_pos (sq_pos_of_pos hpos) (by norm_num)
  have hη : γ * (Q γ - α₁) < γ * (Q γ - α₁) +
      (1 - ξ) * ((α₁ + γ / 2 - Q γ) ^ 2 / 2) :=
    lt_add_of_pos_right _ (mul_pos (sub_pos.mpr hξ₁) hδ)
  apply isComplexLittleOAtZero_of_norm_le_power (C := C) hη
  filter_upwards [hb] with z hz
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hz
  rw [ENNReal.toReal_ofReal (mul_nonneg hC.le (Real.rpow_nonneg (norm_nonneg z) _))] at hh
  exact hh

end DOZZ.Proofs

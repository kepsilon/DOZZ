/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.ChargeShift
public import DOZZ.FourPoint.Dual.Window
import Mathlib.Tactic
/-! # The actual dual radial restart likelihood

The inner factor is |z|² exp(γ(B_m−νm)). Its reflection power removes
all deterministic time dependence, leaving the 2ν Cameron–Martin tilt.
-/
public section
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- Exact dual radial scaling, before averaging or decoupling. -/
theorem dual_radial_restart_likelihood (γ ν r B m : ℝ)
    (hγ : γ ≠ 0) (hr : 0 < r) :
    (r ^ (2 : ℝ) * Real.exp (γ * (B - ν * m))) ^ (2 * ν / γ) =
      r ^ ((4 / γ) * ν) * Real.exp (2 * ν * B - m * (2 * ν) ^ 2 / 2) := by
  rw [Real.mul_rpow (Real.rpow_nonneg hr.le _) (Real.exp_pos _).le,
    ← Real.rpow_mul hr.le, ← Real.exp_mul]
  have he : (2 : ℝ) * (2 * ν / γ) = (4 / γ) * ν := by ring
  rw [he]
  congr 2
  field_simp

/-- Dividing the actual restart-weighted inverse mass by its fusion power gives
exactly the reflected-charge retained inverse moment. -/
theorem dual_radial_leading_moment_identity {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (α₁ α₂ α₃ ξ q m : ℝ) (hm : 0 ≤ m) (z : ℂ) (hz : z ≠ 0)
    (houtside : Real.exp (-m) ≤ ‖z‖ ^ (1 - ξ)) :
    (∫⁻ ω, ENNReal.ofReal ((‖z‖ ^ (2 : ℝ) *
      Real.exp (γ * (Xc ω 0 m - (Q γ - α₁) * m))) ^ (2 * (Q γ - α₁) / γ)) *
        dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^ (-q) ∂P) /
          ENNReal.ofReal (‖z‖ ^ ((4 / γ) * (Q γ - α₁))) =
      ∫⁻ ω, dualOuterMass γ (α₁ + 2 * (Q γ - α₁)) α₂ α₃ (M ω) z ξ ^ (-q) ∂P := by
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  simp_rw [dual_radial_restart_likelihood γ (Q γ - α₁) ‖z‖ _ m hγ.ne' hr,
    ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _), mul_assoc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have ht := dual_outerMass_circle_tilt P X hX γ hγ hγ₂ M hM Xc hXc
      (2 * (Q γ - α₁)) m α₁ α₂ α₃ ξ q hm z
      (Real.rpow_pos_of_pos hr _) houtside
  simp only [mul_assoc] at ht
  rw [ht]
  rw [mul_div_assoc]
  exact ENNReal.mul_div_cancel
    (ENNReal.ofReal_ne_zero_iff.mpr (Real.rpow_pos_of_pos hr _)) ENNReal.ofReal_ne_top


end DOZZ.Proofs

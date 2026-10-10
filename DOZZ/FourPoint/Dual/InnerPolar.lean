/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Dual.InnerKernel
public import DOZZ.FourPoint.Reflected.InnerPolar
import Mathlib.Tactic

/-! # Radial comparison of the actual dual inner mass

The source lateral projection and original chaos parameter are retained in
both scalar bounds. This is the deterministic part of the dual inner-limit comparison.
-/

public section
open MeasureTheory Filter Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The actual inner kernel integral is squeezed by its radial polar mass, with both explicit
scalar factors. The bound is valid before taking any stochastic expectation. -/
theorem dual_inner_kernel_mass_squeeze
    (γ α₁ α₂ α₃ R : ℝ) (hγ : γ ≠ 0) (z : ℂ) (A : TwoSidedPath) (M : Measure ℂ) (T : ℝ≥0)
    (hR : 0 ≤ R) (hR₁ : R < 1) (hz : 0 < ‖z‖)
    (hT : Real.exp (-(T : ℝ)) < 1) (hsep : Real.exp (-(T : ℝ)) ≤ R * ‖z‖) :
    let η := Real.exp (-(T : ℝ))
    let V := ∫⁻ s in Ioi (T : ℝ), ENNReal.ofReal
      (Real.exp (γ * (A s - (Q γ - α₁) * s))) ∂lateralProjectedGMC γ A M
    ENNReal.ofReal ((1-R) ^ (2 : ℝ) * (1-η)⁻¹ ^ (-|γ*α₂|) * ‖z‖ ^ (2 : ℝ)) * V ≤
      (∫⁻ x in {x : ℂ | 0 < ‖x‖ ∧ ‖x‖ < η},
        ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂M) ∧
    (∫⁻ x in {x : ℂ | 0 < ‖x‖ ∧ ‖x‖ < η},
        ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂M) ≤
      ENNReal.ofReal ((1+R) ^ (2 : ℝ) * (1-η)⁻¹ ^ |γ*α₂| * ‖z‖ ^ (2 : ℝ)) * V := by
  dsimp only
  rw [← reflected_inner_radial_polar γ α₁ A M T]
  let E : Set ℂ := {x : ℂ | 0 < ‖x‖ ∧ ‖x‖ < Real.exp (-(T : ℝ))}
  have hE : MeasurableSet E :=
    (measurableSet_lt measurable_const measurable_norm).inter
      (measurableSet_lt measurable_norm measurable_const)
  have hb (x : ℂ) (hx : x ∈ E) := dual_inner_kernel_squeeze γ α₁ α₂ α₃ R
    (Real.exp (-(T : ℝ))) hγ z x hR hR₁ (Real.exp_pos _).le hT hz hx.1
    (hx.2.le.trans hsep) hx.2.le
  constructor
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hE] with x hx
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ = ((1-R) ^ (2 : ℝ) * (1-Real.exp (-(T : ℝ)))⁻¹ ^ (-|γ*α₂|)) *
        (‖z‖ ^ (2 : ℝ) * ‖x‖ ^ (-(γ*α₁))) := by ring
      _ ≤ _ := (hb x hx).1
  · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hE] with x hx
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ ((1+R) ^ (2 : ℝ) * (1-Real.exp (-(T : ℝ)))⁻¹ ^ |γ*α₂|) *
        (‖z‖ ^ (2 : ℝ) * ‖x‖ ^ (-(γ*α₁))) := (hb x hx).2
      _ = _ := by ring


end DOZZ.Proofs

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.InnerKernelSqueeze
public import DOZZ.FourPoint.Reflected.GlobalReinsertion
import Mathlib.Tactic
/-! The inner kernel squeeze before taking expectations on the copied carrier. -/
@[expose] public section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

theorem reflected_reinserted_inner_kernel_mass_squeeze
    (γ α₁ α₂ α₃ R : ℝ) (z : ℂ) (A : TwoSidedPath) (N : Measure ℂ) (T : ℝ≥0)
    (hR : 0 ≤ R) (hR₁ : R < 1) (hz : 0 < ‖z‖)
    (hT : Real.exp (-(T : ℝ)) < 1) (hsep : Real.exp (-(T : ℝ)) ≤ R*‖z‖) :
    let η := Real.exp (-(T : ℝ))
    let J := ∫⁻ x in {x : ℂ | 0 < ‖x‖ ∧ ‖x‖ < η},
      ENNReal.ofReal (‖x‖^(-(γ*α₁)))*ENNReal.ofReal (reflected_global_reinsertionWeight γ A x) ∂N
    let I := ∫⁻ x in {x : ℂ | 0 < ‖x‖ ∧ ‖x‖ < η},
      ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x)*
        ENNReal.ofReal (reflected_global_reinsertionWeight γ A x) ∂N
    ENNReal.ofReal ((1-R)^(γ^2/2)*(1-η)⁻¹^(-|γ*α₂|))*
      (ENNReal.ofReal (‖z‖^(γ^2/2))*J) ≤ I ∧
    I ≤ ENNReal.ofReal ((1+R)^(γ^2/2)*(1-η)⁻¹^|γ*α₂|)*
      (ENNReal.ofReal (‖z‖^(γ^2/2))*J) := by
  dsimp only
  let E := {x : ℂ | 0 < ‖x‖ ∧ ‖x‖ < Real.exp (-(T : ℝ))}
  have hE : MeasurableSet E := (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt measurable_norm measurable_const)
  have hb (x : ℂ) (hx : x ∈ E) := reflected_inner_kernel_squeeze γ α₁ α₂ α₃ R
    (Real.exp (-(T : ℝ))) z x hR hR₁ (Real.exp_pos _).le hT hz hx.1
    (hx.2.le.trans hsep) hx.2.le
  constructor
  · rw [← mul_assoc,← ENNReal.ofReal_mul (by positivity),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hE] with x hx
    have hh := ENNReal.ofReal_le_ofReal (hb x hx).1
    simpa only [ENNReal.ofReal_mul (by positivity : 0 ≤ (1-R)^(γ^2/2)),
      ENNReal.ofReal_mul (by positivity : 0 ≤ (1-Real.exp (-(T : ℝ)))⁻¹^(-|γ*α₂|)),
      ENNReal.ofReal_mul (by positivity : 0 ≤ (1-R)^(γ^2/2)*
        (1-Real.exp (-(T : ℝ)))⁻¹^(-|γ*α₂|)),
      ENNReal.ofReal_mul (Real.rpow_nonneg hz.le (γ^2/2)),mul_assoc] using
        mul_le_mul_left hh (ENNReal.ofReal (reflected_global_reinsertionWeight γ A x))
  · rw [← mul_assoc,← ENNReal.ofReal_mul (by positivity),
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hE] with x hx
    have hh := ENNReal.ofReal_le_ofReal (hb x hx).2
    simpa only [ENNReal.ofReal_mul (by positivity : 0 ≤ (1+R)^(γ^2/2)),
      ENNReal.ofReal_mul (by positivity : 0 ≤ (1-Real.exp (-(T : ℝ)))⁻¹^|γ*α₂|),
      ENNReal.ofReal_mul (by positivity : 0 ≤ (1+R)^(γ^2/2)*
        (1-Real.exp (-(T : ℝ)))⁻¹^|γ*α₂|),
      ENNReal.ofReal_mul (Real.rpow_nonneg hz.le (γ^2/2)),mul_assoc] using
        mul_le_mul_left hh (ENNReal.ofReal (reflected_global_reinsertionWeight γ A x))

end DOZZ.Proofs

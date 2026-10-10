/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.InnerPolar
public import DOZZ.FourPoint.Reflected.CopiedInnerPolar
import Mathlib.Tactic
/-! The actual dual inner kernel on the independent lateral plane carrier. -/
@[expose] public section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The independently reinserted dual inner mass is squeezed by the restarted radial
functional of the translated lateral projection. The chaos parameter remains `γ`. -/
theorem dual_copied_inner_mass_squeeze
    (γ α₁ α₂ α₃ R : ℝ) (hγ : γ ≠ 0) (z : ℂ) (A : TwoSidedPath)
    (N : Measure ℂ) (h0 : N {0} = 0) (T : ℝ≥0)
    (hR : 0 ≤ R) (hR₁ : R < 1) (hz : 0 < ‖z‖)
    (hT : Real.exp (-(T : ℝ)) < 1) (hsep : Real.exp (-(T : ℝ)) ≤ R * ‖z‖) :
    let η := Real.exp (-(T : ℝ))
    let V := ∫⁻ u, (if 0 < u then ENNReal.ofReal (Real.exp
      (γ * (brownianShiftPath T (radialPositiveHalf A) (Real.toNNReal u) -
        (Q γ - α₁) * u))) else 0)
      ∂(N.map (fun x => -Real.log ‖x‖)).map (fun s => s - (T : ℝ))
    let β := ‖z‖ ^ (2 : ℝ) * Real.exp (γ * (A T - (Q γ - α₁) * T))
    let I := ∫⁻ x in {x : ℂ | 0 < ‖x‖ ∧ ‖x‖ < η},
      ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) *
        ENNReal.ofReal (reflected_global_reinsertionWeight γ A x) ∂N
    ENNReal.ofReal ((1-R) ^ (2 : ℝ) * (1-η)⁻¹ ^ (-|γ*α₂|) * β) * V ≤ I ∧
      I ≤ ENNReal.ofReal ((1+R) ^ (2 : ℝ) * (1-η)⁻¹ ^ |γ*α₂| * β) * V := by
  let W := fun x => ENNReal.ofReal (reflected_global_reinsertionWeight γ A x)
  have hW : Measurable W :=
    ((reflected_global_reinsertionWeight_measurable γ).comp
      (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hk : Measurable (fun x => ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x)) :=
    (dual_kernel_measurable γ α₁ α₂ α₃ z).ennreal_ofReal
  have hU : MeasurableSet {x : ℂ | 0 < ‖x‖ ∧ ‖x‖ < Real.exp (-(T : ℝ))} :=
    (measurableSet_lt measurable_const measurable_norm).inter
      (measurableSet_lt measurable_norm measurable_const)
  have hb := dual_inner_kernel_mass_squeeze γ α₁ α₂ α₃ R hγ z A
    (N.withDensity W) T hR hR₁ hz hT hsep
  rw [reflected_reinserted_lateral_projection γ A N h0,
    reflected_inner_polar_restart γ (Q γ - α₁) A _ T] at hb
  dsimp only at hb ⊢
  rw [setLIntegral_withDensity_eq_setLIntegral_mul N hW hk hU] at hb
  have he (c : ℝ) : ENNReal.ofReal (c * ‖z‖ ^ (2 : ℝ)) *
      (ENNReal.ofReal (Real.exp (γ * (A T - (Q γ - α₁) * T))) *
        (∫⁻ u, (if 0 < u then ENNReal.ofReal (Real.exp
          (γ * (brownianShiftPath T (radialPositiveHalf A) (Real.toNNReal u) -
            (Q γ - α₁) * u))) else 0)
          ∂(N.map (fun x => -Real.log ‖x‖)).map (fun s => s - (T : ℝ)))) =
      ENNReal.ofReal (c * (‖z‖ ^ (2 : ℝ) *
        Real.exp (γ * (A T - (Q γ - α₁) * T)))) *
        (∫⁻ u, (if 0 < u then ENNReal.ofReal (Real.exp
          (γ * (brownianShiftPath T (radialPositiveHalf A) (Real.toNNReal u) -
            (Q γ - α₁) * u))) else 0)
          ∂(N.map (fun x => -Real.log ‖x‖)).map (fun s => s - (T : ℝ))) := by
    rw [← mul_assoc, ← ENNReal.ofReal_mul' (by positivity : 0 ≤ Real.exp
      (γ * (A T - (Q γ - α₁) * T))), mul_assoc]
  simp only [Pi.mul_apply] at hb
  rw [he, he] at hb
  simpa only [W, mul_comm] using hb

end DOZZ.Proofs

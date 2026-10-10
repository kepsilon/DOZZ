/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.LocalizationMassComparison
public import DOZZ.Correlations.Tails.CopiedErrorMassBound

/-! The copied multiplier differs from its constant leading weight by a controlled error. -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

theorem actual_copied_localization_comparison
    (μ : Measure ℂ) (z : ℂ) (γ α n nb δ ρ : ℝ) (hδρ : δ ≤ ρ) (hρ1 : ρ ≤ 1)
    (F : ℂ → ℝ) (hFm : Measurable F) (hF : ∀ x, 0 ≤ F x)
    (χ : ℂ → ℝ) (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hχzero : ∀ x ∉ Metric.ball (0 : ℂ) ρ, χ x = 0)
    (hχone : ∀ x ∈ Metric.ball (0 : ℂ) δ, χ x = 1) :
    (∫⁻ x, ENNReal.ofReal (χ x*copiedMultiplier z γ n nb F x)*
      (ENNReal.ofReal ‖x‖)^(-γ*α) ∂μ) ≤
        ENNReal.ofReal (F z*Real.exp (-4*Real.log ‖z‖))*
          (∫⁻ x in Metric.ball (0 : ℂ) 1, (ENNReal.ofReal ‖x‖)^(-γ*α) ∂μ)+
        (∫⁻ x in Metric.ball (0 : ℂ) ρ, ENNReal.ofReal
          |copiedMultiplier z γ n nb F x-F z*Real.exp (-4*Real.log ‖z‖)| *
            (ENNReal.ofReal ‖x‖)^(-γ*α) ∂μ) ∧
    ENNReal.ofReal (F z*Real.exp (-4*Real.log ‖z‖))*
        (∫⁻ x in Metric.ball (0 : ℂ) 1, (ENNReal.ofReal ‖x‖)^(-γ*α) ∂μ) ≤
      (∫⁻ x, ENNReal.ofReal (χ x*copiedMultiplier z γ n nb F x)*
        (ENNReal.ofReal ‖x‖)^(-γ*α) ∂μ)+
      (∫⁻ x in Metric.ball (0 : ℂ) ρ, ENNReal.ofReal
        |copiedMultiplier z γ n nb F x-F z*Real.exp (-4*Real.log ‖z‖)| *
          (ENNReal.ofReal ‖x‖)^(-γ*α) ∂μ)+
      ENNReal.ofReal (F z*Real.exp (-4*Real.log ‖z‖))*
        (∫⁻ x in Metric.ball (0 : ℂ) 1 \ Metric.ball (0 : ℂ) δ,
          (ENNReal.ofReal ‖x‖)^(-γ*α) ∂μ) := by
  let c := F z*Real.exp (-4*Real.log ‖z‖)
  let U := copiedMultiplier z γ n nb F
  let k := fun x : ℂ => (ENNReal.ofReal ‖x‖)^(-γ*α)
  let u := fun x => ENNReal.ofReal (U x)*k x
  let v := fun x => ENNReal.ofReal c*k x
  let e := fun x => ENNReal.ofReal |U x-c| *k x
  have hc : 0 ≤ c := mul_nonneg (hF z) (Real.exp_nonneg _)
  have hU (x : ℂ) : 0 ≤ U x := by
    unfold U copiedMultiplier
    exact mul_nonneg (mul_nonneg (hF _) (Real.exp_nonneg _)) (Real.exp_nonneg _)
  have hUm : Measurable U := by
    unfold U copiedMultiplier localPinCoefficient
    fun_prop
  have hk : Measurable k := by unfold k; fun_prop
  have hv : Measurable v := measurable_const.mul hk
  have he : Measurable e := (continuous_abs.measurable.comp (hUm.sub_const c)).ennreal_ofReal.mul hk
  have hpoint (x : ℂ) (_ : x ∈ Metric.ball (0 : ℂ) ρ) : u x ≤ v x+e x ∧ v x ≤ u x+e x := by
    constructor
    · calc u x ≤ ENNReal.ofReal (c+|U x-c|)*k x := mul_le_mul'
            (ENNReal.ofReal_le_ofReal (by linarith only [le_abs_self (U x-c)])) le_rfl
        _ = v x+e x := by rw [ENNReal.ofReal_add hc (abs_nonneg _),add_mul]
    · calc v x ≤ ENNReal.ofReal (U x+|U x-c|)*k x := mul_le_mul'
            (ENNReal.ofReal_le_ofReal (by linarith only [neg_abs_le (U x-c)])) le_rfl
        _ = u x+e x := by rw [ENNReal.ofReal_add (hU x) (abs_nonneg _),add_mul]
  have h := copied_mass_comparison μ δ ρ hδρ hρ1 χ hχ hχzero hχone u v e hv he hpoint
  have hlocal : (∫⁻ x, ENNReal.ofReal (χ x)*u x ∂μ) =
      (∫⁻ x, ENNReal.ofReal (χ x*U x)*k x ∂μ) := by
    apply lintegral_congr
    intro x
    rw [ENNReal.ofReal_mul (hχ x).1,mul_assoc]
  have hfull : (∫⁻ x in Metric.ball (0 : ℂ) 1, v x ∂μ) =
      ENNReal.ofReal c*(∫⁻ x in Metric.ball (0 : ℂ) 1, k x ∂μ) :=
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hout : (∫⁻ x in Metric.ball (0 : ℂ) 1 \ Metric.ball (0 : ℂ) δ, v x ∂μ) =
      ENNReal.ofReal c*(∫⁻ x in Metric.ball (0 : ℂ) 1 \ Metric.ball (0 : ℂ) δ, k x ∂μ) :=
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  rw [hlocal,hfull,hout] at h
  exact h


end DOZZ.Proofs

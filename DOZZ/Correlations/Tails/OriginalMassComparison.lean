/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.LocalizationMassComparison
public import DOZZ.Statements.Correlations.LocalSingularMass

/-! The original insertion mass and its common compact localization. -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

theorem original_localized_mass_comparison
    {Ω : Type*} (M : Ω → Measure ℂ) (z : ℂ) (γ α δ ρ : ℝ) (hρ1 : ρ ≤ 1)
    (F : ℂ → ℝ) (hF : Measurable F)
    (χ : ℂ → ℝ) (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hχzero : ∀ x ∉ Metric.ball (0 : ℂ) ρ, χ x = 0)
    (hχone : ∀ x ∈ Metric.ball (0 : ℂ) δ, χ x = 1) (ω : Ω) :
    (∫⁻ y, ENNReal.ofReal (χ (y-z)*F y)*(ENNReal.ofReal ‖y-z‖)^(-γ*α) ∂M ω) ≤
      localSingularMass M F z γ α ω ∧
    localSingularMass M F z γ α ω ≤
      (∫⁻ y, ENNReal.ofReal (χ (y-z)*F y)*(ENNReal.ofReal ‖y-z‖)^(-γ*α) ∂M ω)+
      (∫⁻ y in Metric.ball z 1 \ Metric.ball z δ,
        ENNReal.ofReal (F y)*(ENNReal.ofReal ‖y-z‖)^(-γ*α) ∂M ω) := by
  let w := fun y : ℂ => ENNReal.ofReal (F y)*(ENNReal.ofReal ‖y-z‖)^(-γ*α)
  have hw : Measurable w := by unfold w; fun_prop
  have hzero (y : ℂ) (hy : y ∉ Metric.ball z 1) : χ (y-z) = 0 := by
    apply hχzero
    intro h
    apply hy
    have hnorm : ‖y-z‖ < ρ := by simpa only [Metric.mem_ball,dist_zero_right] using h
    simpa only [Metric.mem_ball,dist_eq_norm] using hnorm.trans_le hρ1
  have hone (y : ℂ) (hy : y ∈ Metric.ball z δ) : χ (y-z) = 1 := by
    apply hχone
    simpa only [Metric.mem_ball,dist_zero_right,dist_eq_norm,sub_zero] using hy
  have h := localized_mass_comparison (M ω) z δ (fun y => χ (y-z))
    (fun y => hχ (y-z)) hzero hone w hw
  have hl : (∫⁻ y, ENNReal.ofReal (χ (y-z))*w y ∂M ω) =
      (∫⁻ y, ENNReal.ofReal (χ (y-z)*F y)*(ENNReal.ofReal ‖y-z‖)^(-γ*α) ∂M ω) := by
    apply lintegral_congr
    intro y
    rw [ENNReal.ofReal_mul (hχ (y-z)).1,mul_assoc]
  have hm : localSingularMass M F z γ α ω = ∫⁻ y in Metric.ball z 1, w y ∂M ω := by
    rw [localSingularMass,← lintegral_indicator Metric.isOpen_ball.measurableSet]
    rfl
  rw [hl,← hm] at h
  exact h

theorem actual_prefactor_product (z : ℂ) (hz : 0 < ‖z‖) (f γ n : ℝ) :
    ENNReal.ofReal (Real.exp (γ*n-γ^2*Real.log ‖z‖))*
      ENNReal.ofReal (f*Real.exp (-4*Real.log ‖z‖)) =
    ENNReal.ofReal (f*‖z‖^(-4 : ℝ)*Real.exp (γ*n-γ^2*Real.log ‖z‖)) := by
  have he : ‖z‖^(-4 : ℝ) = Real.exp (-4*Real.log ‖z‖) := by
    rw [Real.rpow_def_of_pos hz,mul_comm]
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),he]
  congr 1
  ring


end DOZZ.Proofs

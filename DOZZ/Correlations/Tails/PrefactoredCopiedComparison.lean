/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.ActualCopiedMassComparison
public import DOZZ.Correlations.Tails.OriginalMassComparison

/-! Literal prefactored copied-mass comparisons with their total remainder. -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

theorem prefactored_copied_localization_comparison
    (μ : Measure ℂ) (z : ℂ) (hz : 0 < ‖z‖) (γ α n nb δ ρ : ℝ) (hδρ : δ ≤ ρ) (hρ1 : ρ ≤ 1)
    (F : ℂ → ℝ) (hFm : Measurable F) (hF : ∀ x, 0 ≤ F x)
    (χ : ℂ → ℝ) (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hχzero : ∀ x ∉ Metric.ball (0 : ℂ) ρ, χ x = 0)
    (hχone : ∀ x ∈ Metric.ball (0 : ℂ) δ, χ x = 1) :
    let S := ENNReal.ofReal (Real.exp (γ*nb-γ^2*Real.log ‖z‖))
    let V := ENNReal.ofReal (F z*‖z‖^(-4 : ℝ)*Real.exp (γ*nb-γ^2*Real.log ‖z‖))
    let L := S*(∫⁻ x, ENNReal.ofReal (χ x*copiedMultiplier z γ n nb F x)*
      (ENNReal.ofReal ‖x‖)^(-γ*α) ∂μ)
    let B := V*(∫⁻ x in Metric.ball (0 : ℂ) 1, (ENNReal.ofReal ‖x‖)^(-γ*α) ∂μ)
    let E := S*(∫⁻ x in Metric.ball (0 : ℂ) ρ, ENNReal.ofReal
      |copiedMultiplier z γ n nb F x-F z*Real.exp (-4*Real.log ‖z‖)| *
        (ENNReal.ofReal ‖x‖)^(-γ*α) ∂μ)+
      V*(∫⁻ x in Metric.ball (0 : ℂ) 1 \ Metric.ball (0 : ℂ) δ,
        (ENNReal.ofReal ‖x‖)^(-γ*α) ∂μ)
    L ≤ B+E ∧ B ≤ L+E := by
  dsimp only
  have h := actual_copied_localization_comparison μ z γ α n nb δ ρ hδρ hρ1 F hFm hF
    χ hχ hχzero hχone
  let S := ENNReal.ofReal (Real.exp (γ*nb-γ^2*Real.log ‖z‖))
  let c := ENNReal.ofReal (F z*Real.exp (-4*Real.log ‖z‖))
  let I := ∫⁻ x in Metric.ball (0 : ℂ) 1, (ENNReal.ofReal ‖x‖)^(-γ*α) ∂μ
  let J := ∫⁻ x in Metric.ball (0 : ℂ) 1 \ Metric.ball (0 : ℂ) δ,
    (ENNReal.ofReal ‖x‖)^(-γ*α) ∂μ
  have h₁ := mul_le_mul' (le_refl S) h.1
  have h₂ := mul_le_mul' (le_refl S) h.2
  rw [mul_add,← mul_assoc S c I,actual_prefactor_product z hz (F z) γ nb] at h₁
  rw [mul_add,mul_add,← mul_assoc S c I,← mul_assoc S c J,
    actual_prefactor_product z hz (F z) γ nb] at h₂
  constructor
  · exact h₁.trans (add_le_add le_rfl le_self_add)
  · simpa only [add_assoc] using h₂


end DOZZ.Proofs

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.TaylorIntermediate
public import DOZZ.FourPoint.TaylorMomentBudget

/-! The source optimized intermediate-region exponent with its actual supplied-GMC estimate. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Optimize the positive order inside the moment range, while retaining the original
inverse order p+2 in the actual positive Taylor square. -/
theorem twoRooted_intermediate_optimized_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hγsq : 2 < γ ^ 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ p q : ℝ) (hα₁ : γ / 2 < α₁) (hα₁2 : α₁ < 2 / γ)
    (hp : 0 ≤ p) (hq : 1 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 4 →
      ∀ z : ℂ, ‖z‖ ≤ ρ → ∀ d : ℝ, 0 < d →
        gammaHalfTwoRootedMajorantOn P M γ α₁ α₂ α₃ p z
          (Metric.ball 0 ρ \ Metric.ball z d) ≤
            ENNReal.ofReal (C * (d⁻¹) ^ 2 * ρ ^ ((γ / 2 + Q γ - α₁) ^ 2 / (2 * q))) := by
  let s : ℝ := (γ / 2 + Q γ - α₁) / (γ * q)
  obtain ⟨hs, hs2, hrange, hopt⟩ := twoRooted_optimized_order γ α₁ q hγ hγ2 hγsq hα₁ hα₁2 hq
  have hαQ : α₁ < Q γ := by unfold Q; linarith only [hα₁2, hγ]
  obtain ⟨C, hC, hbound⟩ := twoRooted_intermediate_physical_bound P X hX γ hγ hγ2 M hM
    α₁ α₂ α₃ p s q hαQ hp hs hs2.le hq hrange
  have heq : (γ ^ 2 / 2) * s + (γ * (Q γ - α₁) * (q * s) - γ ^ 2 * (q * s) ^ 2 / 2) / q =
      (γ / 2 + Q γ - α₁) ^ 2 / (2 * q) := by
    calc
      _ = γ * (Q γ - α₁ + γ / 2) * s - γ ^ 2 * q * s ^ 2 / 2 := by
        have hq0 : q ≠ 0 := (zero_lt_one.trans hq).ne'
        field_simp
        ring
      _ = _ := hopt
  rw [heq] at hbound
  exact ⟨C, hC, hbound⟩

end DOZZ.Proofs

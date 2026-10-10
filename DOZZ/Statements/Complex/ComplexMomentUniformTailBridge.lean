/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Complex.HorizontalStrip
import DOZZ.Complex.Basic

/-! The statement `DOZZ.complexMoment_uniform_tail_bridge`,
proved by `DOZZ.Proofs.complexMoment_uniform_tail_bridge`. -/

public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ

/-- Uniform tail-family Abelian boundary limit (see [KRV, Proposition 8.1]). A tail estimate only
for the limiting random variable is insufficient. Integrability is explicit on the eventually
positive moment exponents. -/
theorem complexMoment_uniform_tail_bridge {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℝ → Ω → ℝ)
    (c : ℝ → ℝ) (c₀ β η γ d₀ C : ℝ)
    (hβ : 0 < β) (hη : 0 < η) (hγ : 0 < γ) (hd₀ : 0 < d₀) (hC : 0 ≤ C)
    (hY : ∀ d : ℝ, 0 < d → d < d₀ → AEMeasurable (Y d) P)
    (hpos : ∀ d : ℝ, 0 < d → d < d₀ → ∀ᵐ ω ∂P, 0 ≤ Y d ω)
    (hc : Tendsto c (𝓝[>] 0) (𝓝 c₀))
    (htail : ∀ (d : ℝ) (hd : 0 < d) (hd' : d < d₀) (t : ℝ), 1 ≤ t →
      |realUpperTail P (Y d) (hY d hd hd') t - c d * t ^ (-β)| ≤ C * t ^ (-β - η)) :
    (∀ d : ℝ, 0 < d → d < min d₀ (γ * β) →
      Integrable (fun ω => (Y d ω : ℂ) ^ ((β - d / γ : ℝ) : ℂ)) P) ∧
    Tendsto (fun d : ℝ => (d : ℂ) *
      (∫ ω, (Y d ω : ℂ) ^ ((β - d / γ : ℝ) : ℂ) ∂P))
      (𝓝[>] 0) (𝓝 ((γ * β * c₀ : ℝ) : ℂ)) := by exact DOZZ.Proofs.complexMoment_uniform_tail_bridge P Y c c₀ β η γ d₀ C hβ hη hγ hd₀ hC hY hpos hc htail

end DOZZ

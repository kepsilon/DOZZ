/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Complex.TwoTailRational
import DOZZ.Complex.TwoTail

/-! The statement `DOZZ.complexMoment_two_tail_residues_of_inverse_moments`,
proved by `DOZZ.Proofs.complexMoment_two_tail_residues_of_inverse_moments`. -/

public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ

/-- The lower-tail extension of [KRV, Lemma 10.4] actually needed by [KRV, Proposition 10.1],
including `s ≤ 0`. Every inverse moment is a separate probabilistic input; it does not follow
from the displayed upper-tail expansion. -/
theorem complexMoment_two_tail_residues_of_inverse_moments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ) (hY : AEMeasurable Y P) (hpos : ∀ᵐ ω ∂P, 0 < Y ω)
    (hinv : ∀ q : ℝ, 0 < q → Integrable (fun ω => Y ω ^ (-q)) P)
    (c₁ c₂ c₃ β₁ β₂ β₃ : ℝ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₃ : 0 < c₃)
    (hβ₁ : 0 < β₁) (hβ₁₂ : β₁ < β₂) (hβ₂₃ : β₂ < β₃)
    (htail : ∀ t : ℝ, 1 ≤ t →
      |realUpperTail P Y hY t - c₁ * t ^ (-β₁) - c₂ * t ^ (-β₂)| ≤ c₃ * t ^ (-β₃)) :
    (∀ s : ℂ, s.re < β₁ → Integrable (fun ω => (Y ω : ℂ) ^ s) P) ∧
    DifferentiableOn ℂ (fun s : ℂ => ∫ ω, (Y ω : ℂ) ^ s ∂P)
      {s : ℂ | s.re < β₁} ∧
    ∃ r : ℂ → ℂ, DifferentiableOn ℂ r {s | s.re < β₃} ∧
      MeromorphicOn (fun s => twoTailRational c₁ c₂ β₁ β₂ s + r s) {s | s.re < β₃} ∧
      (∀ s : ℂ, s.re < β₁ →
        (∫ ω, (Y ω : ℂ) ^ s ∂P) = twoTailRational c₁ c₂ β₁ β₂ s + r s) ∧
      r 0 = 1 ∧
      Tendsto (fun s => (s - (β₁ : ℂ)) *
        (twoTailRational c₁ c₂ β₁ β₂ s + r s)) (𝓝[≠] (β₁ : ℂ)) (𝓝 (-(β₁ * c₁ : ℝ) : ℂ)) ∧
      Tendsto (fun s => (s - (β₂ : ℂ)) *
        (twoTailRational c₁ c₂ β₁ β₂ s + r s)) (𝓝[≠] (β₂ : ℂ)) (𝓝 (-(β₂ * c₂ : ℝ) : ℂ)) := by exact DOZZ.Proofs.complexMoment_two_tail_residues_of_inverse_moments P Y hY hpos hinv c₁ c₂ c₃ β₁ β₂ β₃ hc₁ hc₂ hc₃ hβ₁ hβ₁₂ hβ₂₃ htail

end DOZZ

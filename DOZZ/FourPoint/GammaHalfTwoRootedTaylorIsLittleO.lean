/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.TaylorFundamentalEstimate
public import DOZZ.FourPoint.TwoRootedTaylorAdapter

/-! Proof of the literal two-rooted Taylor little-o statement
`DOZZ.gammaHalf_twoRooted_Taylor_is_littleO` on the corrected strict domain. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology
namespace DOZZ.Proofs

theorem gammaHalf_twoRooted_Taylor_is_littleO {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hγsq : 2 < γ ^ 2)
    (hα₁ : γ / 2 < α₁) (hα₁₂ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    IsComplexLittleOAtZero (γ * (Q γ - α₁))
      (gammaHalfTwoRootedTerm P M γ α₁ α₂ α₃
        ((α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ)) := by
  have _hsource_charges : α₂ < Q γ ∧ α₃ < Q γ := ⟨hα₂, hα₃⟩
  let p : ℝ := (α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ
  have hp : 0 ≤ p := (div_pos (by linarith only [hs]) hγ).le
  obtain ⟨η, C, r, hη, hC, hr, hI⟩ := twoRooted_fundamental_estimate
    P X hX γ hγ hγ₂ hγsq M hM α₁ α₂ α₃ p hα₁ hα₁₂ hp
  obtain ⟨_, hκ, _⟩ := twoRooted_time_exponent γ α₁ hγ hγsq hα₁ hα₁₂
  exact twoRooted_littleO_of_majorant P M γ α₁ α₂ α₃ p
    (γ * (Q γ - α₁)) η C r hκ hη hC.le hr hI

end DOZZ.Proofs

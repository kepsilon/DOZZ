/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.FullTaylorLimit

/-! # The one-rooted Taylor asymptotic -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- The one-rooted contribution has the exact planar coefficient and an `o(|z|^(γ(Q - α₁)))`
remainder [KRV, Lemma 9.2]. -/
theorem gammaHalf_oneRooted_Taylor_asymptotic {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ ^ 2 < 4) (hα₁ : γ / 2 < α₁)
    (hγsq : 2 < γ ^ 2)
    (hα₁₂ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    let p := (α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ
    let κ := γ * (Q γ - α₁)
    ∃ r : ℂ → ℂ,
      (∀ z, gammaHalfOneRootedTerm P M γ α₁ α₂ α₃ p z =
        (-(p * gammaHalfRootedCoefficient P M γ α₁ α₂ α₃ p) : ℂ) *
          (‖z‖ ^ κ : ℝ) + r z) ∧ IsComplexLittleOAtZero κ r := by
  intro p κ
  have hγ2 : γ < 2 := by nlinarith
  have hp : 0 ≤ p := (div_pos (by linarith) hγ).le
  let F := gammaHalfOneRootedTerm P M γ α₁ α₂ α₃ p
  let C : ℂ := -(p * gammaHalfRootedCoefficient P M γ α₁ α₂ α₃ p)
  refine ⟨fun z => F z - C * (‖z‖ ^ κ : ℝ), ?_, ?_⟩
  · intro z
    change F z = C * (‖z‖ ^ κ : ℝ) + (F z - C * (‖z‖ ^ κ : ℝ))
    ring
  · apply fusion_littleO_of_normalized_tendsto κ F C
    simpa only [F, C, κ, neg_mul, Complex.ofReal_neg, Complex.ofReal_mul] using
      fusionFullOneRooted_normalized_tendsto P X hX γ hγ hγ2 M hM α₁ α₂ α₃
        hα₁ hγsq hα₁₂ hα₂ hα₃ p hp

end DOZZ.Proofs

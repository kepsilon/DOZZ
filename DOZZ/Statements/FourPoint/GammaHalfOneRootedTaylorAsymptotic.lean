/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.IsComplexLittleOAtZero
import DOZZ.FourPoint.Fusion.OneRootedTaylor

/-! The statement `DOZZ.gammaHalf_oneRooted_Taylor_asymptotic`,
proved by `DOZZ.Proofs.gammaHalf_oneRooted_Taylor_asymptotic`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

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
          (‖z‖ ^ κ : ℝ) + r z) ∧ IsComplexLittleOAtZero κ r := by exact DOZZ.Proofs.gammaHalf_oneRooted_Taylor_asymptotic P X M γ α₁ α₂ α₃ hγ hγ₂ hα₁ hγsq hα₁₂ hα₂ hα₃ hs hX hM

end DOZZ

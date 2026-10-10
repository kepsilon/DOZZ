/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.GammaHalfOuterMoment
import DOZZ.FourPoint.Reflected.InnerLimit

/-! The statement `DOZZ.gammaHalf_reflected_inner_limit`,
proved by `DOZZ.Proofs.gammaHalf_reflected_inner_limit`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- Exact reflected coefficient from the inner cluster, in explicit little-o form. -/
theorem gammaHalf_reflected_inner_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (X : Ω → Distr)
    (γ μ α₁ α₂ α₃ ξ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hμ : 0 < μ)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃)
    (hξ : 0 < ξ) (hξ₂ : ξ < 1)
    (hreflect : Q γ - α₁ < γ / 2)
    (hnear : γ * (Q γ - α₁) < min 1 ξ)
    (hfreeze : γ * (Q γ - α₁) <
      (1 - ξ) * (γ * (Q γ - α₁) + (α₁ + γ / 2 - Q γ) ^ 2 / 2))
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∃ B : ℝ → Ω → BrownianPath × BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
        IsReflectionData P γ α₁ (B α₁) Z ∧
        let p := (α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ
        let κ := γ * (Q γ - α₁)
        ∃ r : ℂ → ℂ,
          (∀ z,
            (((gammaHalfMoment P M γ α₁ α₂ α₃ p z -
                gammaHalfOuterMoment P M γ α₁ α₂ α₃ p z ξ) : ℝ) : ℂ) =
              ((((1 / 2 * μ ^ p * γ * (Real.Gamma p)⁻¹ *
                  reflectionR P γ μ α₁ (B α₁) Z *
                  structureConstant P M γ μ (2 * Q γ - α₁ - γ / 2) α₂ α₃ : ℝ) : ℂ) *
                ((‖z‖ ^ κ : ℝ) : ℂ)) + r z)) ∧
            IsComplexLittleOAtZero κ r := by exact DOZZ.Proofs.gammaHalf_reflected_inner_limit P M X γ μ α₁ α₂ α₃ ξ hγ hγ₂ hμ hα₁ hα₂ hα₃ hs hξ hξ₂ hreflect hnear hfreeze hX hM

end DOZZ

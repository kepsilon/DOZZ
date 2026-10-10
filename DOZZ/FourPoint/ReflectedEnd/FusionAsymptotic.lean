/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.ReflectedEnd.FusionReduction
public import DOZZ.Statements.FourPoint.GammaHalfReflectedInnerLimit

/-! Reflected fusion: assemble the inner and outer limits with their original witness. -/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The exact reflected fusion asymptotic, retaining the supplied-space reflection data. -/
theorem gammaHalf_reflected_fusion_asymptotic {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (X : Ω → Distr)
    (γ μ α₁ α₂ α₃ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hμ : 0 < μ)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃)
    (hreflect : Q γ - α₁ < γ / 2)
    (hnear : ∃ ξ : ℝ, 0 < ξ ∧ ξ < 1 ∧ γ * (Q γ - α₁) < ξ ∧
      γ * (Q γ - α₁) < (1 - ξ) * (γ * (Q γ - α₁) + (α₁ + γ / 2 - Q γ) ^ 2 / 2))
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∃ B : ℝ → Ω → BrownianPath × BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
        IsReflectionData P γ α₁ (B α₁) Z ∧
        let κ := γ * (Q γ - α₁)
        ∃ r : ℂ → ℝ,
          (∀ z, fourPointT P M γ μ (-γ / 2) α₁ α₂ α₃ z =
            structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ +
              reflectionR P γ μ α₁ (B α₁) Z *
                structureConstant P M γ μ (2 * Q γ - α₁ - γ / 2) α₂ α₃ *
                  (‖z‖ ^ κ : ℝ) + r z) ∧
            Tendsto (fun z => r z / ‖z‖ ^ κ)
              (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}) (nhds 0) := by
  obtain ⟨ξ, hξ, hξ₂, hslack, hfreeze⟩ := hnear
  have hinner := DOZZ.gammaHalf_reflected_inner_limit P M X γ μ α₁ α₂ α₃ ξ
    hγ hγ₂ hμ hα₁ hα₂ hα₃ hs hξ hξ₂ hreflect
    (lt_min (hslack.trans hξ₂) hslack) hfreeze hX hM
  exact gammaHalf_reflected_fusion_asymptotic_of_inner_limit
    P M X γ μ α₁ α₂ α₃ ξ hγ hγ₂ hμ hα₁ hα₂ hα₃ hs hreflect
    hξ hξ₂ hslack hfreeze hX hM hinner

end DOZZ.Proofs

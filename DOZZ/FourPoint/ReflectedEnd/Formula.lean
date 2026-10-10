/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.ReflectedEnd.InnerClassificationReduction
public import DOZZ.Statements.FourPoint.GammaHalfReflectedInnerLimit
public import DOZZ.Statements.FourPoint.DegenerateFourPointDiagonalClassification

/-! The reflected formula follows from the inner limit `DOZZ.gammaHalf_reflected_inner_limit` and
the physical diagonal classification `DOZZ.degenerateFourPoint_diagonal_classification`. -/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The exact reflected formula in the physical frame, with the original reflection data. -/
theorem gammaHalf_reflected_formula {Ω : Type*} [MeasurableSpace Ω]
    {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H)
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
        let a := gaussParameterA γ (γ / 2) α₁ α₂ α₃
        let b := gaussParameterB γ (γ / 2) α₁ α₂ α₃
        let c := gaussParameterC γ (γ / 2) α₁
        ∀ z ∈ gaussCutPlane,
          fourPointT P M γ μ (-γ / 2) α₁ α₂ α₃ z =
            structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ *
                ‖gaussFMinus H a b c z‖ ^ 2 +
              reflectionR P γ μ α₁ (B α₁) Z *
                structureConstant P M γ μ (2 * Q γ - α₁ - γ / 2) α₂ α₃ *
                  ‖gaussFPlus H a b c z‖ ^ 2 := by
  obtain ⟨ξ, hξ, hξ₂, hslack, hfreeze⟩ := hnear
  have hinner := DOZZ.gammaHalf_reflected_inner_limit P M X γ μ α₁ α₂ α₃ ξ
    hγ hγ₂ hμ hα₁ hα₂ hα₃ hs hξ hξ₂ hreflect
    (lt_min (hslack.trans hξ₂) hslack) hfreeze hX hM
  have hclass := DOZZ.degenerateFourPoint_diagonal_classification hH
    P X M γ μ (γ / 2) α₁ α₂ α₃ hγ hγ₂ hμ
    (Or.inl rfl) hα₁ hα₂ hα₃ hs hX hM
  exact gammaHalf_reflected_formula_of_inner_limit hH
    P M X γ μ α₁ α₂ α₃ ξ hγ hγ₂ hμ hα₁ hα₂ hα₃ hs hreflect
    hξ hξ₂ hslack hfreeze hX hM hinner hclass

end DOZZ.Proofs

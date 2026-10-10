/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.ReflectedEnd.FormulaReduction
import Mathlib.Tactic

/-! # The reflected formula directly from the inner-limit and classification conclusions

The inner-limit and BPZ classification conclusions are the only inputs taken as hypotheses.
The outer estimate and every deterministic coefficient-identification step are proved.
-/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The full reflected formula reduces directly to the inner-limit conclusion and
the diagonal-classification conclusion in the same physical frame. -/
theorem gammaHalf_reflected_formula_of_inner_limit {Ω : Type*} [MeasurableSpace Ω]
    {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H)
    (P : Measure Ω) (M : Ω → Measure ℂ) (X : Ω → Distr)
    (γ μ α₁ α₂ α₃ ξ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hμ : 0 < μ)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃)
    (hreflect : Q γ - α₁ < γ / 2)
    (hξ : 0 < ξ) (hξ₂ : ξ < 1) (hslack : γ * (Q γ - α₁) < ξ)
    (hfreeze : γ * (Q γ - α₁) <
      (1 - ξ) * (γ * (Q γ - α₁) + (α₁ + γ / 2 - Q γ) ^ 2 / 2))
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hinner :
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
            IsComplexLittleOAtZero κ r)
    (hclassification :
    let a := gaussParameterA γ (γ / 2) α₁ α₂ α₃
    let b := gaussParameterB γ (γ / 2) α₁ α₂ α₃
    let c := gaussParameterC γ (γ / 2) α₁
    ∀ z ∈ gaussCutPlane,
      fourPointT P M γ μ (-(γ / 2)) α₁ α₂ α₃ z =
        structureConstant P M γ μ (α₁ - (γ / 2)) α₂ α₃ *
          (‖gaussFMinus H a b c z‖ ^ 2 +
            gaussCoefficientRatio a b c *
              ‖gaussFPlus H a b c z‖ ^ 2)) :
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
  have hfusion := gammaHalf_reflected_fusion_asymptotic_of_inner_limit
    P M X γ μ α₁ α₂ α₃ ξ hγ hγ₂ hμ hα₁ hα₂ hα₃ hs hreflect
    hξ hξ₂ hslack hfreeze hX hM hinner
  exact gammaHalf_reflected_formula_of_fusion_and_classification hH
    P M X γ μ α₁ α₂ α₃ hγ hγ₂ hα₁ hα₂ hα₃ hs
    ⟨ξ, hξ, hξ₂, hslack, hfreeze⟩ hfusion hclassification

end DOZZ.Proofs

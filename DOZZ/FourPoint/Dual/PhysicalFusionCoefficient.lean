/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.DiagonalReduction
public import DOZZ.Statements.FourPoint.DegenerateFourPointDiagonalClassification
/-! The physical classification `DOZZ.degenerateFourPoint_diagonal_classification` identifies the
remaining stochastic fusion coefficient. -/
public section
open Filter Topology Set
namespace DOZZ.Proofs

/-- The classification identifies any physical fusion coefficient throughout
the slit plane. The stochastic limit remains explicit; no classification hypothesis remains. -/
theorem dual_physical_fusion_coefficient {Ω : Type*} [MeasurableSpace Ω]
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (P : MeasureTheory.Measure Ω) (X : Ω → Distr) (M : Ω → MeasureTheory.Measure ℂ)
    (γ μ α₁ α₂ α₃ D : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (hμ : 0 < μ)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ + 2 / γ < α₁ + α₂ + α₃)
    (hκ : (4 / γ) * (Q γ - α₁) < 1)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hfusion : Tendsto (fun t : ℝ =>
      (fourPointT P M γ μ (-(2 / γ)) α₁ α₂ α₃ (t : ℂ) -
        structureConstant P M γ μ (α₁ - 2 / γ) α₂ α₃) /
          t ^ ((4 / γ) * (Q γ - α₁))) (nhdsWithin 0 (Ioi 0)) (nhds D)) :
    let a := gaussParameterA γ (2 / γ) α₁ α₂ α₃
    let b := gaussParameterB γ (2 / γ) α₁ α₂ α₃
    let c := gaussParameterC γ (2 / γ) α₁
    D = structureConstant P M γ μ (α₁ - 2 / γ) α₂ α₃ * gaussCoefficientRatio a b c ∧
    ∀ z ∈ gaussCutPlane, fourPointT P M γ μ (-(2 / γ)) α₁ α₂ α₃ z =
      structureConstant P M γ μ (α₁ - 2 / γ) α₂ α₃ * ‖gaussFMinus H a b c z‖ ^ 2 +
        D * ‖gaussFPlus H a b c z‖ ^ 2 := by
  exact dual_physical_classification_reduction hH P M γ μ α₁ α₂ α₃ D hγ hγ₂
    hα₁ hα₂ hα₃ hs hκ
    (DOZZ.degenerateFourPoint_diagonal_classification hH P X M γ μ (2/γ) α₁ α₂ α₃
      hγ hγ₂ hμ (Or.inr rfl) hα₁ hα₂ hα₃ hs hX hM) hfusion

end DOZZ.Proofs

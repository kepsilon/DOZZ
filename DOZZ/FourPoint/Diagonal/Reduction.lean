/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.ThreePointFiniteCorrelation
public import DOZZ.FourPoint.Diagonal.Endpoint
import DOZZ.FourPoint.FourPointTZeroEqStructureConstant
import DOZZ.Hypergeom.ClassificationPhysicalNormalization

/-! Exact reduction of `DOZZ.degenerateFourPoint_diagonal_classification` to the BPZ conclusion.
Continuity at the puncture and the coincident-root value are proved physical inputs, rather
than extra hypotheses on the abstract Gauss PDE solution. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology
namespace DOZZ.Proofs

/-- The literal BPZ conclusion implies the literal diagonal classification.
The complete hypergeometric physical normalization, `real_gauss_solution_physical_normalization`,
supplies nonresonance, connection coefficients and their ratio. Physical continuity at zero and
root fusion identify its coefficient with the three-point constant. -/
theorem degenerateFourPoint_diagonal_classification_of_BPZ {Ω : Type*} [MeasurableSpace Ω]
    {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H)
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ χ α₁ α₂ α₃ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hμ : 0 < μ)
    (hχ : χ = γ / 2 ∨ χ = 2 / γ)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ + χ < α₁ + α₂ + α₃)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hBPZ : IsRealGaussSolution
      (gaussParameterA γ χ α₁ α₂ α₃)
      (gaussParameterB γ χ α₁ α₂ α₃)
      (gaussParameterC γ χ α₁)
      (fun z => fourPointT P M γ μ (-χ) α₁ α₂ α₃ z)) :
    let a := gaussParameterA γ χ α₁ α₂ α₃
    let b := gaussParameterB γ χ α₁ α₂ α₃
    let c := gaussParameterC γ χ α₁
    ∀ z ∈ gaussCutPlane,
      fourPointT P M γ μ (-χ) α₁ α₂ α₃ z =
        structureConstant P M γ μ (α₁ - χ) α₂ α₃ *
          (‖gaussFMinus H a b c z‖ ^ 2 +
            gaussCoefficientRatio a b c *
              ‖gaussFPlus H a b c z‖ ^ 2) := by
  have hχpos : 0 < χ := by
    rcases hχ with rfl | rfl
    · exact div_pos hγ (by norm_num)
    · exact div_pos (by norm_num) hγ
  have hcont := fourPointT_continuousAt_zero P X M γ μ χ α₁ α₂ α₃
    hγ hγ₂ hχpos hα₁ hα₂ hα₃ hs hX hM
  have hnorm := real_gauss_solution_physical_normalization hH γ χ α₁ α₂ α₃
    hγ hγ₂ hχ hs hα₁ hα₂ hα₃
    (fun z => fourPointT P M γ μ (-χ) α₁ α₂ α₃ z) hBPZ hcont
  rw [fourPointT_zero_eq_structureConstant P X M γ μ χ α₁ α₂ α₃ hγ hγ₂ hμ
    (by linarith) hα₂ hα₃ (by linarith) hX hM] at hnorm
  exact hnorm

end DOZZ.Proofs

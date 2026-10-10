/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.ThreePointFiniteCorrelation
import DOZZ.FourPoint.Diagonal.Assembly

/-! The statement `DOZZ.degenerateFourPoint_diagonal_classification`,
proved by `DOZZ.Proofs.degenerateFourPoint_diagonal_classification`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The normalized physical solution has the diagonal Gauss representation with its coefficient
fixed by `T(0) = C`. The physical charge domain supplies nonresonance and nonzero `K₂` (see
`DOZZ.gauss_physical_parameter_range` and `DOZZ.real_gauss_solution_physical_normalization`); the
general classification retains the guard `K₂ ≠ 0` (erratum K27, see
docs/ERRATA-AND-DEVIATIONS.md). -/
theorem degenerateFourPoint_diagonal_classification {Ω : Type*} [MeasurableSpace Ω]
    {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H)
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ χ α₁ α₂ α₃ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hμ : 0 < μ)
    (hχ : χ = γ / 2 ∨ χ = 2 / γ)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ + χ < α₁ + α₂ + α₃)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    let a := gaussParameterA γ χ α₁ α₂ α₃
    let b := gaussParameterB γ χ α₁ α₂ α₃
    let c := gaussParameterC γ χ α₁
    ∀ z ∈ gaussCutPlane,
      fourPointT P M γ μ (-χ) α₁ α₂ α₃ z =
        structureConstant P M γ μ (α₁ - χ) α₂ α₃ *
          (‖gaussFMinus H a b c z‖ ^ 2 +
            gaussCoefficientRatio a b c *
              ‖gaussFPlus H a b c z‖ ^ 2) := by exact DOZZ.Proofs.degenerateFourPoint_diagonal_classification hH P X M γ μ χ α₁ α₂ α₃ hγ hγ₂ hμ hχ hα₁ hα₂ hα₃ hs hX hM

end DOZZ

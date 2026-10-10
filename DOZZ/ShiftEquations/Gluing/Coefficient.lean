/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Gluing.DiagonalUnique
public import DOZZ.Statements.FourPoint.FourPointT
public import DOZZ.Statements.Defs.StructureConstant
public import DOZZ.Statements.Hypergeom.GaussCoefficientRatio
public import DOZZ.Statements.Hypergeom.GaussParameterA
public import DOZZ.Statements.Hypergeom.GaussParameterB
public import DOZZ.Statements.Hypergeom.GaussParameterC

/-!
# The reflected coefficient from two diagonal representations

At charges where both the normalized classification
(`DOZZ.degenerateFourPoint_diagonal_classification`) and a diagonal formula with a second
coefficient `K` hold on the cut plane, uniqueness of diagonal Gauss representations identifies
`K = C(α₁ - χ, α₂, α₃) ρ(a, b, c)`, with `ρ` the Gauss coefficient ratio.
-/

@[expose] public section

open MeasureTheory

namespace DOZZ.Proofs

/-- `c ∉ ℤ` for `0 < c < 1`. -/
theorem complex_ne_int_of_mem_unit {c : ℝ} (h0 : 0 < c) (h1 : c < 1) :
    ∀ n : ℤ, (c : ℂ) ≠ (n : ℂ) := by
  intro n hn
  have hcn : c = n := by exact_mod_cast hn
  have h0' : (0 : ℤ) < n := by exact_mod_cast (hcn ▸ h0)
  have h1' : n < 1 := by exact_mod_cast (hcn ▸ h1)
  omega

/-- **The second diagonal coefficient is fixed by the classification.** -/
theorem second_coefficient_of_classification {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : Ω → Measure ℂ) {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (γ μ χ α₁ α₂ α₃ K : ℝ)
    (hc : ∀ n : ℤ, (gaussParameterC γ χ α₁ : ℂ) ≠ (n : ℂ))
    (h22 : ∀ z ∈ gaussCutPlane, fourPointT P M γ μ (-χ) α₁ α₂ α₃ z =
      structureConstant P M γ μ (α₁ - χ) α₂ α₃ *
        (‖gaussFMinus H (gaussParameterA γ χ α₁ α₂ α₃) (gaussParameterB γ χ α₁ α₂ α₃)
            (gaussParameterC γ χ α₁) z‖ ^ 2 +
          gaussCoefficientRatio (gaussParameterA γ χ α₁ α₂ α₃) (gaussParameterB γ χ α₁ α₂ α₃)
              (gaussParameterC γ χ α₁) *
            ‖gaussFPlus H (gaussParameterA γ χ α₁ α₂ α₃) (gaussParameterB γ χ α₁ α₂ α₃)
              (gaussParameterC γ χ α₁) z‖ ^ 2))
    (hform : ∀ z ∈ gaussCutPlane, fourPointT P M γ μ (-χ) α₁ α₂ α₃ z =
      structureConstant P M γ μ (α₁ - χ) α₂ α₃ *
          ‖gaussFMinus H (gaussParameterA γ χ α₁ α₂ α₃) (gaussParameterB γ χ α₁ α₂ α₃)
            (gaussParameterC γ χ α₁) z‖ ^ 2 +
        K * ‖gaussFPlus H (gaussParameterA γ χ α₁ α₂ α₃) (gaussParameterB γ χ α₁ α₂ α₃)
            (gaussParameterC γ χ α₁) z‖ ^ 2) :
    K = gaussCoefficientRatio (gaussParameterA γ χ α₁ α₂ α₃) (gaussParameterB γ χ α₁ α₂ α₃)
        (gaussParameterC γ χ α₁) * structureConstant P M γ μ (α₁ - χ) α₂ α₃ := by
  have h := diagonal_gauss_coefficients_unique hH hc (T := fourPointT P M γ μ (-χ) α₁ α₂ α₃)
    (A₁ := structureConstant P M γ μ (α₁ - χ) α₂ α₃) (A₂ := structureConstant P M γ μ (α₁ - χ) α₂ α₃)
    (D₁ := K) (D₂ := structureConstant P M γ μ (α₁ - χ) α₂ α₃ *
      gaussCoefficientRatio (gaussParameterA γ χ α₁ α₂ α₃) (gaussParameterB γ χ α₁ α₂ α₃)
        (gaussParameterC γ χ α₁)) hform (fun z hz => by rw [h22 z hz]; ring)
  rw [h.2]
  ring

end DOZZ.Proofs

end

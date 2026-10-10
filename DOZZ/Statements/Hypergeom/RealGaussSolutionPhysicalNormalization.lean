/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.GaussParameterC
import DOZZ.Hypergeom.ClassificationPhysicalNormalization

/-! The statement `DOZZ.real_gauss_solution_physical_normalization`,
proved by `DOZZ.Proofs.real_gauss_solution_physical_normalization`. -/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- Endpoint normalization [KRV, (Fundrelation1)] on the physical range of [KRV, §4.3]. The strict
physical bounds supply all nonresonance and Gamma finiteness conditions. Continuity at the puncture
identifies the coefficient with T(0); no value of an arbitrary PDE solution at the excluded point is
read without this hypothesis. -/
theorem real_gauss_solution_physical_normalization {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) (γ χ α₁ α₂ α₃ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hχ : χ = γ / 2 ∨ χ = 2 / γ)
    (hsum : 2 * Q γ + χ < α₁ + α₂ + α₃)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (T : ℂ → ℝ)
    (hT : IsRealGaussSolution (gaussParameterA γ χ α₁ α₂ α₃)
      (gaussParameterB γ χ α₁ α₂ α₃) (gaussParameterC γ χ α₁) T)
    (hcont : ContinuousAt T 0) :
    ∀ z ∈ gaussCutPlane,
      T z = T 0 *
        (‖gaussFMinus H (gaussParameterA γ χ α₁ α₂ α₃)
          (gaussParameterB γ χ α₁ α₂ α₃) (gaussParameterC γ χ α₁) z‖ ^ 2 +
        gaussCoefficientRatio (gaussParameterA γ χ α₁ α₂ α₃)
          (gaussParameterB γ χ α₁ α₂ α₃) (gaussParameterC γ χ α₁) *
          ‖gaussFPlus H (gaussParameterA γ χ α₁ α₂ α₃)
            (gaussParameterB γ χ α₁ α₂ α₃) (gaussParameterC γ χ α₁) z‖ ^ 2) := by exact DOZZ.Proofs.real_gauss_solution_physical_normalization hH γ χ α₁ α₂ α₃ hγ hγ₂ hχ hsum hα₁ hα₂ hα₃ T hT hcont

end DOZZ

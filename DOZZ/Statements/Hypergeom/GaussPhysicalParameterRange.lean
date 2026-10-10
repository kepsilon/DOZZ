/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.GaussParameterC
import DOZZ.Hypergeom.PhysicalRange

/-! The statement `DOZZ.gauss_physical_parameter_range`,
proved by `DOZZ.Proofs.gauss_physical_parameter_range`. -/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- The strict four-point Seiberg range of [KRV, §4.3]. In this range [KRV, (Fundrelation)] has no
junk Gamma factors and both undivided coefficients are positive. -/
theorem gauss_physical_parameter_range (γ χ α₁ α₂ α₃ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hχ : χ = γ / 2 ∨ χ = 2 / γ)
    (hsum : 2 * Q γ + χ < α₁ + α₂ + α₃)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) :
    0 < gaussParameterA γ χ α₁ α₂ α₃ ∧
      gaussParameterA γ χ α₁ α₂ α₃ < gaussParameterB γ χ α₁ α₂ α₃ ∧
      gaussParameterB γ χ α₁ α₂ α₃ < gaussParameterC γ χ α₁ ∧
      gaussParameterC γ χ α₁ < 1 ∧
      0 < gaussParameterC γ χ α₁ - gaussParameterA γ χ α₁ α₂ α₃ -
        gaussParameterB γ χ α₁ α₂ α₃ ∧
      gaussParameterC γ χ α₁ - gaussParameterA γ χ α₁ α₂ α₃ -
        gaussParameterB γ χ α₁ α₂ α₃ < 1 ∧
      0 < gaussK₁ (gaussParameterA γ χ α₁ α₂ α₃)
        (gaussParameterB γ χ α₁ α₂ α₃) (gaussParameterC γ χ α₁) ∧
      0 < gaussK₂ (gaussParameterA γ χ α₁ α₂ α₃)
        (gaussParameterB γ χ α₁ α₂ α₃) (gaussParameterC γ χ α₁) := by exact DOZZ.Proofs.gauss_physical_parameter_range γ χ α₁ α₂ α₃ hγ hγ₂ hχ hsum hα₁ hα₂ hα₃

end DOZZ

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
import DOZZ.DOZZAlgebra.FormulaReflection

/-! The statement `DOZZ.dozzFormula_reflection`, proved by `DOZZ.Proofs.dozzFormula_reflection`. -/

public section

open Complex MeasureTheory Set Filter Topology

namespace DOZZ

/-- Reflection relation `C^{DOZZ}(α₁,α₂,α₃) = R^{DOZZ}(α₁) C^{DOZZ}(2Q-α₁,α₂,α₃)`
([KRV, (rrel1)]). -/
theorem dozzFormula_reflection {γ : ℝ} {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2) {μ : ℝ} (hμ : 0 < μ)
    (hU : IsUpsilon γ U) (α₂ α₃ : ℂ) :
    ∀ᶠ α₁ in codiscrete ℂ,
      dozzFormula γ μ U α₁ α₂ α₃ =
        reflectionDOZZ γ μ α₁ * dozzFormula γ μ U (2 * Q γ - α₁) α₂ α₃ := by exact DOZZ.Proofs.dozzFormula_reflection hγ hγ2 hμ hU α₂ α₃

end DOZZ

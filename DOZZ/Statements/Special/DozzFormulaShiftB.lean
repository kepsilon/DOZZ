/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
import DOZZ.DOZZAlgebra.FormulaShiftB

/-! The statement `DOZZ.dozzFormula_shift_b`, proved by `DOZZ.Proofs.dozzFormula_shift_b`. -/

public section

open Complex MeasureTheory Set Filter Topology

namespace DOZZ

/-- `C^{DOZZ}` satisfies the `γ/2` shift ([KRV, (3pointconstanteqintro)]). -/
theorem dozzFormula_shift_b {γ : ℝ} {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2) {μ : ℝ} (hμ : 0 < μ)
    (hU : IsUpsilon γ U) (α₂ α₃ : ℂ) :
    ∀ᶠ α₁ in codiscrete ℂ,
      dozzFormula γ μ U (α₁ + γ / 2) α₂ α₃ =
        -(1 / (Real.pi * μ)) * shiftCoeffA γ (γ / 2) α₁ α₂ α₃ *
          dozzFormula γ μ U (α₁ - γ / 2) α₂ α₃ := by exact DOZZ.Proofs.dozzFormula_shift_b hγ hγ2 hμ hU α₂ α₃

end DOZZ

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
import DOZZ.DOZZAlgebra.FormulaShiftBinv

/-! The statement `DOZZ.dozzFormula_shift_binv`, proved by `DOZZ.Proofs.dozzFormula_shift_binv`. -/

public section

open Complex MeasureTheory Set Filter Topology

namespace DOZZ

/-- `C^{DOZZ}` satisfies the dual `2/γ` shift ([KRV, (3pointconstanteqintrodual)]). The printed
coefficient `μ̃` is singular when `4/γ² ∈ ℕ`; those `γ` are excluded. -/
theorem dozzFormula_shift_binv {γ : ℝ} {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hγk : ∀ k : ℕ, 4 / γ ^ 2 ≠ (k : ℝ)) {μ : ℝ} (hμ : 0 < μ)
    (hU : IsUpsilon γ U) (α₂ α₃ : ℂ) :
    ∀ᶠ α₁ in codiscrete ℂ,
      dozzFormula γ μ U (α₁ + 2 / γ) α₂ α₃ =
        -(1 / (Real.pi * dualMu γ μ)) * shiftCoeffA γ (2 / γ) α₁ α₂ α₃ *
          dozzFormula γ μ U (α₁ - 2 / γ) α₂ α₃ := by exact DOZZ.Proofs.dozzFormula_shift_binv hγ hγ2 hγk hμ hU α₂ α₃

end DOZZ

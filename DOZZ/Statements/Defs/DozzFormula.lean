/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DozzBase

/-! The definition `DOZZ.dozzFormula`. -/

@[expose] public section

open Complex MeasureTheory Set Filter Topology

namespace DOZZ

/-- The DOZZ formula `C_γ^{DOZZ}` ([KRV, (DOZZformula)]), built from a given `Υ_{γ/2} = U`;
`ᾱ = α₁ + α₂ + α₃`. -/
noncomputable def dozzFormula (γ μ : ℝ) (U : ℂ → ℂ) (α₁ α₂ α₃ : ℂ) : ℂ :=
  ((dozzBase γ μ * (γ / 2) ^ (2 - γ ^ 2 / 2) : ℝ) : ℂ) ^ ((2 * Q γ - (α₁ + α₂ + α₃)) / γ) *
    (deriv U 0 * U α₁ * U α₂ * U α₃) /
    (U ((α₁ + α₂ + α₃ - 2 * Q γ) / 2) * U ((α₁ + α₂ + α₃) / 2 - α₁) *
      U ((α₁ + α₂ + α₃) / 2 - α₂) * U ((α₁ + α₂ + α₃) / 2 - α₃))

end DOZZ

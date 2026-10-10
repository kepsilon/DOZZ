/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.ExtendedSeiberg3

/-! The definition `DOZZ.shiftCoeffA`. -/

@[expose] public section

open Complex MeasureTheory Set Filter Topology

namespace DOZZ

/-- `𝒜_γ(χ, α₁, α₂, α₃)` ([KRV, (Aformula)]), `ᾱ = α₁ + α₂ + α₃`. -/
noncomputable def shiftCoeffA (γ : ℝ) (χ α₁ α₂ α₃ : ℂ) : ℂ :=
  lFun (-χ ^ 2) * lFun (χ * α₁) * lFun (χ * α₁ - χ ^ 2) *
      lFun (χ / 2 * ((α₁ + α₂ + α₃) - 2 * α₁ - χ)) /
    (lFun (χ / 2 * ((α₁ + α₂ + α₃) - χ - 2 * Q γ)) * lFun (χ / 2 * ((α₁ + α₂ + α₃) - 2 * α₃ - χ)) *
      lFun (χ / 2 * ((α₁ + α₂ + α₃) - 2 * α₂ - χ)))

end DOZZ

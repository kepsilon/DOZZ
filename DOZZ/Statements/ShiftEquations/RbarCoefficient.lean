/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.ShiftEquations.MobiusMap

/-! The definition `DOZZ.rbarCoefficient`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The coefficient of [KRV, (formulaforbarR)] with the corrected constant `+2π/γ` (erratum K29, see
docs/ERRATA-AND-DEVIATIONS.md); the printed `−π/γ` is off by a factor of `−2` and would force
`Rbar ≤ 0`. -/
noncomputable def rbarCoefficient (γ : ℝ) (z : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) / γ) *
    lFun ((γ : ℂ) / 2 * z - (γ : ℂ) ^ 2 / 4 - 1) /
      (lFun (1 + (γ : ℂ) / 2 * (z - (Q γ : ℂ))) *
        lFun (-((γ : ℂ) ^ 2) / 4) * lFun ((γ : ℂ) ^ 2 / 4))

end DOZZ

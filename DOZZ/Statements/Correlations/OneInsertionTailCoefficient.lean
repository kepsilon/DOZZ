/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Correlations.OneInsertionErrorCeiling

/-! The definition `DOZZ.oneInsertionTailCoefficient`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The exact coefficient in the one-insertion tail of [KRV, Lemma 7.1] (erratum K17, see
docs/ERRATA-AND-DEVIATIONS.md): the domain has `‖z‖ ≥ 2`, so the background factor is `‖z‖`, not
`normPlus z`. -/
noncomputable def oneInsertionTailCoefficient (γ α : ℝ) (z : ℂ)
    (Fz Rbar : ℝ) : ℝ :=
  Real.rpow ‖z‖ (-4 * α * (Q γ - α)) *
    Real.rpow Fz (reflectionExponent γ α) * Rbar

end DOZZ

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GFFStructure.ExteriorPinnedEvaluation

/-! The definition `DOZZ.equatorRestorationScalar`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

universe u

namespace DOZZ

/-- Correlated equator-restoration scalar `L = m₁(Y)`, used in
`DOZZ.exists_exteriorPinned_markov_uniform`. -/
noncomputable def equatorRestorationScalar {Ω : Type*}
    (Xc : Ω → ℂ → ℝ → ℝ) (R : ℝ) (_hR : 0 < R) (ω : Ω) : ℝ :=
  Xc ω 0 0 - Xc ω 0 (-Real.log R)

end DOZZ

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GFFStructure.CircleLogPotential

/-! The definition `DOZZ.exteriorPinnedEvaluation`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

universe u

namespace DOZZ

/-- Evaluation of `Y = X - m_R(X)` for the exterior-pinned Markov decomposition
`DOZZ.exists_exteriorPinned_markov_uniform` (see [KRV, Lemma 7.3]). -/
noncomputable def exteriorPinnedEvaluation {Ω : Type*} (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (R : ℝ) (_hR : 0 < R) (ω : Ω) (f : TestFn) : ℝ :=
  X ω f - Xc ω 0 (-Real.log R) * (∫ x : ℂ, f x)

end DOZZ

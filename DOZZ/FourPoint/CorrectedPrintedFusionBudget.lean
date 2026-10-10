/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.FourFusionMass

/-! The corrected disk-moment budget (erratum K21, see docs/ERRATA-AND-DEVIATIONS.md), including
the equality endpoint. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- The printed order `q = p + 2` has nonnegative disk-moment budget exactly when `Q ≤ 2γ`,
equivalently `γ² ≥ 4/3`, including equality (erratum K21, see docs/ERRATA-AND-DEVIATIONS.md). -/
theorem corrected_printed_fusion_budget (γ : ℝ) (hγ : 0 < γ) :
    (0 ≤ 2 - Q γ / γ) ↔ Q γ ≤ 2 * γ ∧ 4 / 3 ≤ γ ^ 2 := by
  have hQγ : Q γ * γ = 2 + γ ^ 2 / 2 := by
    unfold Q
    field_simp
  constructor
  · intro h
    have hQ : Q γ ≤ 2 * γ := (div_le_iff₀ hγ).mp (by linarith only [h])
    refine ⟨hQ, ?_⟩
    have hmul := mul_le_mul_of_nonneg_right hQ hγ.le
    rw [hQγ] at hmul
    nlinarith only [hmul]
  · rintro ⟨hQ, _⟩
    have hdiv : Q γ / γ ≤ 2 := (div_le_iff₀ hγ).mpr hQ
    linarith only [hdiv]

end DOZZ.Proofs

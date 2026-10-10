/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.GaussPhysicalParameterRange
import Mathlib.Tactic

/-! # Strict dual charge domains

The open simplex of dual seed charges and the explicit near-Q window. These are consequences of
the literal premises.
-/

public section

namespace DOZZ.Proofs


/-- Each charge lies strictly above the dual degenerate charge. -/
theorem dual_seed_charge_lower (γ α ε α' : ℝ)
    (hα : α < Q γ) (hε : ε < Q γ) (hα' : α' < Q γ)
    (hs : 2 * Q γ + 2 / γ < α + ε + α') :
    2 / γ < α ∧ 2 / γ < ε ∧ 2 / γ < α' := by
  constructor
  · linarith only [hs, hε, hα']
  constructor
  · linarith only [hs, hα, hα']
  · linarith only [hs, hα, hε]


end DOZZ.Proofs

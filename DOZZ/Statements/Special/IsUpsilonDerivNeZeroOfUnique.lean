/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
import DOZZ.Upsilon.ZeroStructure

/-! The statement `DOZZ.IsUpsilon.deriv_ne_zero_of_unique`,
proved by `DOZZ.Proofs.IsUpsilon.deriv_ne_zero_of_unique`. -/

public section

open Complex MeasureTheory Set Filter Topology

namespace DOZZ

/-- Simple zeros at uniquely represented points, for every `γ`. -/
theorem IsUpsilon.deriv_ne_zero_of_unique {γ : ℝ} {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hU : IsUpsilon γ U) (m n : ℕ)
    (huniq : ∀ m' n' : ℕ, (m' : ℝ) * (γ / 2) + n' * (2 / γ) = m * (γ / 2) + n * (2 / γ) →
      m' = m ∧ n' = n) :
    deriv U (-(m * (γ / 2) + n * (2 / γ) : ℝ)) ≠ 0 := by exact DOZZ.Proofs.IsUpsilon.deriv_ne_zero_of_unique hγ hγ2 hU m n huniq

end DOZZ

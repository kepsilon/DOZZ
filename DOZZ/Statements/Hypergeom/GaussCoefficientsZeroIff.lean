/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.GaussCoefficientRatio
import DOZZ.Hypergeom.CoefficientZeros

/-! The statement `DOZZ.gauss_coefficients_zero_iff`,
proved by `DOZZ.Proofs.gauss_coefficients_zero_iff`. -/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- Exact degeneracy of the coefficients `K₁`, `K₂` of [KRV-local, Lemma 4.4] (a helper not used in
the proofs of the main theorems). The Γ numerator factors are finite and nonzero under `c ∉ ℤ`. -/
theorem gauss_coefficients_zero_iff (a b c : ℝ) (hc : ∀ n : ℤ, c ≠ (n : ℝ)) :
    (gaussK₁ a b c = 0 ↔ ∃ n : ℕ,
      a = -(n : ℝ) ∨ b = -(n : ℝ) ∨ c - a = -(n : ℝ) ∨ c - b = -(n : ℝ)) ∧
    (gaussK₂ a b c = 0 ↔ ∃ n : ℕ,
      a = (n : ℝ) + 1 ∨ b = (n : ℝ) + 1 ∨
        c - a = (n : ℝ) + 1 ∨ c - b = (n : ℝ) + 1) := by exact DOZZ.Proofs.gauss_coefficients_zero_iff a b c hc

end DOZZ

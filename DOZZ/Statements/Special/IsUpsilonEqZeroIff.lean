/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
import DOZZ.Upsilon.ZeroStructure

/-! The statement `DOZZ.IsUpsilon.eq_zero_iff`, proved by `DOZZ.Proofs.IsUpsilon.eq_zero_iff`. -/

public section

open Complex MeasureTheory Set Filter Topology

namespace DOZZ

/-- Zero set ([KRV, §12.5]): `Υ(z) = 0` iff `z = -m γ/2 - n 2/γ` or `z = Q + m γ/2 + n 2/γ`. -/
theorem IsUpsilon.eq_zero_iff {γ : ℝ} {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2) (hU : IsUpsilon γ U)
    (z : ℂ) :
    U z = 0 ↔ ∃ m n : ℕ, z = -(m * (γ / 2) + n * (2 / γ) : ℝ) ∨
      z = (Q γ + m * (γ / 2) + n * (2 / γ) : ℝ) := by exact DOZZ.Proofs.IsUpsilon.eq_zero_iff hγ hγ2 hU z

end DOZZ

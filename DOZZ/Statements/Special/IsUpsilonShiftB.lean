/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
import DOZZ.Upsilon.FullShifts

/-! The statement `DOZZ.IsUpsilon.shift_b`, proved by `DOZZ.Proofs.IsUpsilon.shift_b`. -/

public section

open Complex MeasureTheory Set Filter Topology

namespace DOZZ

/-- First shift ([KRV, (shiftUpsilon)]), away from the poles of `Γ(γz/2)`. -/
theorem IsUpsilon.shift_b {γ : ℝ} {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2) (hU : IsUpsilon γ U)
    (z : ℂ) (hz : ∀ n : ℕ, (γ / 2 : ℂ) * z ≠ -(n : ℂ)) :
    U (z + γ / 2) = lFun (γ / 2 * z) * ((γ / 2 : ℝ) : ℂ) ^ (1 - γ * z) * U z := by exact DOZZ.Proofs.IsUpsilon.shift_b hγ hγ2 hU z hz

end DOZZ

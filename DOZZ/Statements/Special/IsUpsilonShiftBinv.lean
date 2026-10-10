/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
import DOZZ.Upsilon.FullShifts

/-! The statement `DOZZ.IsUpsilon.shift_binv`, proved by `DOZZ.Proofs.IsUpsilon.shift_binv`. -/

public section

open Complex MeasureTheory Set Filter Topology

namespace DOZZ

/-- Second shift ([KRV, (shiftUpsilon)]), away from the poles of `Γ(2z/γ)`. -/
theorem IsUpsilon.shift_binv {γ : ℝ} {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2) (hU : IsUpsilon γ U)
    (z : ℂ) (hz : ∀ n : ℕ, (2 / γ : ℂ) * z ≠ -(n : ℂ)) :
    U (z + 2 / γ) = lFun (2 / γ * z) * ((γ / 2 : ℝ) : ℂ) ^ (4 / γ * z - 1) * U z := by exact DOZZ.Proofs.IsUpsilon.shift_binv hγ hγ2 hU z hz

end DOZZ

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
import DOZZ.Upsilon.ZeroStructure

/-! The statement `DOZZ.IsUpsilon.deriv_zero`, proved by `DOZZ.Proofs.IsUpsilon.deriv_zero`. -/

public section

open Complex MeasureTheory Set Filter Topology

namespace DOZZ

/-- `Υ'(0) = Υ(γ/2)` (z → 0 in [KRV, (shiftUpsilon)]); hence `Υ'(0) ≠ 0` for every `γ`. -/
theorem IsUpsilon.deriv_zero {γ : ℝ} {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2) (hU : IsUpsilon γ U) :
    deriv U 0 = U (γ / 2) := by exact DOZZ.Proofs.IsUpsilon.deriv_zero hγ hγ2 hU

end DOZZ

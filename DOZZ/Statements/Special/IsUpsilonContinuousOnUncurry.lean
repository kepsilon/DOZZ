/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
import DOZZ.Upsilon.JointContinuity

/-! The statement `DOZZ.IsUpsilon.continuousOn_uncurry`,
proved by `DOZZ.Proofs.IsUpsilon.continuousOn_uncurry`. -/

public section

open Complex MeasureTheory Set Filter Topology

namespace DOZZ

/-- Joint continuity of `Υ_{γ/2}(z)` in `(γ, z)` (see the continuity arguments in [KRV, §10.6]
and [KRV, §11]). -/
theorem IsUpsilon.continuousOn_uncurry {U : ℝ → ℂ → ℂ}
    (hU : ∀ γ ∈ Ioo (0 : ℝ) 2, IsUpsilon γ (U γ)) :
    ContinuousOn (Function.uncurry U) (Ioo 0 2 ×ˢ univ) := by exact DOZZ.Proofs.IsUpsilon.continuousOn_uncurry hU

end DOZZ

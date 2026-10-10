/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
import DOZZ.Upsilon.ZeroStructure

/-! The statement `DOZZ.IsUpsilon.deriv_ne_zero_of_irrational`,
proved by `DOZZ.Proofs.IsUpsilon.deriv_ne_zero_of_irrational`. -/

public section

open Complex MeasureTheory Set Filter Topology

namespace DOZZ

/-- Zeros are simple when `γ²` is irrational ([KRV, §12.5]). -/
theorem IsUpsilon.deriv_ne_zero_of_irrational {γ : ℝ} {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hU : IsUpsilon γ U) (hirr : Irrational (γ ^ 2)) (z : ℂ) (hz : U z = 0) :
    deriv U z ≠ 0 := by exact DOZZ.Proofs.IsUpsilon.deriv_ne_zero_of_irrational hγ hγ2 hU hirr z hz

end DOZZ

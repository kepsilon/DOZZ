/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
import DOZZ.Upsilon.Uniqueness

/-! The statement `DOZZ.IsUpsilon.reflect`, proved by `DOZZ.Proofs.IsUpsilon.reflect`. -/

public section

open Complex MeasureTheory Set Filter Topology

namespace DOZZ

/-- Reflection symmetry `Υ(Q - z) = Υ(z)`. -/
theorem IsUpsilon.reflect {γ : ℝ} {U : ℂ → ℂ} (hγ : 0 < γ) (hγ2 : γ < 2) (hU : IsUpsilon γ U) (z : ℂ) :
    U (Q γ - z) = U z := by exact DOZZ.Proofs.IsUpsilon.reflect hγ hγ2 hU z

end DOZZ

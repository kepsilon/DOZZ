/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
import DOZZ.Upsilon.Uniqueness

/-! The statement `DOZZ.IsUpsilon.unique`, proved by `DOZZ.Proofs.IsUpsilon.unique`. -/

public section

open Complex MeasureTheory Set Filter Topology

namespace DOZZ

/-- Uniqueness of `Υ_{γ/2}` (identity theorem on the strip). -/
theorem IsUpsilon.unique {γ : ℝ} {U V : ℂ → ℂ} (hγ : 0 < γ) (hU : IsUpsilon γ U) (hV : IsUpsilon γ V) :
    U = V := by exact DOZZ.Proofs.IsUpsilon.unique hγ hU hV

end DOZZ

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.GaussCutPlane

/-! The definition `DOZZ.gaussRegularPlane`. -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- The regular PDE domain, see [KRV, (Tsolution)] and [KRV-local, Lemma 4.4]. -/
def gaussRegularPlane : Set ℂ := {z | z ≠ 0 ∧ z ≠ 1}

end DOZZ

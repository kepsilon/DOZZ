/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.WirtingerZ

/-! The definition `DOZZ.IsRealGaussSolution`. -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- Real, single-valued C² solutions of the normalized Gauss PDE [KRV, (hypergeo)], see
[KRV, (Tsolution)] and [KRV-local, Lemma 4.4]; the codomain is restricted to ℝ. -/
def IsRealGaussSolution (a b c : ℝ) (T : ℂ → ℝ) : Prop :=
  ContDiffOn ℝ 2 T gaussRegularPlane ∧
    ∀ z ∈ gaussRegularPlane,
      wirtingerZ (wirtingerZ (fun w => (T w : ℂ))) z +
        ((c : ℂ) - z * ((a : ℂ) + b + 1)) / (z * (1 - z)) *
          wirtingerZ (fun w => (T w : ℂ)) z -
        (a : ℂ) * b / (z * (1 - z)) * (T z : ℂ) = 0

end DOZZ

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.GaussGPlus

/-! The definition `DOZZ.gaussHolomorphicOperator`. -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- The Gauss holomorphic differential operator, [KRV, (hypergeo)]. -/
noncomputable def gaussHolomorphicOperator (a b c : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  z * (1 - z) * deriv (deriv f) z + (c - (a + b + 1) * z) * deriv f z - a * b * f z

end DOZZ

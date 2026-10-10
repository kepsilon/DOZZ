/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.GaussHolomorphicOperator

/-! The definition `DOZZ.wirtingerZ`. -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- Literal ∂z = (∂x−i∂y)/2, using the real Fréchet derivative, as in [KRV, (hypergeo)] and
[KRV-local, Lemma 4.4]. Applied only on C² open domains. -/
noncomputable def wirtingerZ (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (fderiv ℝ f z 1 - Complex.I * fderiv ℝ f z Complex.I) / 2

end DOZZ

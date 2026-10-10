/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.GaussRegularPlane

/-! The definition `DOZZ.IsGaussHypergeometric`. -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- Predicate characterization of the principal Gauss continuation [KRV, (Fpmdef)]: holomorphic on
the slit and equal to the series on the open unit disk. Off-slit values are unconstrained. -/
def IsGaussHypergeometric (a b c : ℂ) (F : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ F gaussSlitPlane ∧
    ∀ z : ℂ, ‖z‖ < 1 → F z = ordinaryHypergeometric a b c z

end DOZZ

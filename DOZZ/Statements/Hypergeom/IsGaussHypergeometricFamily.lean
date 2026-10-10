/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.IsGaussHypergeometric

/-! The definition `DOZZ.IsGaussHypergeometricFamily`. -/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- The parameterized Gauss hypergeometric function, characterized separately at every denominator
parameter away from nonpositive integers. No connection/PDE/classification result is a field. -/
def IsGaussHypergeometricFamily (H : ℂ → ℂ → ℂ → ℂ → ℂ) : Prop :=
  ∀ a b c : ℂ, (∀ n : ℕ, c ≠ -(n : ℂ)) → IsGaussHypergeometric a b c (H a b c)

end DOZZ

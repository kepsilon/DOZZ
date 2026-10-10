/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.UpsilonLog

/-! The definition `DOZZ.IsUpsilon`. -/

@[expose] public section

open Complex MeasureTheory Set Filter Topology

namespace DOZZ

/-- `U` is the function `Υ_{γ/2}` of [KRV, (def:upsilon)]: entire, and equal to
`exp (upsilonLog γ z)` on the strip `0 < Re z < Q`. (Uniqueness is the identity theorem;
existence is part of `dozz_existence`.) -/
def IsUpsilon (γ : ℝ) (U : ℂ → ℂ) : Prop :=
  Differentiable ℂ U ∧
    ∀ z : ℂ, 0 < z.re → z.re < Q γ → U z = Complex.exp (upsilonLog γ z)

end DOZZ

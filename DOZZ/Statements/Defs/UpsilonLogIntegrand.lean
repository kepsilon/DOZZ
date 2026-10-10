/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.LFun

/-! The definition `DOZZ.upsilonLogIntegrand`. -/

@[expose] public section

open Complex MeasureTheory Set Filter Topology

namespace DOZZ

/-- The integrand of `ln Υ_{γ/2}(z)` in [KRV, (def:upsilon)], as a function of `t > 0`. -/
noncomputable def upsilonLogIntegrand (γ : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  ((Q γ / 2 - z) ^ 2 * Real.exp (-t)
    - Complex.sinh ((Q γ / 2 - z) * (t / 2)) ^ 2
      / (Real.sinh (t * γ / 4) * Real.sinh (t / γ))) / t

end DOZZ

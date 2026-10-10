/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.IsCircleAverage

/-! The definition `DOZZ.regularizedGMC`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- The regularized chaos `e^{γ X_r(x) − γ² E[X_r(x)²]/2} |x|_+^{-4} d²x` ([KRV, (Meps1)]). -/
noncomputable def regularizedGMC {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Xc : Ω → ℂ → ℝ → ℝ) (γ r : ℝ) (ω : Ω) : Measure ℂ :=
  volume.withDensity fun x =>
    ENNReal.ofReal (Real.exp (γ * Xc ω x r - γ ^ 2 / 2 * ∫ ω', Xc ω' x r ^ 2 ∂P)
      * normPlus x ^ (-4 : ℝ))

end DOZZ

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.IsLateralGMCOf

/-!
# First moments of lateral GMC intervals

The lateral carrier `DOZZ.IsLateralGMCOf` already specifies its intensity. This file extracts the
exact interval mean and the corresponding uniform moment bound at order one; higher and negative
orders require the subcritical chaos estimates.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace DOZZ.Proofs

/-- Every lateral GMC interval has the exact intensity prescribed by its carrier. -/
theorem lateralGMC_interval_first_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (a b : ℝ) (hab : a < b) :
    ∫⁻ ω, Z ω (Set.Ioc a b) ∂P = ENNReal.ofReal (2 * Real.pi * (b - a)) := by
  rcases hZ with ⟨_, _, _, _, _, _, _, hinterval, _⟩
  exact hinterval a b hab


end DOZZ.Proofs

end

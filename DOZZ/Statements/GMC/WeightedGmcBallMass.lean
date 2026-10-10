/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.GmcMassMoment

/-! The definition `DOZZ.weightedGmcBallMass`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Weighted local GMC mass `∫_{B(z,r)} |x-z|^{-γα} M(dx)`, with the singular value at the
center interpreted as an extended nonnegative real. See [KRV, (annulus)] and
[KRV, (ThextendedSeibergbounds)]. -/
noncomputable def weightedGmcBallMass (γ : ℝ) (M : Measure ℂ) (α : ℝ)
    (z : ℂ) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Metric.ball z r,
    ENNReal.rpow (ENNReal.ofReal ‖x - z‖) (-γ * α) ∂M

end DOZZ

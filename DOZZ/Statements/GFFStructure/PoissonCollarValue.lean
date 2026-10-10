/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GFFStructure.DiskGreenCovariance

/-! The definition `DOZZ.poissonCollarValue`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

universe u

namespace DOZZ

/-- Smooth Poisson collar density in Cartesian coordinates. -/
noncomputable def poissonCollarValue (c z : ℂ) (ρ : ℝ) (_hρ : 0 < ρ)
    (_hz : z ∈ ball c ρ) (q : ℝ → ℝ) (w : ℂ) : ℝ :=
  q (‖w - c‖ - ρ) * (ρ ^ 2 - ‖z - c‖ ^ 2) /
    (2 * Real.pi * ‖w - c‖ * ‖c + (ρ : ℂ) * (w - c) / (‖w - c‖ : ℂ) - z‖ ^ 2)

end DOZZ

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Correlations.UniformPositiveC1Family

/-! The definition `DOZZ.localSingularMass`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The local singular mass at a center. The open unit ball is the source's insertion domain.
The extended-real power retains the source's infinite singularity at the center for `γα > 0`. -/
noncomputable def localSingularMass {Ω : Type*} (M : Ω → Measure ℂ)
    (F : ℂ → ℝ) (z : ℂ) (γ α : ℝ) (ω : Ω) : ℝ≥0∞ := by
  classical
  exact ∫⁻ x, (if x ∈ Metric.ball z 1 then
    ENNReal.ofReal (F x) *
      ENNReal.rpow (ENNReal.ofReal ‖x - z‖) (-γ * α) else 0) ∂M ω

end DOZZ

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.BrownianPiecewiseDrift
import DOZZ.Brownian.Barrier.GaussianBounds

/-! The statement `DOZZ.brownian_piecewiseDrift_barrier_bound`,
proved by `DOZZ.Proofs.brownian_piecewiseDrift_barrier_bound`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The barrier bound in the two piecewise-drift regimes. The separate cases keep the distinct
likelihood estimates when the second drift is nonnegative or nonpositive. -/
theorem brownian_piecewiseDrift_barrier_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (hB : ProbabilityTheory.IsBrownianReal B P) (α αtilde β s r : ℝ)
    (hβ : 0 ≤ β) (hs : 0 ≤ s) (hsr : s ≤ r) (hα : 0 ≤ α) :
    ((0 ≤ αtilde) →
      P {ω | ∀ u : ℝ≥0, (u : ℝ) ≤ r →
        B u ω + brownianPiecewiseDrift α αtilde s (u : ℝ) ≤ β} ≤
        ENNReal.ofReal (Real.exp
          (-((α + αtilde) ^ 2) * s / 2 - α ^ 2 * (r - s) / 2 +
            (α + αtilde) * β))) ∧
    ((αtilde ≤ 0) →
      P {ω | ∀ u : ℝ≥0, (u : ℝ) ≤ r →
        B u ω + brownianPiecewiseDrift α αtilde s (u : ℝ) ≤ β} ≤
        ENNReal.ofReal (Real.exp
          (-(((α + αtilde) ^ 2 - α ^ 2 - αtilde ^ 2) * s) / 2 -
            α ^ 2 * r / 2 + α * β))) := by exact DOZZ.Proofs.brownian_piecewiseDrift_barrier_bound P B hB α αtilde β s r hβ hs hsr hα

end DOZZ

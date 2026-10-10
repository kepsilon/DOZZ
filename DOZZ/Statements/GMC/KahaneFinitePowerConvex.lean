/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.FiniteChaosMoment
import DOZZ.GMC.FiniteChaosPowerShift

/-! The statement `DOZZ.kahane_finite_power_convex`,
proved by `DOZZ.Proofs.kahane_finite_power_convex`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Convex-power Kahane comparison for negative powers and powers at least one, as an inequality
of extended expectations. See [KRV, §9.2] and [KRV, §12.2]. -/
theorem kahane_finite_power_convex
    {ΩX ΩY : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    {ι : Type*} [Fintype ι]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (hX : IsCenteredJointlyGaussian PX X) (hY : IsCenteredJointlyGaussian PY Y)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (γ p : ℝ)
    (hp : p ≤ 0 ∨ 1 ≤ p)
    (hcov : ∀ i j,
      gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) ≤
        gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j)) :
    finiteChaosMoment PX X a γ p ≤ finiteChaosMoment PY Y a γ p := by exact DOZZ.Proofs.kahane_finite_power_convex PX PY X Y hX hY a ha γ p hp hcov

end DOZZ

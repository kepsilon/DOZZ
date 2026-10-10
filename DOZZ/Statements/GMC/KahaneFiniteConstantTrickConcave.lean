/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.FiniteChaosMoment
import DOZZ.GMC.FiniteChaosConstantTrick

/-! The statement `DOZZ.kahane_finite_constant_trick_concave`,
proved by `DOZZ.Proofs.kahane_finite_constant_trick_concave`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Two-sided finite-dimensional Kahane comparison for `0 < p < 1`; the constant-trick exponent
is `γ² C (p-p²)/2`. -/
theorem kahane_finite_constant_trick_concave
    {ΩX ΩY : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    {ι : Type*} [Fintype ι]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (hX : IsCenteredJointlyGaussian PX X) (hY : IsCenteredJointlyGaussian PY Y)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (γ C p : ℝ) (hC : 0 ≤ C)
    (hp : 0 < p ∧ p < 1)
    (hcov : ∀ i j, |gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) -
      gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j)| ≤ C) :
    ENNReal.ofReal (Real.exp (-(γ ^ 2 * C / 2 * (p - p ^ 2)))) *
        finiteChaosMoment PY Y a γ p ≤ finiteChaosMoment PX X a γ p ∧
      finiteChaosMoment PX X a γ p ≤
        ENNReal.ofReal (Real.exp (γ ^ 2 * C / 2 * (p - p ^ 2))) *
          finiteChaosMoment PY Y a γ p := by exact DOZZ.Proofs.kahane_finite_constant_trick_concave PX PY X Y hX hY a ha γ C p hC hp hcov

end DOZZ

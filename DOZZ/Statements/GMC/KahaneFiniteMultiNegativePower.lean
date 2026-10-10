/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.FieldChaosMass
import DOZZ.GMC.FiniteChaosMultiNegativePower

/-! The statement `DOZZ.kahane_finite_multi_negative_power`,
proved by `DOZZ.Proofs.kahane_finite_multi_negative_power`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Finite multivariate Kahane comparison for products of negative block-mass powers.
It is used in the freezing and weighted-moment arguments. -/
theorem kahane_finite_multi_negative_power
    {ΩX ΩY : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (hX : IsCenteredJointlyGaussian PX X) (hY : IsCenteredJointlyGaussian PY Y)
    (block : ι → κ) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (γ : ℝ)
    (q : κ → ℝ) (hq : ∀ k, 0 ≤ q k)
    (hcov : ∀ i j,
      gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) ≤
        gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j)) :
    ∫⁻ ω, ∏ k, ENNReal.rpow (ENNReal.ofReal
        (finiteChaosMass PX X (fun i => if block i = k then a i else 0) γ ω)) (-q k) ∂PX ≤
      ∫⁻ ω, ∏ k, ENNReal.rpow (ENNReal.ofReal
        (finiteChaosMass PY Y (fun i => if block i = k then a i else 0) γ ω)) (-q k) ∂PY := by exact DOZZ.Proofs.kahane_finite_multi_negative_power PX PY X Y hX hY block a ha γ q hq hcov

end DOZZ

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.FiniteChaosMass
import DOZZ.GMC.KahaneFiniteConcave

/-! The statement `DOZZ.kahane_finite_concave`, proved by `DOZZ.Proofs.kahane_finite_concave`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Kahane comparison for concave functions of finite-dimensional chaos masses; the inequality
reverses under entrywise covariance order. See [KRV, §9.2] and [KRV, §12.2]. -/
theorem kahane_finite_concave
    {ΩX ΩY : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    {ι : Type*} [Fintype ι]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (hX : IsCenteredJointlyGaussian PX X) (hY : IsCenteredJointlyGaussian PY Y)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (γ : ℝ)
    (hcov : ∀ i j,
      gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) ≤
        gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j))
    (F : ℝ → ℝ) (hF : Measurable F)
    (hconcave : ConcaveOn ℝ (Set.Ici 0) F)
    (hIY : Integrable (fun ω => F (finiteChaosMass PY Y a γ ω)) PY) :
    Integrable (fun ω => F (finiteChaosMass PX X a γ ω)) PX ∧
      ∫ ω, F (finiteChaosMass PX X a γ ω) ∂PX ≥
        ∫ ω, F (finiteChaosMass PY Y a γ ω) ∂PY := by exact DOZZ.Proofs.kahane_finite_concave PX PY X Y hX hY a ha γ hcov F hF hconcave hIY

end DOZZ

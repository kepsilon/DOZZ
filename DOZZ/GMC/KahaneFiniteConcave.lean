/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.KahaneFiniteConvex

/-! Finite Kahane comparison for concave tests by negation. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

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
        ∫ ω, F (finiteChaosMass PY Y a γ ω) ∂PY := by
  have h := kahane_finite_convex PX PY X Y hX hY a ha γ hcov
    (fun x => -F x) hF.neg hconcave.neg hIY.neg
  constructor
  · convert h.1.neg using 1
    funext ω
    exact (neg_neg _).symm
  · simpa only [integral_neg, neg_le_neg_iff] using h.2


end DOZZ.Proofs

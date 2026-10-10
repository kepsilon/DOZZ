/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.FieldChaosMass
import DOZZ.GMC.FieldChaosConstantTrick

/-! The statement `DOZZ.kahane_field_constant_trick`,
proved by `DOZZ.Proofs.kahane_field_constant_trick`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Continuum constant trick: a uniform covariance discrepancy transfers all convex and concave
power moments in both directions by adding a common independent Gaussian scalar. -/
theorem kahane_field_constant_trick
    {ΩX ΩY S : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [MeasurableSpace S]
    (PX : Measure ΩX) (PY : Measure ΩY) (Φ : ΩX → S → ℝ) (Ψ : ΩY → S → ℝ)
    (hΦ : IsCenteredGaussianField PX Φ) (hΨ : IsCenteredGaussianField PY Ψ)
    (ν : Measure S) [IsFiniteMeasure ν] (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ C p : ℝ) (hC : 0 ≤ C)
    (hp : p ≤ 0 ∨ 1 ≤ p)
    (hcov : ∀ᵐ q ∂ν.prod ν,
      |(∫ ω, Φ ω q.1 * Φ ω q.2 ∂PX) -
        (∫ ω, Ψ ω q.1 * Ψ ω q.2 ∂PY)| ≤ C)
    (hdiag : ∀ᵐ x ∂ν,
      |(∫ ω, Φ ω x ^ 2 ∂PX) - (∫ ω, Ψ ω x ^ 2 ∂PY)| ≤ C) :
    ENNReal.ofReal (Real.exp (-(γ ^ 2 * C / 2 * (p ^ 2 - p)))) *
        (∫⁻ ω, fieldChaosMass PY Ψ ν h γ ω ^ p ∂PY) ≤
          ∫⁻ ω, fieldChaosMass PX Φ ν h γ ω ^ p ∂PX ∧
      (∫⁻ ω, fieldChaosMass PX Φ ν h γ ω ^ p ∂PX) ≤
        ENNReal.ofReal (Real.exp (γ ^ 2 * C / 2 * (p ^ 2 - p))) *
          (∫⁻ ω, fieldChaosMass PY Ψ ν h γ ω ^ p ∂PY) := by exact DOZZ.Proofs.kahane_field_constant_trick PX PY Φ Ψ hΦ hΨ ν h hh hhb γ C p hC hp hcov hdiag

end DOZZ

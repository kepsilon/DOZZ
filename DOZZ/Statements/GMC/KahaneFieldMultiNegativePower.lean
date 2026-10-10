/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.FieldChaosMass
import DOZZ.GMC.FieldChaosMultiNegativePower

/-! The statement `DOZZ.kahane_field_multi_negative_power`,
proved by `DOZZ.Proofs.kahane_field_multi_negative_power`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Continuum multivariate Kahane comparison for products of negative block-mass powers. The
blocks may overlap; covariance order is imposed on the common disjoint-union reference space. -/
theorem kahane_field_multi_negative_power
    {ΩX ΩY S κ : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    [MeasurableSpace S] [Fintype κ]
    (PX : Measure ΩX) (PY : Measure ΩY) (Φ : ΩX → S → ℝ) (Ψ : ΩY → S → ℝ)
    (hΦ : IsCenteredGaussianField PX Φ) (hΨ : IsCenteredGaussianField PY Ψ)
    (ν : Measure S) [IsFiniteMeasure ν] (h : κ → S → ℝ≥0)
    (hh : ∀ k, Measurable (h k))
    (hhb : ∀ k, ∃ c : ℝ≥0, ∀ x, h k x ≤ c)
    (γ : ℝ) (q : κ → ℝ) (hq : ∀ k, 0 ≤ q k)
    (hcov : ∀ᵐ xy ∂ν.prod ν,
      ∫ ω, Φ ω xy.1 * Φ ω xy.2 ∂PX ≤ ∫ ω, Ψ ω xy.1 * Ψ ω xy.2 ∂PY)
    (hdiag : ∀ᵐ x ∂ν,
      ∫ ω, Φ ω x ^ 2 ∂PX ≤ ∫ ω, Ψ ω x ^ 2 ∂PY) :
    ∫⁻ ω, ∏ k, ENNReal.rpow (fieldChaosMass PX Φ ν (h k) γ ω) (-q k) ∂PX ≤
      ∫⁻ ω, ∏ k, ENNReal.rpow (fieldChaosMass PY Ψ ν (h k) γ ω) (-q k) ∂PY := by exact DOZZ.Proofs.kahane_field_multi_negative_power PX PY Φ Ψ hΦ hΨ ν h hh hhb γ q hq hcov hdiag

end DOZZ

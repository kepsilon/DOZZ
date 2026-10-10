/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.FieldChaosMass
import DOZZ.GMC.KahaneLimitFieldMultiNegativePower

/-! The statement `DOZZ.kahane_limit_field_multi_negative_power`,
proved by `DOZZ.Proofs.kahane_limit_field_multi_negative_power`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Multivariate negative-power Kahane comparison for chaos limits. Convergence in probability of
each block mass suffices, through the multivariate Laplace representation. -/
theorem kahane_limit_field_multi_negative_power
    {ΩX ΩY S κ : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [MeasurableSpace S]
    [Fintype κ]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (Φ : ℝ → ΩX → S → ℝ) (Ψ : ℝ → ΩY → S → ℝ)
    (hΦ : ∀ r, IsCenteredGaussianField PX (Φ r))
    (hΨ : ∀ r, IsCenteredGaussianField PY (Ψ r))
    (ν : Measure S) [IsFiniteMeasure ν] (h : κ → S → ℝ≥0)
    (hh : ∀ k, Measurable (h k)) (hhb : ∀ k, ∃ c : ℝ≥0, ∀ x, h k x ≤ c)
    (γ : ℝ) (q : κ → ℝ) (hq : ∀ k, 0 ≤ q k)
    (hcov : ∀ r, ∀ᵐ xy ∂ν.prod ν,
      ∫ ω, Φ r ω xy.1 * Φ r ω xy.2 ∂PX ≤ ∫ ω, Ψ r ω xy.1 * Ψ r ω xy.2 ∂PY)
    (hdiag : ∀ r, ∀ᵐ x ∂ν,
      ∫ ω, Φ r ω x ^ 2 ∂PX ≤ ∫ ω, Ψ r ω x ^ 2 ∂PY)
    (ZX : κ → ΩX → ℝ) (ZY : κ → ΩY → ℝ)
    (hXconv : ∀ k, TendstoInMeasure PX
      (fun r ω => (fieldChaosMass PX (Φ r) ν (h k) γ ω).toReal) atTop (ZX k))
    (hYconv : ∀ k, TendstoInMeasure PY
      (fun r ω => (fieldChaosMass PY (Ψ r) ν (h k) γ ω).toReal) atTop (ZY k)) :
    ∫⁻ ω, ∏ k, ENNReal.rpow (ENNReal.ofReal (ZX k ω)) (-q k) ∂PX ≤
      ∫⁻ ω, ∏ k, ENNReal.rpow (ENNReal.ofReal (ZY k ω)) (-q k) ∂PY := by exact DOZZ.Proofs.kahane_limit_field_multi_negative_power PX PY Φ Ψ hΦ hΨ ν h hh hhb γ q hq hcov hdiag ZX ZY hXconv hYconv

end DOZZ

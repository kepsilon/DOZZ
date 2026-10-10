/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.FieldChaosMass
import DOZZ.GMC.KahaneLimitFieldPositivePower

/-! The statement `DOZZ.kahane_limit_field_positive_power`,
proved by `DOZZ.Proofs.kahane_limit_field_positive_power`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Limit Kahane comparison for positive powers above one. Each finite-cutoff pair satisfies the
continuum covariance order; convergence against the test mass in probability and in `L¹` passes
the comparison to the chaos limits. -/
theorem kahane_limit_field_positive_power
    {ΩX ΩY S : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [MeasurableSpace S]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (Φ : ℝ → ΩX → S → ℝ) (Ψ : ℝ → ΩY → S → ℝ)
    (hΦ : ∀ r, IsCenteredGaussianField PX (Φ r))
    (hΨ : ∀ r, IsCenteredGaussianField PY (Ψ r))
    (ν : Measure S) [IsFiniteMeasure ν] (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ p : ℝ) (hp : 1 < p)
    (hcov : ∀ r, ∀ᵐ q ∂ν.prod ν,
      ∫ ω, Φ r ω q.1 * Φ r ω q.2 ∂PX ≤ ∫ ω, Ψ r ω q.1 * Ψ r ω q.2 ∂PY)
    (hdiag : ∀ r, ∀ᵐ x ∂ν,
      ∫ ω, Φ r ω x ^ 2 ∂PX ≤ ∫ ω, Ψ r ω x ^ 2 ∂PY)
    (ZX : ΩX → ℝ) (ZY : ΩY → ℝ)
    (hXconv : TendstoInMeasure PX
      (fun r ω => (fieldChaosMass PX (Φ r) ν h γ ω).toReal) atTop ZX)
    (hYconv : TendstoInMeasure PY
      (fun r ω => (fieldChaosMass PY (Ψ r) ν h γ ω).toReal) atTop ZY)
    (hXL1 : Tendsto (fun r : ℝ =>
      eLpNorm (fun ω => (fieldChaosMass PX (Φ r) ν h γ ω).toReal - ZX ω) 1 PX)
      atTop (𝓝 0))
    (hYL1 : Tendsto (fun r : ℝ =>
      eLpNorm (fun ω => (fieldChaosMass PY (Ψ r) ν h γ ω).toReal - ZY ω) 1 PY)
      atTop (𝓝 0)) :
    ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (ZX ω)) p ∂PX ≤
      ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (ZY ω)) p ∂PY := by exact DOZZ.Proofs.kahane_limit_field_positive_power PX PY Φ Ψ hΦ hΨ ν h hh hhb γ p hp hcov hdiag ZX ZY hXconv hYconv hXL1 hYL1

end DOZZ

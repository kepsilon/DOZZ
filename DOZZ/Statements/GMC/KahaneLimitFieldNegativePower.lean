/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.FieldChaosMass
import DOZZ.GMC.KahaneLimitFieldNegativePower

/-! The statement `DOZZ.kahane_limit_field_negative_power`,
proved by `DOZZ.Proofs.kahane_limit_field_negative_power`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Limit Kahane comparison for negative powers. Convergence in probability suffices because the
comparison passes through bounded Laplace tests; no `L¹` convergence of the masses is needed. -/
theorem kahane_limit_field_negative_power
    {ΩX ΩY S : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [MeasurableSpace S]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (Φ : ℝ → ΩX → S → ℝ) (Ψ : ℝ → ΩY → S → ℝ)
    (hΦ : ∀ r, IsCenteredGaussianField PX (Φ r))
    (hΨ : ∀ r, IsCenteredGaussianField PY (Ψ r))
    (ν : Measure S) [IsFiniteMeasure ν] (h : S → ℝ≥0) (hh : Measurable h)
    (hhb : ∃ c : ℝ≥0, ∀ x, h x ≤ c) (γ q : ℝ) (hq : 0 < q)
    (hcov : ∀ r, ∀ᵐ xy ∂ν.prod ν,
      ∫ ω, Φ r ω xy.1 * Φ r ω xy.2 ∂PX ≤ ∫ ω, Ψ r ω xy.1 * Ψ r ω xy.2 ∂PY)
    (hdiag : ∀ r, ∀ᵐ x ∂ν,
      ∫ ω, Φ r ω x ^ 2 ∂PX ≤ ∫ ω, Ψ r ω x ^ 2 ∂PY)
    (ZX : ΩX → ℝ) (ZY : ΩY → ℝ)
    (hXconv : TendstoInMeasure PX
      (fun r ω => (fieldChaosMass PX (Φ r) ν h γ ω).toReal) atTop ZX)
    (hYconv : TendstoInMeasure PY
      (fun r ω => (fieldChaosMass PY (Ψ r) ν h γ ω).toReal) atTop ZY) :
    ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (ZX ω)) (-q) ∂PX ≤
      ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (ZY ω)) (-q) ∂PY := by exact DOZZ.Proofs.kahane_limit_field_negative_power PX PY Φ Ψ hΦ hΨ ν h hh hhb γ q hq hcov hdiag ZX ZY hXconv hYconv

end DOZZ

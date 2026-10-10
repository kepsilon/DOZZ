/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FieldChaosConstantTrick
public import DOZZ.GMC.FieldChaosConstantTrickConcave

/-! Finite-cutoff Kahane comparison for every positive moment in the separated joint-tail
estimate. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The convex and concave constant tricks cover every positive order with the same
absolute quadratic correction. No limiting Dirichlet chaos is used. -/
theorem separatedTail_fieldChaosMoment_le_of_covariance_discrepancy
    {ΩX ΩY S : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [MeasurableSpace S]
    (PX : Measure ΩX) (PY : Measure ΩY) (Φ : ΩX → S → ℝ) (Ψ : ΩY → S → ℝ)
    (hΦ : DOZZ.IsCenteredGaussianField PX Φ) (hΨ : DOZZ.IsCenteredGaussianField PY Ψ)
    (ν : Measure S) [IsFiniteMeasure ν] (w : S → ℝ≥0) (hw : Measurable w)
    (hwb : ∃ b : ℝ≥0, ∀ x, w x ≤ b) (γ C t : ℝ) (hC : 0 ≤ C) (ht : 0 < t)
    (hcov : ∀ᵐ xy ∂ν.prod ν, |(∫ ω, Φ ω xy.1 * Φ ω xy.2 ∂PX) -
      (∫ ω, Ψ ω xy.1 * Ψ ω xy.2 ∂PY)| ≤ C)
    (hdiag : ∀ᵐ x ∂ν, |(∫ ω, Φ ω x ^ 2 ∂PX) - (∫ ω, Ψ ω x ^ 2 ∂PY)| ≤ C) :
    (∫⁻ ω, DOZZ.fieldChaosMass PX Φ ν w γ ω ^ t ∂PX) ≤
      ENNReal.ofReal (Real.exp (γ^2*C/2*|t^2-t|)) *
        (∫⁻ ω, DOZZ.fieldChaosMass PY Ψ ν w γ ω ^ t ∂PY) := by
  rcases le_or_gt 1 t with h | h
  · have hsign : 0 ≤ t^2-t := by nlinarith
    simpa only [abs_of_nonneg hsign] using
      (kahane_field_constant_trick PX PY Φ Ψ hΦ hΨ ν w hw hwb γ C t hC
        (Or.inr h) hcov hdiag).2
  · have hsign : t^2-t ≤ 0 := by nlinarith
    simpa only [abs_of_nonpos hsign, neg_sub] using
      (kahane_field_constant_trick_concave PX PY Φ Ψ hΦ hΨ ν w hw hwb γ C t hC
        ⟨ht,h⟩ hcov hdiag).2

end DOZZ.Proofs

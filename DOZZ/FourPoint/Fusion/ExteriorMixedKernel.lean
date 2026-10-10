/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.ExteriorSecondKernel

/-! # The exterior second derivative kernel has a bounded denominator -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The mixed exterior kernel is the complex cast of the norm of the pure kernel. -/
theorem fusion_exteriorMixedKernel_integrable (γ α₁ α₂ α₃ : ℝ) (z : ℂ)
    (hz : ‖z‖ ≤ 1 / 4) (μ : Measure ℂ)
    (hkernel : (∫⁻ x, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂μ) < ⊤) :
    IntegrableOn (fun x : ℂ => (gammaHalfKernel γ α₁ α₂ α₃ z x : ℂ) / (‖x - z‖ ^ 2 : ℝ))
      (Metric.ball (0 : ℂ) (1 / 2))ᶜ μ := by
  have h : IntegrableOn (fun x : ℂ => (‖(gammaHalfKernel γ α₁ α₂ α₃ z x : ℂ) / (x - z) ^ 2‖ : ℂ))
      (Metric.ball (0 : ℂ) (1 / 2))ᶜ μ :=
    (fusion_exteriorSecondKernel_integrable γ α₁ α₂ α₃ z hz μ hkernel).norm.ofReal
  simpa only [fusion_secondKernel_norm, Complex.ofReal_div] using h

end DOZZ.Proofs

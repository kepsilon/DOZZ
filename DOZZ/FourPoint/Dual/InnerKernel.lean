/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Dual.Kernel
import DOZZ.FourPoint.Reflected.InnerKernelSqueeze
import Mathlib.Tactic

/-! # Uniform radial squeeze for the dual inner kernel

The deterministic k=2 squeeze used in the dual inner-limit comparison.
-/

public section

namespace DOZZ.Proofs

/-- The actual dual density is squeezed by its two radial Williams weights. -/
theorem dual_inner_kernel_squeeze (γ α₁ α₂ α₃ R η : ℝ) (hγ : γ ≠ 0) (z x : ℂ)
    (hR : 0 ≤ R) (hR₁ : R < 1) (hη : 0 ≤ η) (hη₁ : η < 1)
    (hz : 0 < ‖z‖) (hx : 0 < ‖x‖)
    (hsep : ‖x‖ ≤ R * ‖z‖) (hsmall : ‖x‖ ≤ η) :
    ((1 - R) ^ (2 : ℝ) * (1 - η)⁻¹ ^ (-|γ * α₂|)) *
        (‖z‖ ^ (2 : ℝ) * ‖x‖ ^ (-(γ * α₁))) ≤
      dualFusionKernel γ α₁ α₂ α₃ z x ∧
    dualFusionKernel γ α₁ α₂ α₃ z x ≤
      ((1 + R) ^ (2 : ℝ) * (1 - η)⁻¹ ^ |γ * α₂|) *
        (‖z‖ ^ (2 : ℝ) * ‖x‖ ^ (-(γ * α₁))) := by
  rw [dual_kernel_eq_scaled_half γ α₁ α₂ α₃ hγ z x]
  have hh := reflected_inner_kernel_squeeze 2 (γ * α₁ / 2) (γ * α₂ / 2)
    (γ * α₃ / 2) R η z x hR hR₁ hη hη₁ hz hx hsep hsmall
  rw [show (2 : ℝ) ^ 2 / 2 = 2 by norm_num,
    show 2 * (γ * α₁ / 2) = γ * α₁ by ring,
    show 2 * (γ * α₂ / 2) = γ * α₂ by ring] at hh
  exact hh

end DOZZ.Proofs

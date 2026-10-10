/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Dual.Kernel
public import DOZZ.FourPoint.Dual.Normalization
import DOZZ.FourPoint.BPZ.Mass
import Mathlib.Tactic

/-! # The literal dual four-point observable

The source zero-mode normalization is attached to the actual dual density,
with atomlessness supplied by the GMC rather than assumed at the roots.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace DOZZ.Proofs

/-- The reduced dual four-point correlation is the actual kernel inverse moment times its prefactor. -/
theorem fourPointT_eq_dualKernelMoment
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (μ α₁ α₂ α₃ : ℝ) (z : ℂ) :
    fourPointT P M γ μ (-2 / γ) α₁ α₂ α₃ z =
      (2 * μ ^ (-((α₁ + α₂ + α₃ - 2 / γ - 2 * Q γ) / γ)) / γ *
        Real.Gamma ((α₁ + α₂ + α₃ - 2 / γ - 2 * Q γ) / γ)) *
      (∫⁻ ω, (∫⁻ x, ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂M ω) ^
        (-((α₁ + α₂ + α₃ - 2 / γ - 2 * Q γ) / γ)) ∂P).toReal := by
  have ht := fourPointT_eq_bpzMass (χ := 2 / γ) (α₁ := α₁) (α₂ := α₂) (α₃ := α₃)
    P X hX hγ hγ₂ M hM μ z
  have hs : fourPointSExp γ (-(2 / γ)) α₁ α₂ α₃ =
      (α₁ + α₂ + α₃ - 2 / γ - 2 * Q γ) / γ := by
    rw [← neg_div]
    exact fourPointSExp_dual γ α₁ α₂ α₃
  rw [hs] at ht
  simpa only [neg_div, bpzMass, ENNReal.rpow_eq_pow,
    dual_kernel_eq_bpzWeight γ α₁ α₂ α₃ hγ.ne'] using ht

end DOZZ.Proofs

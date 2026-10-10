/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.SpatialCutoffs
public import DOZZ.FourPoint.Reflected.OuterKernelLimit
public import DOZZ.FourPoint.TwoRootedDomination
/-! Compact spatial tests for the literal reflected kernel. -/
@[expose] public section
open MeasureTheory Set Filter Topology
namespace DOZZ.Proofs

/-- The integration-point kernel is continuous away from its two singular roots; its moving
insertion has a nonnegative exponent and does not need to be excluded. -/
theorem reflected_spatial_kernel_continuousOn (γ α₁ α₂ α₃ : ℝ) (z : ℂ) :
    ContinuousOn (gammaHalfKernel γ α₁ α₂ α₃ z) ({0, 1} : Set ℂ)ᶜ := by
  intro x hx
  have hx0 : x ≠ 0 := fun h => hx (by simp [h])
  have hx1 : x ≠ 1 := fun h => hx (by simp [h])
  have h0 : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have h1 : 0 < ‖x-1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx1)
  have hplus : Continuous normPlus := by unfold normPlus; fun_prop
  have hpp : 0 < normPlus x := by unfold normPlus; positivity
  have hn : ContinuousAt (fun x : ℂ => ‖x-z‖^(γ^2/2)) x :=
    ((continuous_id.sub continuous_const).norm.continuousAt).rpow_const
      (Or.inr (by positivity))
  have hd0 : ContinuousAt (fun x : ℂ => ‖x‖^(γ*α₁)) x :=
    continuous_norm.continuousAt.rpow_const (Or.inl h0.ne')
  have hd1 : ContinuousAt (fun x : ℂ => ‖x-1‖^(γ*α₂)) x :=
    ((continuous_id.sub continuous_const).norm.continuousAt).rpow_const (Or.inl h1.ne')
  exact ((hn.mul (hplus.continuousAt.rpow_const (Or.inl hpp.ne'))).div
    (hd0.mul hd1) (mul_ne_zero (Real.rpow_pos_of_pos h0 _).ne'
      (Real.rpow_pos_of_pos h1 _).ne')).continuousWithinAt

/-- Literal reflected-kernel tests exhaust both the mass and its guarded inverse expectations
on any open subregion away from the roots. -/
theorem reflected_spatial_kernel_inverse_approximation (γ α₁ α₂ α₃ : ℝ) (z : ℂ)
    (U : Set ℂ) (hU : IsOpen U) (hroots : U ⊆ ({0, 1} : Set ℂ)ᶜ)
    (D : Set ℂ) (hD : IsCompact D) (hDU : D ⊆ U) :
    ∃ g : ℕ → BoundedContinuousFunction ℂ ℝ,
      (∀ n, EqOn (g n) (gammaHalfKernel γ α₁ α₂ α₃ z) D) ∧
      (∀ n, IsCompact (tsupport (g n : ℂ → ℝ))) ∧
      (∀ n, tsupport (g n : ℂ → ℝ) ⊆ U) ∧
      (∀ n x, 0 ≤ g n x) ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M : Ω → Measure ℂ),
        Measurable M →
        (∀ᵐ ω ∂P, (∫⁻ x in U, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂M ω) ≠ ⊤) →
        ∀ q : ℝ, 0 ≤ q →
        (∫⁻ ω, (∫⁻ x in D, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂M ω)^(-q) ∂P) ≠ ⊤ →
        Tendsto (fun n => ∫⁻ ω, (∫⁻ x, ENNReal.ofReal (g n x) ∂M ω)^(-q) ∂P)
          atTop (𝓝 (∫⁻ ω, (∫⁻ x in U,
            ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂M ω)^(-q) ∂P)) := by
  exact reflected_open_weighted_inverse_approximation U hU D hD hDU
    (gammaHalfKernel γ α₁ α₂ α₃ z)
    ((reflected_spatial_kernel_continuousOn γ α₁ α₂ α₃ z).mono hroots)
    (reflected_gammaHalfKernel_measurable γ α₁ α₂ α₃ z)
    (gammaHalfKernel_nonneg γ α₁ α₂ α₃ z)

end DOZZ.Proofs

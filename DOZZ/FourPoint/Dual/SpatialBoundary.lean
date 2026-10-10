/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.OuterMassLimit
public import DOZZ.FourPoint.Reflected.SpatialBoundary
/-! Removing the deterministic circle boundary from the literal retained region. -/
@[expose] public section
open MeasureTheory Set Filter
open scoped ENNReal
namespace DOZZ.Proofs

/-- The literal retained Coulomb mass equals its open-exterior kernel integral. -/
theorem dual_outerMass_eq_open_kernel (γ α₁ α₂ α₃ ξ : ℝ) (hγ : γ ≠ 0) (z : ℂ)
    (μ : Measure ℂ) (h0 : μ {0} = 0) (h1 : μ {1} = 0)
    (hz : ‖z‖ < ‖z‖ ^ (1 - ξ))
    (hs : μ (Metric.sphere (0 : ℂ) (‖z‖ ^ (1 - ξ))) = 0) :
    dualOuterMass γ α₁ α₂ α₃ μ z ξ =
      ∫⁻ x in {x : ℂ | ‖z‖ ^ (1 - ξ) < ‖x‖},
        ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂μ := by
  rw [dual_outerMass_eq_kernel_integral γ α₁ α₂ α₃ ξ hγ z μ h0 h1 hz]
  exact reflected_exterior_integral_open μ _ hs _

/-- The retained mass `dualOuterMass` is exactly the full open region required by comparison. -/
theorem dual_outerMass_eq_comparison_region (γ α₁ α₂ α₃ ξ : ℝ) (hγ : γ ≠ 0) (z : ℂ)
    (μ : Measure ℂ) (h0 : μ {0} = 0) (h1 : μ {1} = 0)
    (hz : ‖z‖ < ‖z‖ ^ (1 - ξ))
    (hs : μ (Metric.sphere (0 : ℂ) (‖z‖ ^ (1 - ξ))) = 0) :
    dualOuterMass γ α₁ α₂ α₃ μ z ξ =
      ∫⁻ x in {x : ℂ | ‖z‖ ^ (1 - ξ) < ‖x‖} ∩ ({0, 1} : Set ℂ)ᶜ,
        ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂μ := by
  rw [dual_outerMass_eq_open_kernel γ α₁ α₂ α₃ ξ hγ z μ h0 h1 hz hs]
  exact reflected_open_exterior_remove_roots μ _ ((norm_nonneg z).trans_lt hz) h1 _

/-- The supplied ordinary GMC has precisely the open retained mass almost surely. -/
theorem dual_source_outerMass_eq_comparison_region
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ ξ : ℝ) (z : ℂ) (hz : ‖z‖ < ‖z‖ ^ (1 - ξ)) :
    ∀ᵐ ω ∂P, dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ =
      ∫⁻ x in {x : ℂ | ‖z‖ ^ (1 - ξ) < ‖x‖} ∩ ({0, 1} : Set ℂ)ᶜ,
        ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂M ω := by
  filter_upwards [reflected_gmc_sphere_null P X hX γ hγ hγ₂ M hM 0 0,
    reflected_gmc_sphere_null P X hX γ hγ hγ₂ M hM 1 0,
    reflected_gmc_sphere_null P X hX γ hγ hγ₂ M hM 0 (‖z‖ ^ (1 - ξ))]
      with ω h0 h1 hs
  simp only [Metric.sphere_zero] at h0 h1
  exact dual_outerMass_eq_comparison_region γ α₁ α₂ α₃ ξ hγ.ne' z (M ω) h0 h1 hz hs

end DOZZ.Proofs

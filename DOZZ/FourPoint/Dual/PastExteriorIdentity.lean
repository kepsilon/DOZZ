/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.SourceCopiedOuterLaw
import Mathlib.Tactic
/-! The stopped-past exterior observable is the actual retained source mass. -/
@[expose] public section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- On an exterior region beyond the restart disk, the measurable past mass is precisely
the kernel mass of the radially reinserted lateral measure. -/
theorem dual_past_exterior_mass_reinserted (γ α₁ α₂ α₃ : ℝ) (z : ℂ)
    (A : TwoSidedPath) (T : ℝ≥0) (r : ℝ) (hr : Real.exp (-(T : ℝ)) ≤ r)
    (N : DualLocalPlaneMeasure) :
    dualPastExteriorMass γ α₁ α₂ α₃ z r
      ((stopBrownianPath (radialPositiveHalf A) T, radialNegativeHalf A), N) =
      ∫⁻ x in reflected_outerRegion r, ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x)
        ∂N.val.withDensity (fun x => ENNReal.ofReal (reflected_global_reinsertionWeight γ A x)) := by
  rw [dual_past_exterior_mass_eq γ α₁ α₂ α₃ z A T r hr N]
  let U := reflected_outerRegion r
  have hU : MeasurableSet U := (isOpen_lt continuous_const continuous_norm).measurableSet.inter
    (Set.Finite.measurableSet (by simp)).compl
  have hU0 : U ⊆ ({0} : Set ℂ)ᶜ := by
    intro x hx hx0
    exact hx.2 (by simp [mem_singleton_iff.mp hx0])
  rw [setLIntegral_indicator hU, inter_eq_left.mpr hU0]
  have hW : Measurable (fun x => ENNReal.ofReal (reflected_global_reinsertionWeight γ A x)) :=
    ((reflected_global_reinsertionWeight_measurable γ).comp
      (measurable_const.prodMk measurable_id)).ennreal_ofReal
  rw [setLIntegral_withDensity_eq_setLIntegral_mul N.val hW
    (dual_kernel_measurable γ α₁ α₂ α₃ z).ennreal_ofReal hU]
  apply setLIntegral_congr_fun hU
  intro x _
  exact mul_comm _ _

/-- The supplied GMC and its exact radial removal identify the stopped-past observable
with the actual retained mass, including the removed deterministic boundary. -/
theorem dual_source_past_exterior_mass_eq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M N : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (A : Ω → TwoSidedPath)
    (hfin : ∀ ω K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → N ω K < ⊤)
    (heq : N =ᵐ[P] (fun ω => (M ω).withDensity (lateralRadialWeight γ (A ω))))
    (α₁ α₂ α₃ ξ : ℝ) (z : ℂ) (hz : ‖z‖ < ‖z‖^(1-ξ))
    (T : ℝ≥0) (hT : Real.exp (-(T : ℝ)) ≤ ‖z‖^(1-ξ)) :
    ∀ᵐ ω ∂P, dualPastExteriorMass γ α₁ α₂ α₃ z (‖z‖^(1-ξ))
      ((stopBrownianPath (radialPositiveHalf (A ω)) T, radialNegativeHalf (A ω)),
        (⟨N ω, hfin ω⟩ : DualLocalPlaneMeasure)) = dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ := by
  let U := reflected_outerRegion (‖z‖^(1-ξ))
  have hU : MeasurableSet U := (isOpen_lt continuous_const continuous_norm).measurableSet.inter
    (Set.Finite.measurableSet (by simp)).compl
  have hU0 : U ⊆ ({0} : Set ℂ)ᶜ := by
    intro x hx hx0
    exact hx.2 (by simp [mem_singleton_iff.mp hx0])
  filter_upwards [heq, dual_source_outerMass_eq_comparison_region P X hX γ hγ hγ₂ M hM
    α₁ α₂ α₃ ξ z hz] with ω hω houter
  rw [dual_past_exterior_mass_reinserted γ α₁ α₂ α₃ z (A ω) T _ hT]
  have hrein : (N ω).withDensity
      (fun x => ENNReal.ofReal (reflected_global_reinsertionWeight γ (A ω) x)) =
      (M ω).restrict ({0} : Set ℂ)ᶜ := by
    rw [hω]
    exact reflected_global_reinsertion_measure γ (A ω) (M ω)
  change (∫⁻ x in U, ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x)
    ∂(N ω).withDensity (fun x => ENNReal.ofReal (reflected_global_reinsertionWeight γ (A ω) x))) = _
  rw [hrein, Measure.restrict_restrict hU, inter_eq_left.mpr hU0]
  exact houter.symm

end DOZZ.Proofs

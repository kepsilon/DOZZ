/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Reflected.OuterKernelLimit
public import DOZZ.FourPoint.Reflected.MassFiniteness
public import DOZZ.FourPoint.TaylorKernelMass
public import DOZZ.Statements.FourPoint.GammaHalfOuterMass
import Mathlib.Tactic

/-! # The literal outer mass and its subcritical limiting rho -/

public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- The zero-kernel integral is the literal rho with effective charge `α₁-γ/2`. -/
theorem reflected_zero_kernel_integral_eq_rho (γ α₁ α₂ α₃ : ℝ) (μ : Measure ℂ)
    (h0 : μ {0} = 0) (h1 : μ {1} = 0) :
    (∫⁻ x, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ 0 x) ∂μ) =
      rho γ μ (α₁ - γ / 2) α₂ α₃ := by
  have ha0 : ∀ᵐ x ∂μ, x ≠ 0 := by
    rw [ae_iff]; simpa only [not_not, Set.ofPred_eq_eq_singleton] using h0
  have ha1 : ∀ᵐ x ∂μ, x ≠ 1 := by
    rw [ae_iff]; simpa only [not_not, Set.ofPred_eq_eq_singleton] using h1
  unfold rho
  apply lintegral_congr_ae
  filter_upwards [ha0, ha1] with x hx0 hx1
  exact congrArg ENNReal.ofReal (reflected_zero_kernel_weight γ α₁ α₂ α₃ x hx0 hx1)

/-- The moving root is absent from the retained region, so no atom assumption at `z` is needed. -/
theorem reflected_outerMass_eq_kernel_integral (γ α₁ α₂ α₃ ξ : ℝ) (z : ℂ)
    (μ : Measure ℂ) (h0 : μ {0} = 0) (h1 : μ {1} = 0)
    (hz : ‖z‖ < ‖z‖ ^ (1 - ξ)) :
    gammaHalfOuterMass γ α₁ α₂ α₃ μ z ξ =
      ∫⁻ x in {x : ℂ | ‖z‖ ^ (1 - ξ) ≤ ‖x‖},
        ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂μ := by
  let D : Set ℂ := {x | ‖z‖ ^ (1 - ξ) ≤ ‖x‖}
  have hzD : z ∉ D := not_le.mpr hz
  have hzr : (μ.restrict D) {z} = 0 := by
    rw [Measure.restrict_apply (measurableSet_singleton z),
      singleton_inter_of_notMem hzD, measure_empty]
  have h0r : (μ.restrict D) {0} = 0 := by
    apply le_zero_iff.mp
    rw [Measure.restrict_apply (measurableSet_singleton 0)]
    exact (measure_mono inter_subset_left).trans_eq h0
  have h1r : (μ.restrict D) {1} = 0 := by
    apply le_zero_iff.mp
    rw [Measure.restrict_apply (measurableSet_singleton 1)]
    exact (measure_mono inter_subset_left).trans_eq h1
  exact (gammaHalfMass_eq_coulombMass γ α₁ α₂ α₃ z (μ.restrict D) hzr h0r h1r).symm

/-- The literal retained mass tends to its rho, including when the first bare charge is above Q. -/
theorem reflected_outerMass_tendsto (γ α₁ α₂ α₃ ξ : ℝ) (μ : Measure ℂ)
    (hξ : 0 < ξ) (hξ₁ : ξ < 1) (h0 : μ {0} = 0) (h1 : μ {1} = 0)
    (hfin : rho γ μ (α₁ - γ / 2) α₂ α₃ ≠ ⊤) :
    Tendsto (fun z : ℂ => gammaHalfOuterMass γ α₁ α₂ α₃ μ z ξ)
      (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0})
      (nhds (rho γ μ (α₁ - γ / 2) α₂ α₃)) := by
  have heq := reflected_zero_kernel_integral_eq_rho γ α₁ α₂ α₃ μ h0 h1
  have ht := reflected_outer_kernel_integral_tendsto γ α₁ α₂ α₃ ξ μ hξ hξ₁ h0
    (by rw [heq]; exact hfin)
  rw [heq] at ht
  have hn : Tendsto (fun z : ℂ => ‖z‖)
      (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}) (nhds 0) := by
    simpa only [norm_zero] using (continuous_norm.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
  apply ht.congr'
  filter_upwards [hn.eventually (gt_mem_nhds zero_lt_one), self_mem_nhdsWithin] with z hz hz0
  have hr : ‖z‖ < ‖z‖ ^ (1 - ξ) := by
    have hh := Real.rpow_lt_rpow_of_exponent_gt (norm_pos_iff.mpr hz0) hz
      (by linarith only [hξ] : 1 - ξ < 1)
    simpa only [Real.rpow_one] using hh
  exact (reflected_outerMass_eq_kernel_integral γ α₁ α₂ α₃ ξ z μ h0 h1 hr).symm

/-- Almost-sure convergence of the actual retained GMC mass in the reflected chart. -/
theorem reflected_outerMass_ae_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ ξ : ℝ) (hξ : 0 < ξ) (hξ₁ : ξ < 1)
    (hα₁ : α₁ - γ / 2 < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) :
    ∀ᵐ ω ∂P, Tendsto (fun z : ℂ => gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ)
      (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0})
      (nhds (rho γ (M ω) (α₁ - γ / 2) α₂ α₃)) := by
  filter_upwards [gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ₂ M hM 0,
    gmc_atomless_at_root_of_isGMCOf P X hX γ hγ hγ₂ M hM 1,
    reflected_rho_ae_finite P X hX γ hγ hγ₂ M hM (α₁ - γ / 2) α₂ α₃
      hα₁ hα₂ hα₃] with ω h0 h1 hf
  exact reflected_outerMass_tendsto γ α₁ α₂ α₃ ξ (M ω) hξ hξ₁ h0 h1 hf.ne

/-- The real-valued retained mass has the same finite almost-sure limit. -/
theorem reflected_outerMass_real_ae_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X) (γ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ ξ : ℝ) (hξ : 0 < ξ) (hξ₁ : ξ < 1)
    (hα₁ : α₁ - γ / 2 < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) :
    ∀ᵐ ω ∂P, Tendsto
      (fun z : ℂ => (gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ).toReal)
      (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0})
      (nhds (rho γ (M ω) (α₁ - γ / 2) α₂ α₃).toReal) := by
  filter_upwards [reflected_outerMass_ae_tendsto P X hX γ hγ hγ₂ M hM
    α₁ α₂ α₃ ξ hξ hξ₁ hα₁ hα₂ hα₃,
    reflected_rho_ae_finite P X hX γ hγ hγ₂ M hM (α₁ - γ / 2) α₂ α₃
      hα₁ hα₂ hα₃] with ω ht hf
  exact (ENNReal.tendsto_toReal hf.ne).comp ht

end DOZZ.Proofs

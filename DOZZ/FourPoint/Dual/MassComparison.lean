/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.Kernel
public import DOZZ.FourPoint.Dual.OuterMassLimit
public import DOZZ.FourPoint.Dual.NegativePowerDifference
import Mathlib.Tactic
/-! # The actual retained dual mass and its zero-mass comparison -/
public section
open MeasureTheory Set
namespace DOZZ.Proofs

/-- The dual density is nonnegative, including its prescribed root values. -/
theorem dual_kernel_nonneg (γ α₁ α₂ α₃ : ℝ) (z x : ℂ) :
    0 ≤ dualFusionKernel γ α₁ α₂ α₃ z x := by
  unfold dualFusionKernel
  exact div_nonneg
    (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      (Real.rpow_nonneg (by unfold normPlus; positivity) _))
    (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _))

/-- Integrability of the zero density implies integrability of the actual retained density. -/
theorem dual_retained_mass_integrable (γ α₁ α₂ α₃ ξ : ℝ) (hγ : γ ≠ 0)
    (z : ℂ) (μ : Measure ℂ) (hsep : ‖z‖ ≤ ‖z‖ ^ (1 - ξ))
    (hzero : Integrable (dualFusionKernel γ α₁ α₂ α₃ 0) μ) :
    Integrable (dualFusionKernel γ α₁ α₂ α₃ z)
      (μ.restrict {x : ℂ | ‖z‖ ^ (1 - ξ) ≤ ‖x‖}) := by
  apply (hzero.restrict.const_mul 4).mono'
    (dual_kernel_measurable γ α₁ α₂ α₃ z).aestronglyMeasurable
  filter_upwards [ae_restrict_mem
    (isClosed_le continuous_const continuous_norm).measurableSet] with x hx
  rw [Real.norm_of_nonneg (dual_kernel_nonneg γ α₁ α₂ α₃ z x)]
  simpa only [Real.rpow_two, show (2 : ℝ) ^ 2 = 4 by norm_num] using
    dual_kernel_outer_bound γ α₁ α₂ α₃ hγ z x (hsep.trans hx)

/-- The actual retained mass is at most four times the full zero mass. -/
theorem dual_retained_mass_le_four_zero (γ α₁ α₂ α₃ ξ : ℝ) (hγ : γ ≠ 0)
    (z : ℂ) (μ : Measure ℂ) (hsep : ‖z‖ ≤ ‖z‖ ^ (1 - ξ))
    (hzero : Integrable (dualFusionKernel γ α₁ α₂ α₃ 0) μ) :
    (∫ x in {x : ℂ | ‖z‖ ^ (1 - ξ) ≤ ‖x‖}, dualFusionKernel γ α₁ α₂ α₃ z x ∂μ) ≤
      4 * ∫ x, dualFusionKernel γ α₁ α₂ α₃ 0 x ∂μ := by
  have hz := dual_retained_mass_integrable γ α₁ α₂ α₃ ξ hγ z μ hsep hzero
  calc
    _ ≤ ∫ x in {x : ℂ | ‖z‖ ^ (1 - ξ) ≤ ‖x‖}, 4 * dualFusionKernel γ α₁ α₂ α₃ 0 x ∂μ := by
      apply integral_mono_ae hz (hzero.restrict.const_mul 4)
      filter_upwards [ae_restrict_mem
        (isClosed_le continuous_const continuous_norm).measurableSet] with x hx
      simpa only [Real.rpow_two, show (2 : ℝ) ^ 2 = 4 by norm_num] using
        dual_kernel_outer_bound γ α₁ α₂ α₃ hγ z x (hsep.trans hx)
    _ = 4 * ∫ x in {x : ℂ | ‖z‖ ^ (1 - ξ) ≤ ‖x‖}, dualFusionKernel γ α₁ α₂ α₃ 0 x ∂μ :=
      integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (setIntegral_le_integral hzero (ae_of_all _ fun x => dual_kernel_nonneg γ α₁ α₂ α₃ 0 x)) (by norm_num)

/-- The common lower mass can be chosen as one quarter of the actual retained mass. -/
theorem dual_negative_power_difference_relative (p a b : ℝ) (hp : 0 < p)
    (hb : 0 < b) (ha : b / 4 ≤ a) :
    |a ^ (-p) - b ^ (-p)| ≤
      (p * (4 : ℝ) ^ (p + 1)) * b ^ (-p - 1) * |a - b| := by
  have hl : 0 < b / 4 := div_pos hb (by norm_num)
  have hh := dual_negative_power_lipschitz p (b / 4) a b hp hl ha (by linarith only [hb])
  have he : (b / 4) ^ (-p - 1) = b ^ (-p - 1) * (4 : ℝ) ^ (p + 1) := by
    rw [Real.div_rpow hb.le (by norm_num), div_eq_mul_inv, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
    congr 2
    ring
  rw [he] at hh
  exact hh.trans_eq (by ring)


/-- The signed difference between full zero mass and retained perturbed mass is
bounded by the deleted zero mass and the retained absolute density difference. -/
theorem dual_retained_mass_difference (γ α₁ α₂ α₃ ξ : ℝ) (hγ : γ ≠ 0)
    (z : ℂ) (μ : Measure ℂ) (hsep : ‖z‖ ≤ ‖z‖ ^ (1 - ξ))
    (hzero : Integrable (dualFusionKernel γ α₁ α₂ α₃ 0) μ) :
    |(∫ x, dualFusionKernel γ α₁ α₂ α₃ 0 x ∂μ) -
      ∫ x in {x : ℂ | ‖z‖ ^ (1 - ξ) ≤ ‖x‖}, dualFusionKernel γ α₁ α₂ α₃ z x ∂μ| ≤
      (∫ x in {x : ℂ | ‖x‖ < ‖z‖ ^ (1 - ξ)}, dualFusionKernel γ α₁ α₂ α₃ 0 x ∂μ) +
        ∫ x in {x : ℂ | ‖z‖ ^ (1 - ξ) ≤ ‖x‖},
          |dualFusionKernel γ α₁ α₂ α₃ 0 x - dualFusionKernel γ α₁ α₂ α₃ z x| ∂μ := by
  let D : Set ℂ := {x | ‖z‖ ^ (1 - ξ) ≤ ‖x‖}
  have hD : MeasurableSet D := (isClosed_le continuous_const continuous_norm).measurableSet
  have hz := dual_retained_mass_integrable γ α₁ α₂ α₃ ξ hγ z μ hsep hzero
  have hdc : Dᶜ = {x : ℂ | ‖x‖ < ‖z‖ ^ (1 - ξ)} := by
    ext x
    simp only [D, mem_compl_iff, mem_ofPred_eq, not_le]
  have he : (∫ x, dualFusionKernel γ α₁ α₂ α₃ 0 x ∂μ) -
      ∫ x in D, dualFusionKernel γ α₁ α₂ α₃ z x ∂μ =
      (∫ x in Dᶜ, dualFusionKernel γ α₁ α₂ α₃ 0 x ∂μ) +
        ∫ x in D, (dualFusionKernel γ α₁ α₂ α₃ 0 x - dualFusionKernel γ α₁ α₂ α₃ z x) ∂μ := by
    rw [integral_sub hzero.restrict hz, ← integral_add_compl hD hzero]
    ring
  rw [he, ← hdc]
  apply (abs_add_le _ _).trans
  have hn : 0 ≤ ∫ x in Dᶜ, dualFusionKernel γ α₁ α₂ α₃ 0 x ∂μ :=
    integral_nonneg fun x => dual_kernel_nonneg γ α₁ α₂ α₃ 0 x
  rw [abs_of_nonneg hn]
  apply add_le_add le_rfl
  simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
    (μ := μ.restrict D) (fun x => dualFusionKernel γ α₁ α₂ α₃ 0 x - dualFusionKernel γ α₁ α₂ α₃ z x)


end DOZZ.Proofs

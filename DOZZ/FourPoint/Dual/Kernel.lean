/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.BPZ.Weight
public import DOZZ.FourPoint.Reflected.OuterKernelLimit
import Mathlib.Tactic

/-! # The actual dual fusion kernel

The deterministic weight Kᵈ of the dual fusion. Deterministic half-charge kernel estimates can be
reused at parameter 2 after scaling the charges; this identity makes no claim that the supplied
chaos has parameter 2.
-/

@[expose] public section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace DOZZ.Proofs

/-- The source dual kernel, including its prescribed totalized root values. -/
noncomputable def dualFusionKernel (γ α₁ α₂ α₃ : ℝ) (z x : ℂ) : ℝ :=
  ‖x - z‖ ^ (2 : ℝ) * normPlus x ^ (γ * (α₁ + α₂ + α₃ - 2 / γ)) /
    (‖x‖ ^ (γ * α₁) * ‖x - 1‖ ^ (γ * α₂))

/-- Scaling the charges identifies the dual kernel with the deterministic parameter-2 kernel. -/
theorem dual_kernel_eq_scaled_half (γ α₁ α₂ α₃ : ℝ) (hγ : γ ≠ 0) (z x : ℂ) :
    dualFusionKernel γ α₁ α₂ α₃ z x =
      gammaHalfKernel 2 (γ * α₁ / 2) (γ * α₂ / 2) (γ * α₃ / 2) z x := by
  unfold dualFusionKernel gammaHalfKernel
  have he : γ * (α₁ + α₂ + α₃ - 2 / γ) =
      2 * (γ * α₁ / 2 + γ * α₂ / 2 + γ * α₃ / 2 - 2 / 2) := by
    field_simp
  rw [he, show 2 * (γ * α₁ / 2) = γ * α₁ by ring,
    show 2 * (γ * α₂ / 2) = γ * α₂ by ring]
  norm_num

/-- The dual kernel is the literal unsoftened BPZ density including its prescribed root values. -/
theorem dual_kernel_eq_bpzWeight (γ α₁ α₂ α₃ : ℝ) (hγ : γ ≠ 0) (z x : ℂ) :
    dualFusionKernel γ α₁ α₂ α₃ z x = bpzSoftWeight γ (2 / γ) α₁ α₂ α₃ 0 z x := by
  have he : γ * (2 / γ) / 2 = 1 := by field_simp
  unfold dualFusionKernel bpzSoftWeight bpzBaseWeight
  rw [he]
  simp only [zero_pow (by norm_num : 2 ≠ 0), add_zero, Real.rpow_one,
    Real.rpow_two, Real.rpow_neg (norm_nonneg x), Real.rpow_neg (norm_nonneg (x - 1)),
    Complex.normSq_eq_norm_sq]
  ring

/-- The actual dual kernel mass is the supplied Coulomb mass, with root values removed by atomlessness. -/
theorem dual_kernel_integral_eq_coulombMass (γ α₁ α₂ α₃ : ℝ) (hγ : γ ≠ 0)
    (z : ℂ) (μ : Measure ℂ) (hz : μ {z} = 0) (h0 : μ {0} = 0) (h1 : μ {1} = 0) :
    (∫⁻ x, ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂μ) =
      coulombMass γ μ ![-2 / γ, α₁, α₂] ![z, 0, 1] α₃ := by
  simp only [dual_kernel_eq_bpzWeight γ α₁ α₂ α₃ hγ]
  simpa only [neg_div] using (coulombMass_eq_lintegral_bpzSoftWeight (γ := γ) (χ := 2 / γ)
    (α₁ := α₁) (α₂ := α₂) (α₃ := α₃) μ z hz h0 h1).symm

/-- The zero density has the exact shifted first charge. -/
theorem dual_zero_kernel_weight (γ α₁ α₂ α₃ : ℝ) (hγ : γ ≠ 0) (x : ℂ)
    (hx : x ≠ 0) (hx1 : x ≠ 1) :
    dualFusionKernel γ α₁ α₂ α₃ 0 x =
      normPlus x ^ (γ * ((α₁ - 2 / γ) + α₂ + α₃)) /
        (‖x‖ ^ (γ * (α₁ - 2 / γ)) * ‖x - 1‖ ^ (γ * α₂)) := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hx1pos : 0 < ‖x - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx1)
  have he : 2 + γ * (α₁ - 2 / γ) = γ * α₁ := by field_simp; ring
  have hprod := Real.rpow_add hxpos 2 (γ * (α₁ - 2 / γ))
  rw [he] at hprod
  unfold dualFusionKernel
  rw [sub_zero, hprod,
    show α₁ + α₂ + α₃ - 2 / γ = (α₁ - 2 / γ) + α₂ + α₃ by ring]
  have h0 := (Real.rpow_pos_of_pos hxpos 2).ne'
  have h1 := (Real.rpow_pos_of_pos hxpos (γ * (α₁ - 2 / γ))).ne'
  have h2 := (Real.rpow_pos_of_pos hx1pos (γ * α₂)).ne'
  field_simp

/-- No parameter-2 GMC input is used when transferring outer density domination. -/
theorem dual_kernel_outer_bound (γ α₁ α₂ α₃ : ℝ) (hγ : γ ≠ 0) (z x : ℂ)
    (hsep : ‖z‖ ≤ ‖x‖) :
    dualFusionKernel γ α₁ α₂ α₃ z x ≤ 4 * dualFusionKernel γ α₁ α₂ α₃ 0 x := by
  rw [dual_kernel_eq_scaled_half γ α₁ α₂ α₃ hγ z x,
    dual_kernel_eq_scaled_half γ α₁ α₂ α₃ hγ 0 x]
  have hb := reflected_outer_kernel_bound 2 (γ * α₁ / 2) (γ * α₂ / 2)
    (γ * α₃ / 2) z x hsep
  norm_num [Real.rpow_two] at hb
  exact hb

/-- Measurability of the literal dual density, including its root values. -/
theorem dual_kernel_measurable (γ α₁ α₂ α₃ : ℝ) (z : ℂ) :
    Measurable (fun x => dualFusionKernel γ α₁ α₂ α₃ z x) := by
  unfold dualFusionKernel normPlus
  fun_prop

/-- Dominated removal of the retained cutoff for the actual dual kernel. -/
theorem dual_outer_kernel_integral_tendsto (γ α₁ α₂ α₃ ξ : ℝ) (hγ : γ ≠ 0)
    (μ : Measure ℂ) (hξ : 0 < ξ) (hξ₁ : ξ < 1) (h0 : μ {0} = 0)
    (hfin : (∫⁻ x, ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ 0 x) ∂μ) ≠ ⊤) :
    Tendsto (fun z : ℂ => ∫⁻ x in {x : ℂ | ‖z‖ ^ (1 - ξ) ≤ ‖x‖},
      ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂μ)
      (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0})
      (nhds (∫⁻ x, ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ 0 x) ∂μ)) := by
  simp only [dual_kernel_eq_scaled_half γ α₁ α₂ α₃ hγ] at hfin ⊢
  exact reflected_outer_kernel_integral_tendsto 2 (γ * α₁ / 2) (γ * α₂ / 2)
    (γ * α₃ / 2) ξ μ hξ hξ₁ h0 hfin

end DOZZ.Proofs

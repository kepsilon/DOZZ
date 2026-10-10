/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.OuterKernel
public import DOZZ.GMC.SharpMoments.SeibergWeight
import Mathlib.Tactic
/-! The literal inner kernel is squeezed between the two radial Williams weights. -/
@[expose] public section
open Filter Topology
namespace DOZZ.Proofs

/-- Uniform bounds for the actual half-charge kernel in the inner fusion disk. The root at
one contributes a factor tending to one with the disk radius. -/
theorem reflected_inner_kernel_squeeze (γ α₁ α₂ α₃ R η : ℝ) (z x : ℂ)
    (hR : 0 ≤ R) (hR₁ : R < 1) (hη : 0 ≤ η) (hη₁ : η < 1)
    (hz : 0 < ‖z‖) (hx : 0 < ‖x‖)
    (hsep : ‖x‖ ≤ R * ‖z‖) (hsmall : ‖x‖ ≤ η) :
    ((1 - R) ^ (γ ^ 2 / 2) * (1 - η)⁻¹ ^ (-|γ * α₂|)) *
        (‖z‖ ^ (γ ^ 2 / 2) * ‖x‖ ^ (-(γ * α₁))) ≤
      gammaHalfKernel γ α₁ α₂ α₃ z x ∧
    gammaHalfKernel γ α₁ α₂ α₃ z x ≤
      ((1 + R) ^ (γ ^ 2 / 2) * (1 - η)⁻¹ ^ |γ * α₂|) *
        (‖z‖ ^ (γ ^ 2 / 2) * ‖x‖ ^ (-(γ * α₁))) := by
  have hk : 0 ≤ γ ^ 2 / 2 := by positivity
  have hηp : 0 < 1 - η := by linarith
  have hL : 1 ≤ (1 - η)⁻¹ := by
    rw [one_le_inv₀ hηp]
    linarith
  have hd1 : (1 - η) ≤ ‖x - 1‖ := by
    have hh := norm_sub_norm_le (1 : ℂ) x
    rw [norm_one, norm_sub_rev] at hh
    linarith
  have hd2 : ‖x - 1‖ ≤ (1 - η)⁻¹ := by
    have hh := norm_sub_le x (1 : ℂ)
    rw [norm_one] at hh
    apply hh.trans
    rw [← one_div]
    apply (le_div_iff₀ hηp).mpr
    nlinarith [sq_nonneg η]
  have hbase : 0 < ‖x - 1‖ := hηp.trans_le hd1
  have hlo := coulombWeight_le_rpow hL (by simpa only [inv_inv] using hd1) hd2
    (-(γ * α₂))
  have hup := coulombWeight_rpow_le hL (by simpa only [inv_inv] using hd1) hd2
    (-(γ * α₂))
  simp only [abs_neg] at hlo hup
  have hdistlo : (1 - R) * ‖z‖ ≤ ‖x - z‖ := by
    have hh := norm_sub_norm_le z x
    rw [norm_sub_rev] at hh
    nlinarith only [hh, hsep]
  have hdisthi : ‖x - z‖ ≤ (1 + R) * ‖z‖ := by
    have hh := norm_sub_le x z
    nlinarith only [hh, hsep]
  have hpowlo := Real.rpow_le_rpow (by positivity : 0 ≤ (1-R)*‖z‖) hdistlo hk
  have hpowhi := Real.rpow_le_rpow (norm_nonneg (x-z)) hdisthi hk
  rw [Real.mul_rpow (by linarith : 0 ≤ 1-R) hz.le] at hpowlo
  rw [Real.mul_rpow (by positivity : 0 ≤ 1+R) hz.le] at hpowhi
  have heq : gammaHalfKernel γ α₁ α₂ α₃ z x =
      ‖x-z‖ ^ (γ^2/2) * ‖x‖ ^ (-(γ*α₁)) * ‖x-1‖ ^ (-(γ*α₂)) := by
    unfold gammaHalfKernel normPlus
    rw [max_eq_left (hsmall.trans hη₁.le), Real.one_rpow, mul_one,
      Real.rpow_neg hx.le, Real.rpow_neg hbase.le]
    ring
  rw [heq]
  constructor
  · have hh := mul_le_mul_of_nonneg_right hpowlo (Real.rpow_nonneg hx.le (-(γ*α₁)))
    have hh' := mul_le_mul hh hlo (by positivity) (by positivity)
    calc
      _ = ((1-R) ^ (γ^2/2) * ‖z‖ ^ (γ^2/2) * ‖x‖ ^ (-(γ*α₁))) *
        (1-η)⁻¹ ^ (-|γ*α₂|) := by ring
      _ ≤ _ := hh'
  · have hh := mul_le_mul_of_nonneg_right hpowhi (Real.rpow_nonneg hx.le (-(γ*α₁)))
    have hh' := mul_le_mul hh hup (by positivity) (by positivity)
    calc
      _ ≤ ((1+R) ^ (γ^2/2) * ‖z‖ ^ (γ^2/2) * ‖x‖ ^ (-(γ*α₁))) *
        (1-η)⁻¹ ^ |γ*α₂| := hh'
      _ = _ := by ring

/-- The extra factor from the root at one vanishes in the first, insertion-point limit. -/
theorem reflected_inner_root_factor_limit (R e : ℝ) :
    Tendsto (fun z : ℂ => (1 - R * ‖z‖)⁻¹ ^ e) (𝓝 0) (𝓝 1) := by
  have hn : Tendsto (fun z : ℂ => ‖z‖) (𝓝 0) (𝓝 0) := by
    simpa only [norm_zero] using (continuous_norm.tendsto (0 : ℂ))
  have hb : Tendsto (fun z : ℂ => 1 - R * ‖z‖) (𝓝 0) (𝓝 1) := by
    simpa only [mul_zero, sub_zero] using tendsto_const_nhds.sub (hn.const_mul R)
  have hi := hb.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  simpa only [inv_one, Real.one_rpow] using hi.rpow_const (p := e) (Or.inl (by norm_num))

/-- Both scalar bounds approach one in the final large-buffer limit. -/
theorem reflected_inner_scalar_squeeze_limit (γ : ℝ) :
    Tendsto (fun h : ℝ => ((1 - Real.exp (-h)) ^ (γ ^ 2 / 2),
      (1 + Real.exp (-h)) ^ (γ ^ 2 / 2))) atTop (𝓝 (1, 1)) := by
  have he := Real.tendsto_exp_neg_atTop_nhds_zero
  have hm : Tendsto (fun h : ℝ => 1 - Real.exp (-h)) atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub he
  have hp : Tendsto (fun h : ℝ => 1 + Real.exp (-h)) atTop (𝓝 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add he
  simpa only [Real.one_rpow] using
    (hm.rpow_const (p := γ ^ 2 / 2) (Or.inl (by norm_num))).prodMk_nhds
      (hp.rpow_const (p := γ ^ 2 / 2) (Or.inl (by norm_num)))

end DOZZ.Proofs

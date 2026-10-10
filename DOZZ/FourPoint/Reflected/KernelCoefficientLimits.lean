/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.InnerKernelSqueeze
/-! Ordered spatial and depth limits of the two literal kernel coefficients. -/
@[expose] public section
open Filter Topology
namespace DOZZ.Proofs

theorem reflected_kernel_coefficient_spatial_limits (γ α h : ℝ) :
    Tendsto (fun z : ℂ => max 1 ((1+Real.exp (-h))^(γ^2/2)*
      (1-Real.exp (-h)*‖z‖)⁻¹^|γ*α|)) (𝓝 0) (𝓝 (max 1 ((1+Real.exp (-h))^(γ^2/2)))) ∧
    Tendsto (fun z : ℂ => min 1 ((1-Real.exp (-h))^(γ^2/2)*
      (1-Real.exp (-h)*‖z‖)⁻¹^(-|γ*α|))) (𝓝 0) (𝓝 (min 1 ((1-Real.exp (-h))^(γ^2/2)))) := by
  have hi := (reflected_inner_root_factor_limit (Real.exp (-h)) |γ*α|).const_mul
    ((1+Real.exp (-h))^(γ^2/2))
  have hl := (reflected_inner_root_factor_limit (Real.exp (-h)) (-|γ*α|)).const_mul
    ((1-Real.exp (-h))^(γ^2/2))
  constructor
  · simpa only [mul_one] using (tendsto_const_nhds (x := (1 : ℝ))).max hi
  · simpa only [mul_one] using (tendsto_const_nhds (x := (1 : ℝ))).min hl

theorem reflected_kernel_coefficient_depth_limit (γ : ℝ) :
    Tendsto (fun h : ℝ => (max 1 ((1+Real.exp (-h))^(γ^2/2)),
      min 1 ((1-Real.exp (-h))^(γ^2/2)))) atTop (𝓝 (1,1)) := by
  have h := reflected_inner_scalar_squeeze_limit γ
  simpa only [max_self,min_self] using
    ((tendsto_const_nhds (x := (1 : ℝ))).max h.snd_nhds).prodMk_nhds
      ((tendsto_const_nhds (x := (1 : ℝ))).min h.fst_nhds)

end DOZZ.Proofs

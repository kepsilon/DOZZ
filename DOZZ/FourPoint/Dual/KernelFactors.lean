/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
/-! The literal inner-kernel factors converge in the prescribed spatial/buffer order. -/
@[expose] public section
open Filter Topology
namespace DOZZ.Proofs

/-- At fixed radial buffer, the origin-distance factor tends to one. -/
theorem dual_inner_kernel_factor_spatial_tendsto (R a h : ℝ) :
    Tendsto (fun z : ℂ => (1+R)^(2 : ℝ)*
      (1-Real.exp (-h)*‖z‖)⁻¹^a) (𝓝[≠] (0 : ℂ)) (𝓝 ((1+R)^(2 : ℝ))) := by
  have hn : Tendsto (fun z : ℂ => ‖z‖) (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℝ)) := by
    simpa only [norm_zero] using (continuous_norm.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
  have hbase := (tendsto_const_nhds.sub (hn.const_mul (Real.exp (-h)))).inv₀
    (by norm_num : (1 : ℝ)-Real.exp (-h)*0 ≠ 0)
  have hp := (Real.continuousAt_rpow_const 1 a (Or.inl one_ne_zero)).tendsto
  have hb : Tendsto (fun z : ℂ => (1-Real.exp (-h)*‖z‖)⁻¹) (𝓝[≠] (0 : ℂ)) (𝓝 (1 : ℝ)) := by
    simpa only [mul_zero, sub_zero, inv_one] using hbase
  simpa only [Real.one_rpow, mul_one, Function.comp_def] using (hp.comp hb).const_mul ((1+R)^(2 : ℝ))

/-- After the spatial limit, both relative kernel factors approach one as the buffer grows. -/
theorem dual_inner_kernel_factor_buffer_tendsto (s : ℝ) :
    Tendsto (fun h : ℝ => (1+s*Real.exp (-h))^(2 : ℝ)) atTop (𝓝 (1 : ℝ)) := by
  have he : Tendsto (fun h : ℝ => Real.exp (-h)) atTop (𝓝 (0 : ℝ)) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have hb := (tendsto_const_nhds (x := (1 : ℝ))).add (he.const_mul s)
  have hp := (Real.continuousAt_rpow_const 1 2 (Or.inl one_ne_zero)).tendsto
  have hb' : Tendsto (fun h : ℝ => 1+s*Real.exp (-h)) atTop (𝓝 (1 : ℝ)) := by
    simpa only [mul_zero, add_zero] using hb
  simpa only [Real.one_rpow, Function.comp_def] using hp.comp hb'

/-- The integrated relative-error constant has its literal fixed-buffer spatial limit. -/
theorem dual_inner_kernel_relative_error_spatial_tendsto (γ α h : ℝ) :
    Tendsto (fun z : ℂ => max
      |(1-Real.exp (-h))^(2 : ℝ)*(1-Real.exp (-h)*‖z‖)⁻¹^(-|γ*α|)-1|
      |(1+Real.exp (-h))^(2 : ℝ)*(1-Real.exp (-h)*‖z‖)⁻¹^|γ*α|-1|)
      (𝓝[≠] (0 : ℂ)) (𝓝 (max |(1-Real.exp (-h))^(2 : ℝ)-1|
        |(1+Real.exp (-h))^(2 : ℝ)-1|)) := by
  have hlo := dual_inner_kernel_factor_spatial_tendsto (-Real.exp (-h)) (-|γ*α|) h
  have hhi := dual_inner_kernel_factor_spatial_tendsto (Real.exp (-h)) |γ*α| h
  simpa only [sub_eq_add_neg] using
    ((hlo.sub (tendsto_const_nhds (x := (1 : ℝ)))).abs).max ((hhi.sub (tendsto_const_nhds (x := (1 : ℝ)))).abs)

/-- The fixed-buffer relative error tends to zero after the spatial limit. -/
theorem dual_inner_kernel_relative_error_buffer_tendsto :
    Tendsto (fun h : ℝ => max |(1-Real.exp (-h))^(2 : ℝ)-1|
      |(1+Real.exp (-h))^(2 : ℝ)-1|) atTop (𝓝 (0 : ℝ)) := by
  have hlo := dual_inner_kernel_factor_buffer_tendsto (-1)
  have hhi := dual_inner_kernel_factor_buffer_tendsto 1
  simpa only [neg_one_mul, one_mul, sub_eq_add_neg, sub_self, add_neg_cancel, abs_zero, max_self] using
    ((hlo.sub (tendsto_const_nhds (x := (1 : ℝ)))).abs).max ((hhi.sub (tendsto_const_nhds (x := (1 : ℝ)))).abs)

end DOZZ.Proofs

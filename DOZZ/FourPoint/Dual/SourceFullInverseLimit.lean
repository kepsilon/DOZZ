/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.SourceCopiedInverseBound
public import DOZZ.FourPoint.Dual.SourceCopiedPolarLimit
public import DOZZ.FourPoint.Dual.BufferRelativeLimit
public import DOZZ.FourPoint.Dual.KernelFactors
public import DOZZ.FourPoint.Dual.OuterLittleO
import Mathlib.Tactic
/-! The actual full dual inverse expectation has the same-witness stochastic fusion coefficient. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Assemble the actual full-to-copied error, retained outer correction, copied polar limit
and literal kernel squeeze, then remove the radial buffer after the spatial limit. -/
theorem dual_source_full_inverse_increment_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (α₁ α₂ α₃ ξ : ℝ) (hα₁ : α₁ < Q γ) (hreflect : Q γ-α₁ < γ/2)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2*Q γ+2/γ < α₁+α₂+α₃)
    (hshifted : 2*Q γ-α₁-2/γ < Q γ)
    (hslack : (4/γ)*(Q γ-α₁) < 2+γ*(Q γ-α₁)-γ^2/2) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (hβ : γ*α₁ < 4)
    (hκξ : (4/γ)*(Q γ-α₁) < ξ)
    (hspatial : (4/γ)*(Q γ-α₁) < (1-ξ)*(4-γ*α₁))
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α₁ B Z)
    (hiZ : IndepFun (originRadialPath Xc) Z P)
    (heZ : Z =ᵐ[P] (fun ω => lateralProjectedGMC γ (originRadialPath Xc ω) (M ω))) :
    let ν := Q γ-α₁
    let a := 2*ν/γ
    let p := (α₁+α₂+α₃-2/γ-2*Q γ)/γ
    Tendsto (fun z : ℂ =>
      ((∫⁻ ω, (∫⁻ x, ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂M ω)^(-p) ∂P).toReal-
        (∫⁻ ω, coulombMass γ (M ω) ![-2/γ,α₁,α₂] ![0,0,1] α₃^(-p) ∂P).toReal)/
          ‖z‖^((4/γ)*ν)) (𝓝[≠] (0 : ℂ))
      (𝓝 ((a*Real.Gamma (-a)*Real.Gamma (p+a)/Real.Gamma p)*
        (∫⁻ ω, rho γ (M ω) (2*Q γ-α₁-2/γ) α₂ α₃^(-(p+a)) ∂P).toReal*
        (∫⁻ ω, twoSidedReflectionMass γ B Z ω^a ∂P).toReal)) := by
  let _ : IsProbabilityMeasure P := hX.1
  let ν := Q γ-α₁
  let a := 2*ν/γ
  let p := (α₁+α₂+α₃-2/γ-2*Q γ)/γ
  let κ := (4/γ)*ν
  have hp : 0 < p := div_pos (by linarith only [hs]) hγ
  have hαshift : α₁-2/γ < Q γ := by linarith only [hα₁, div_pos (by norm_num : (0 : ℝ) < 2) hγ]
  let W := fun h : ℝ => dual_full_copied_path_law_carrier P X Xc hX hc hm hcont γ hγ hγ₂ M hM
    α₁ α₂ α₃ p h ξ κ hp hα₁ hα₂ hα₃ hβ hspatial hξ hξ1 hκξ
  let N := fun h => Classical.choose (W h)
  have hN (h : ℝ) := Classical.choose_spec (W h)
  let A := originRadialPath Xc
  let T := fun h (z : ℂ) => Real.toNNReal (-Real.log ‖z‖+h)
  let O := fun h z (v : Ω × Ω) => ∫⁻ x in reflected_outerRegion (‖z‖^(1-ξ)),
    ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x)*
      ENNReal.ofReal (reflected_global_reinsertionWeight γ (A v.1) x) ∂N h v.2
  let D := fun h z => ∫ v : (Ω × Ω) × Ω,
    ((O h z v.1).toReal+dualPathRadialScale γ ν h z (A v.1.1)*
      (∫⁻ t, (if 0 < t then ENNReal.ofReal (Real.exp (γ*
        (brownianShiftPath (T h z) (radialPositiveHalf (A v.1.1)) (Real.toNNReal t)-ν*t))) else 0)
          ∂(Z v.2).map (fun s => s-(T h z : ℝ))).toReal)^(-p)-(O h z v.1).toReal^(-p)
      ∂(P.prod P).prod P
  let full := fun z : ℂ => (∫⁻ ω, (∫⁻ x,
    ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂M ω)^(-p) ∂P).toReal
  let outer := fun z : ℂ => (∫⁻ ω, dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ^(-p) ∂P).toReal
  let zero := (∫⁻ ω, coulombMass γ (M ω) ![-2/γ,α₁,α₂] ![0,0,1] α₃^(-p) ∂P).toReal
  let copied := fun h z => (dualCopiedSeparatedInverseMoment P Xc (N h) γ α₁ α₂ α₃ p z
    (Real.exp (-h)*‖z‖) (‖z‖^(1-ξ))).toReal
  let f := fun z : ℂ => (full z-zero)/‖z‖^κ
  let g := fun h z => D h z/‖z‖^κ
  let d := fun h z => |(full z-copied h z)/‖z‖^κ|+|(outer z-zero)/‖z‖^κ|
  let e := fun h (z : ℂ) => max
    |(1-Real.exp (-h))^(2 : ℝ)*(1-Real.exp (-h)*‖z‖)⁻¹^(-|γ*α₂|)-1|
    |(1+Real.exp (-h))^(2 : ℝ)*(1-Real.exp (-h)*‖z‖)⁻¹^|γ*α₂|-1|
  let C := fun h => max |(1-Real.exp (-h))^(2 : ℝ)-1| |(1+Real.exp (-h))^(2 : ℝ)-1|
  let L := (a*Real.Gamma (-a)*Real.Gamma (p+a)/Real.Gamma p)*
    (∫⁻ ω, rho γ (M ω) (2*Q γ-α₁-2/γ) α₂ α₃^(-(p+a)) ∂P).toReal*
    (∫⁻ ω, twoSidedReflectionMass γ B Z ω^a ∂P).toReal
  have hg (h : ℝ) (hh : 0 < h) : Tendsto (g h) (𝓝[≠] (0 : ℂ)) (𝓝 L) :=
    dual_source_copied_polar_increment_tendsto P X hX γ hγ hγ₂ M hM Xc hc hm hcont
      (N h) (hN h).1 (hN h).2.2.1 (hN h).2.2.2.2.1 α₁ α₂ α₃ ξ h
      hα₁ hreflect hα₂ hα₃ hh.le hs hshifted hslack hξ hξ1 B Z hData hiZ
  have htOuter : Tendsto (fun z : ℂ => (outer z-zero)/‖z‖^κ) (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
    dual_outer_inverse_moment_littleO P X M γ α₁ α₂ α₃ p ξ κ hγ hγ₂ hp
      hαshift hα₂ hα₃ hβ hξ hξ1 hκξ hspatial hX hM
  have hd (h : ℝ) (_hh : 0 < h) : Tendsto (d h) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    simpa only [abs_zero, zero_add] using ((hN h).2.2.2.2.2.abs).add htOuter.abs
  have he (h : ℝ) (_hh : 0 < h) : Tendsto (e h) (𝓝[≠] (0 : ℂ)) (𝓝 (C h)) :=
    dual_inner_kernel_relative_error_spatial_tendsto γ α₂ h
  apply dual_buffer_relative_squeeze_tendsto (𝓝[≠] (0 : ℂ)) f g d e C L hg hd he
    dual_inner_kernel_relative_error_buffer_tendsto
  intro h hh
  have hn : Tendsto (fun z : ℂ => ‖z‖) (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℝ)) := by
    simpa only [norm_zero] using (continuous_norm.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hn.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with z hz0 hz
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hz1 : z ≠ 1 := by intro he; simp only [he, norm_one, lt_self_iff_false] at hz
  have hstrict : ‖z‖ < ‖z‖^(1-ξ) := by
    simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_gt hzpos hz
      (by linarith only [hξ] : 1-ξ < 1)
  have htime : 0 ≤ -Real.log ‖z‖+h := by
    have hl := Real.log_nonpos hzpos.le hz.le
    linarith only [hl, hh]
  have hT : (T h z : ℝ) = -Real.log ‖z‖+h := Real.coe_toNNReal _ htime
  have hηEq : Real.exp (-(T h z : ℝ)) = Real.exp (-h)*‖z‖ := by
    rw [hT]
    have he : -(-Real.log ‖z‖+h) = -h+Real.log ‖z‖ := by ring
    rw [he, Real.exp_add, Real.exp_log hzpos]
  have hR : Real.exp (-h) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hh)
  have hη : Real.exp (-(T h z : ℝ)) < 1 := by
    rw [hηEq]
    exact (mul_lt_mul_of_pos_left hz (Real.exp_pos _)).trans_le (by simpa only [mul_one] using hR.le)
  have hr : Real.exp (-(T h z : ℝ)) ≤ ‖z‖^(1-ξ) := by
    rw [hηEq]
    exact (mul_le_of_le_one_left hzpos.le hR.le).trans hstrict.le
  have hb := dual_source_copied_kernel_inverse_bound P X Xc hX hc hm hcont γ hγ hγ₂ M hM
    (N h) (hN h).1 (hN h).2.2.1 (hN h).2.2.2.1 Z hData.2.1 heZ
    α₁ α₂ α₃ ξ h p hp hh hα₁ hα₂ hα₃ hξ hξ1 z hz0 hz1 hz.le hstrict
    (T h z) hT hη hr hiZ B Z hData ((hN h).2.2.2.2.1 α₁ α₂ α₃ ξ z hstrict)
  dsimp only at hb
  rw [hηEq] at hb
  have hκpos : 0 < ‖z‖^κ := Real.rpow_pos_of_pos hzpos _
  have hb' : |(copied h z-outer z-D h z)/‖z‖^κ| ≤ e h z*(-g h z) := by
    rw [abs_div, abs_of_pos hκpos]
    apply (div_le_div_of_nonneg_right hb hκpos.le).trans_eq
    dsimp only [e, g]
    ring
  have hdecomp : f z-g h z = (full z-copied h z)/‖z‖^κ+
      (outer z-zero)/‖z‖^κ+(copied h z-outer z-D h z)/‖z‖^κ := by
    dsimp only [f, g]
    ring
  rw [hdecomp]
  exact (abs_add_le _ _).trans (add_le_add
    (abs_add_le ((full z-copied h z)/‖z‖^κ) ((outer z-zero)/‖z‖^κ)) hb')

end DOZZ.Proofs

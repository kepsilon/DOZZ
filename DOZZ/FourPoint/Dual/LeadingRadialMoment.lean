/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.SourceRadialMoments
public import DOZZ.FourPoint.Reflected.LeadingRadialMoment
import Mathlib.Tactic
/-! The normalized leading Pareto weight has the actual reflected charge-shift limit. -/
@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- On the punctured plane the exponential scale equals the literal quadratic restart. -/
theorem dual_radial_scale_eq_restart {Ω : Type*} (γ ν h : ℝ)
    (Xc : Ω → ℂ → ℝ → ℝ) (z : ℂ) (hz : z ≠ 0) (ω : Ω) :
    dual_radial_scale γ ν h Xc z ω = ‖z‖ ^ (2 : ℝ) *
      Real.exp (γ * (Xc ω 0 (-Real.log ‖z‖ + h) - ν * (-Real.log ‖z‖ + h))) := by
  unfold dual_radial_scale
  rw [Real.rpow_def_of_pos (norm_pos_iff.mpr hz), ← Real.exp_add]
  congr 1
  ring

/-- The leading source moment is an exact norm power times the circle likelihood moment. -/
theorem dual_leading_radial_moment_identity
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (γ ν h : ℝ) (hγ : γ ≠ 0) (Xc : Ω → ℂ → ℝ → ℝ)
    (F : Ω → ℝ≥0∞) (z : ℂ) (hz : z ≠ 0) :
    (∫⁻ ω, ENNReal.ofReal ((dual_radial_scale γ ν h Xc z ω)^(2*ν/γ))*F ω ∂P) =
      ENNReal.ofReal (‖z‖^((4/γ)*ν)) *
        ∫⁻ ω, ENNReal.ofReal (Real.exp
          (2*ν*Xc ω 0 (-Real.log ‖z‖+h)-(-Real.log ‖z‖+h)*(2*ν)^2/2))*F ω ∂P := by
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have he (ω : Ω) : (dual_radial_scale γ ν h Xc z ω)^(2*ν/γ) =
      ‖z‖^((4/γ)*ν)*Real.exp
        (2*ν*Xc ω 0 (-Real.log ‖z‖+h)-(-Real.log ‖z‖+h)*(2*ν)^2/2) := by
    dsimp only [dual_radial_scale]
    rw [← Real.exp_mul, Real.rpow_def_of_pos hn, ← Real.exp_add]
    congr 1
    field_simp
    ring
  simp_rw [he, ENNReal.ofReal_mul (Real.rpow_nonneg hn.le _), mul_assoc]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The normalized actual leading moment converges to the reflected rho, independently of
the fixed radial buffer. -/
theorem dual_leading_radial_moment_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (ν α₁ α₂ α₃ ξ q h : ℝ) (hh : 0 ≤ h) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hq : 0 ≤ q)
    (hα₁ : α₁+2*ν-2/γ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) :
    Tendsto (fun z : ℂ =>
      (∫⁻ ω, ENNReal.ofReal ((dual_radial_scale γ ν h Xc z ω)^(2*ν/γ))*
        dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^(-q) ∂P) /
          ENNReal.ofReal (‖z‖^((4/γ)*ν)))
      (𝓝[≠] (0 : ℂ))
      (𝓝 (∫⁻ ω, rho γ (M ω) (α₁+2*ν-2/γ) α₂ α₃ ^(-q) ∂P)) := by
  have ht := dual_tilted_outer_inverse_moment_tendsto P X hX γ hγ hγ₂ M hM Xc hc
    (2*ν) α₁ α₂ α₃ ξ q h hh hξ hξ1 hq hα₁ hα₂ hα₃
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : z ≠ 0 := hz
  rw [dual_leading_radial_moment_identity P γ ν h hγ.ne' Xc _ z hz0]
  have hp : 0 < ‖z‖^((4/γ)*ν) := Real.rpow_pos_of_pos (norm_pos_iff.mpr hz0) _
  symm
  rw [mul_comm (ENNReal.ofReal (‖z‖^((4/γ)*ν)))]
  exact ENNReal.mul_div_cancel_right (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top

/-- The normalized leading Pareto expectation has its genuine finite real limit. -/
theorem dual_leading_radial_moment_toReal_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (ν α₁ α₂ α₃ ξ q h : ℝ) (hh : 0 ≤ h) (hξ : 0 < ξ) (hξ1 : ξ < 1) (hq : 0 ≤ q)
    (hα₁ : α₁+2*ν-2/γ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) :
    Tendsto (fun z : ℂ =>
      (∫⁻ ω, ENNReal.ofReal ((dual_radial_scale γ ν h Xc z ω)^(2*ν/γ))*
        dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^(-q) ∂P).toReal / ‖z‖^((4/γ)*ν))
      (𝓝[≠] (0 : ℂ))
      (𝓝 (∫⁻ ω, rho γ (M ω) (α₁+2*ν-2/γ) α₂ α₃ ^(-q) ∂P).toReal) := by
  have ht := dual_leading_radial_moment_tendsto P X hX γ hγ hγ₂ M hM Xc hc
    ν α₁ α₂ α₃ ξ q h hh hξ hξ1 hq hα₁ hα₂ hα₃
  have hf := reflected_rho_inverse_expectation_lt_top P X hX γ hγ hγ₂ M hM
    (α₁+2*ν-2/γ) α₂ α₃ q hq
  have hr := (ENNReal.tendsto_toReal hf.ne).comp ht
  simpa only [Function.comp_def, ENNReal.toReal_div, ENNReal.toReal_ofReal (Real.rpow_nonneg (norm_nonneg _) _)] using hr

end DOZZ.Proofs

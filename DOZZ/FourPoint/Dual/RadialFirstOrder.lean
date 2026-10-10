/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.RadialLikelihood
public import DOZZ.FourPoint.Reflected.Remainder
import Mathlib.Tactic
/-! # The first-order restart error is negligible at the dual fusion scale -/
public section
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The actual first-order restart-weighted inverse moment has deterministic power
2+γ(Q−α₁)−γ²/2. The estimate uses the supplied GMC under its exact circle tilt. -/
theorem dual_radial_first_order_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (α₁ α₂ α₃ ξ q h : ℝ) (hh : 0 ≤ h) (hξ : 0 < ξ) (hξ₁ : ξ < 1) (hq : 0 ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ z : ℂ in nhdsWithin 0 {z : ℂ | z ≠ 0},
      (∫⁻ ω, ENNReal.ofReal (‖z‖ ^ (2 : ℝ) * Real.exp
        (γ * (Xc ω 0 (-Real.log ‖z‖ + h) -
          (Q γ - α₁) * (-Real.log ‖z‖ + h)))) *
          dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^ (-q) ∂P) ≤
            ENNReal.ofReal (C * ‖z‖ ^ (2 + γ * (Q γ - α₁) - γ ^ 2 / 2)) := by
  obtain ⟨C₀, hC₀, hb⟩ := dual_outerMass_inverse_moment_uniform
    P X hX γ hγ hγ₂ M hM (α₁ + γ) α₂ α₃ q hq
  let D := Real.exp ((γ ^ 2 / 2 - γ * (Q γ - α₁)) * h)
  refine ⟨D * C₀, mul_pos (Real.exp_pos _) hC₀, ?_⟩
  have hn : Tendsto (fun z : ℂ => ‖z‖)
      (nhdsWithin 0 {z : ℂ | z ≠ 0}) (nhds 0) := by
    simpa only [norm_zero] using (continuous_norm.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds
  filter_upwards [hn.eventually (gt_mem_nhds zero_lt_one), self_mem_nhdsWithin] with z hz hz0
  have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hm : 0 ≤ -Real.log ‖z‖ + h := by
    have hl := Real.log_nonpos hp.le hz.le
    linarith only [hl, hh]
  have hr : ‖z‖ ≤ ‖z‖ ^ (1 - ξ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hp hz.le
      (by linarith only [hξ] : 1 - ξ ≤ 1)
  have hout : Real.exp (-(-Real.log ‖z‖ + h)) ≤ ‖z‖ ^ (1 - ξ) := by
    apply le_trans _ hr
    have he : -(-Real.log ‖z‖ + h) ≤ Real.log ‖z‖ := by linarith only [hh]
    simpa only [Real.exp_log hp] using Real.exp_le_exp.mpr he
  have he (ω : Ω) : ‖z‖ ^ (2 : ℝ) * Real.exp
      (γ * (Xc ω 0 (-Real.log ‖z‖ + h) - (Q γ - α₁) * (-Real.log ‖z‖ + h))) =
      (D * ‖z‖ ^ (2 + γ * (Q γ - α₁) - γ ^ 2 / 2)) *
        Real.exp (γ * Xc ω 0 (-Real.log ‖z‖ + h) -
          (-Real.log ‖z‖ + h) * γ ^ 2 / 2) := by
    dsimp only [D]
    rw [Real.rpow_def_of_pos hp, Real.rpow_def_of_pos hp]
    simp only [← Real.exp_add]
    congr 1
    ring
  have hs : 0 ≤ D * ‖z‖ ^ (2 + γ * (Q γ - α₁) - γ ^ 2 / 2) := by
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hp.le _)
  simp_rw [he, ENNReal.ofReal_mul hs, mul_assoc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have ht := dual_outerMass_circle_tilt P X hX γ hγ hγ₂ M hM Xc hXc
    γ (-Real.log ‖z‖ + h) α₁ α₂ α₃ ξ q hm z (Real.rpow_pos_of_pos hp _) hout
  rw [ht]
  calc
    _ ≤ ENNReal.ofReal (D * ‖z‖ ^ (2 + γ * (Q γ - α₁) - γ ^ 2 / 2)) * ENNReal.ofReal C₀ :=
      mul_le_mul' le_rfl (hb z ξ hz.le
        (by simpa only [Real.one_rpow] using Real.rpow_le_rpow (norm_nonneg z) hz.le (sub_nonneg.mpr hξ₁.le)))
    _ = _ := by
      rw [← ENNReal.ofReal_mul hs]
      congr 1
      ring

/-- The actual first-order radial error vanishes after division by the dual power,
whenever its explicit radial exponent has the strict source margin. -/
theorem dual_radial_first_order_littleO {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (α₁ α₂ α₃ ξ q h κ : ℝ) (hh : 0 ≤ h) (hξ : 0 < ξ) (hξ₁ : ξ < 1) (hq : 0 ≤ q)
    (hslack : κ < 2 + γ * (Q γ - α₁) - γ ^ 2 / 2) :
    Tendsto (fun z : ℂ =>
      (∫⁻ ω, ENNReal.ofReal (‖z‖ ^ (2 : ℝ) * Real.exp
        (γ * (Xc ω 0 (-Real.log ‖z‖ + h) -
          (Q γ - α₁) * (-Real.log ‖z‖ + h)))) *
          dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^ (-q) ∂P).toReal / ‖z‖ ^ κ)
      (nhdsWithin 0 {z : ℂ | z ≠ 0}) (nhds 0) := by
  let F : ℂ → ℝ := fun z =>
    (∫⁻ ω, ENNReal.ofReal (‖z‖ ^ (2 : ℝ) * Real.exp
      (γ * (Xc ω 0 (-Real.log ‖z‖ + h) -
        (Q γ - α₁) * (-Real.log ‖z‖ + h)))) *
        dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^ (-q) ∂P).toReal
  obtain ⟨C, hC, hb⟩ := dual_radial_first_order_bound P X hX γ hγ hγ₂ M hM Xc hXc
    α₁ α₂ α₃ ξ q h hh hξ hξ₁ hq
  have hn : ∀ᶠ z : ℂ in nhdsWithin 0 {z : ℂ | z ≠ 0},
      ‖(F z : ℂ)‖ ≤ C * ‖z‖ ^ (2 + γ * (Q γ - α₁) - γ ^ 2 / 2) := by
    filter_upwards [hb] with z hz
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hz).trans_eq
      (ENNReal.toReal_ofReal (mul_nonneg hC.le (Real.rpow_nonneg (norm_nonneg z) _)))
  exact (isComplexLittleOAtZero_ofReal_iff κ F).mp
    (isComplexLittleOAtZero_of_norm_le_power hslack hn)

end DOZZ.Proofs

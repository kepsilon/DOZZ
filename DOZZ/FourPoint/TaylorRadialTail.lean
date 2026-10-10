/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Planar.RadialCriteria
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! The sharp planar tail power, obtained by Haar dilation. -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Exact dilation of a radial tail. The factor is the planar Jacobian times the radial power. -/
theorem planar_radial_tail_scale (a ρ : ℝ) (hρ : 0 < ρ) :
    (∫⁻ x : ℂ in (Metric.ball 0 ρ)ᶜ, ENNReal.ofReal (‖x‖ ^ a)) =
      ENNReal.ofReal (ρ ^ (a + 2)) *
        ∫⁻ x : ℂ in (Metric.ball 0 1)ᶜ, ENNReal.ofReal (‖x‖ ^ a) := by
  let F : ℂ → ℝ≥0∞ := ((Metric.ball 0 ρ)ᶜ).indicator (fun x => ENNReal.ofReal (‖x‖ ^ a))
  have hf : Measurable F := (ENNReal.measurable_ofReal.comp (measurable_norm.pow_const a)).indicator measurableSet_ball.compl
  have hcomp : (fun x : ℂ => F (ρ • x)) =
      fun x : ℂ => ENNReal.ofReal (ρ ^ a) * ((Metric.ball 0 1)ᶜ).indicator (fun y => ENNReal.ofReal (‖y‖ ^ a)) x := by
    funext x
    have hn : ‖ρ • x‖ = ρ * ‖x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    have hm : ρ • x ∈ (Metric.ball (0 : ℂ) ρ)ᶜ ↔ x ∈ (Metric.ball (0 : ℂ) 1)ᶜ := by
      simp only [mem_compl_iff, Metric.mem_ball, dist_zero_right, hn]
      apply not_congr
      constructor
      · intro hh
        nlinarith only [hh, hρ]
      · intro hh
        nlinarith only [hh, hρ]
    by_cases hx : x ∈ (Metric.ball (0 : ℂ) 1)ᶜ
    · simp only [F, Set.indicator_of_mem (hm.mpr hx), Set.indicator_of_mem hx, hn]
      rw [Real.mul_rpow hρ.le (norm_nonneg _), ENNReal.ofReal_mul (Real.rpow_nonneg hρ.le _)]
    · simp only [F, Set.indicator_of_notMem (hm.not.mpr hx), Set.indicator_of_notMem hx, mul_zero]
  have hmap := Measure.map_addHaar_smul (volume : Measure ℂ) hρ.ne'
  have hchange := lintegral_map (μ := (volume : Measure ℂ)) hf (measurable_const_smul ρ)
  rw [hmap, lintegral_smul_measure, Complex.finrank_real_complex, abs_of_pos (inv_pos.mpr (sq_pos_of_pos hρ))] at hchange
  change ENNReal.ofReal ((ρ ^ 2)⁻¹) * (∫⁻ x, F x) = _ at hchange
  rw [hcomp, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_indicator measurableSet_ball.compl] at hchange
  have he : ENNReal.ofReal (ρ ^ 2) * ENNReal.ofReal ((ρ ^ 2)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul (sq_nonneg ρ), mul_inv_cancel₀ (pow_ne_zero _ hρ.ne'), ENNReal.ofReal_one]
  have he₂ : ENNReal.ofReal (ρ ^ 2) * ENNReal.ofReal (ρ ^ a) = ENNReal.ofReal (ρ ^ (a + 2)) := by
    rw [← ENNReal.ofReal_mul (sq_nonneg ρ), ← Real.rpow_natCast, ← Real.rpow_add hρ]
    congr 2
    ring
  calc
    _ = ENNReal.ofReal (ρ ^ 2) * (ENNReal.ofReal ((ρ ^ 2)⁻¹) * ∫⁻ x, F x) := by rw [← mul_assoc, he, one_mul, lintegral_indicator measurableSet_ball.compl]
    _ = ENNReal.ofReal (ρ ^ 2) * (ENNReal.ofReal (ρ ^ a) * ∫⁻ x in (Metric.ball (0 : ℂ) 1)ᶜ, ENNReal.ofReal (‖x‖ ^ a)) := by
      dsimp only [F]
      rw [lintegral_indicator measurableSet_ball.compl, hchange, lintegral_indicator measurableSet_ball.compl]
    _ = _ := by rw [← mul_assoc, he₂]

/-- A finite constant before every positive radius, with the literal tail exponent a+2. -/
theorem planar_radial_tail_bound (a : ℝ) (ha : a < -2) :
    ∃ C : ℝ, 0 < C ∧ ∀ ρ : ℝ, 0 < ρ →
      (∫⁻ x : ℂ in (Metric.ball 0 ρ)ᶜ, ENNReal.ofReal (‖x‖ ^ a)) ≤ ENNReal.ofReal (C * ρ ^ (a + 2)) := by
  let J : ℝ≥0∞ := ∫⁻ x : ℂ in (Metric.ball 0 1)ᶜ, ENNReal.ofReal (‖x‖ ^ a)
  have hJ : J < ⊤ := by
    have h := (integrableOn_norm_rpow_ball_compl_iff a 1 zero_lt_one).mpr ha
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using
      (hasFiniteIntegral_iff_norm _).mp h.hasFiniteIntegral
  refine ⟨J.toReal + 1, by positivity, ?_⟩
  intro ρ hρ
  rw [planar_radial_tail_scale a ρ hρ]
  have hj : J ≤ ENNReal.ofReal (J.toReal + 1) := by
    calc
      J = ENNReal.ofReal J.toReal := (ENNReal.ofReal_toReal hJ.ne).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
  calc
    _ ≤ ENNReal.ofReal (ρ ^ (a + 2)) * ENNReal.ofReal (J.toReal + 1) := mul_le_mul' le_rfl hj
    _ = _ := by rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hρ.le _), mul_comm]

end DOZZ.Proofs

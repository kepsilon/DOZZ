/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.TaylorPairIntegrability
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! The sharp planar tail power, obtained by Haar dilation. -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Exact dilation of a radial disk. The factor is the planar Jacobian times the radial power. -/
theorem planar_radial_ball_scale (a ρ : ℝ) (hρ : 0 < ρ) :
    (∫⁻ x : ℂ in (Metric.ball 0 ρ), ENNReal.ofReal (‖x‖ ^ a)) =
      ENNReal.ofReal (ρ ^ (a + 2)) *
        ∫⁻ x : ℂ in (Metric.ball 0 1), ENNReal.ofReal (‖x‖ ^ a) := by
  let F : ℂ → ℝ≥0∞ := ((Metric.ball 0 ρ)).indicator (fun x => ENNReal.ofReal (‖x‖ ^ a))
  have hf : Measurable F := (ENNReal.measurable_ofReal.comp (measurable_norm.pow_const a)).indicator measurableSet_ball
  have hcomp : (fun x : ℂ => F (ρ • x)) =
      fun x : ℂ => ENNReal.ofReal (ρ ^ a) * ((Metric.ball 0 1)).indicator (fun y => ENNReal.ofReal (‖y‖ ^ a)) x := by
    funext x
    have hn : ‖ρ • x‖ = ρ * ‖x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    have hm : ρ • x ∈ (Metric.ball (0 : ℂ) ρ) ↔ x ∈ (Metric.ball (0 : ℂ) 1) := by
      simp only [Metric.mem_ball, dist_zero_right, hn]
      constructor
      · intro hh
        nlinarith only [hh, hρ]
      · intro hh
        nlinarith only [hh, hρ]
    by_cases hx : x ∈ (Metric.ball (0 : ℂ) 1)
    · simp only [F, Set.indicator_of_mem (hm.mpr hx), Set.indicator_of_mem hx, hn]
      rw [Real.mul_rpow hρ.le (norm_nonneg _), ENNReal.ofReal_mul (Real.rpow_nonneg hρ.le _)]
    · simp only [F, Set.indicator_of_notMem (hm.not.mpr hx), Set.indicator_of_notMem hx, mul_zero]
  have hmap := Measure.map_addHaar_smul (volume : Measure ℂ) hρ.ne'
  have hchange := lintegral_map (μ := (volume : Measure ℂ)) hf (measurable_const_smul ρ)
  rw [hmap, lintegral_smul_measure, Complex.finrank_real_complex, abs_of_pos (inv_pos.mpr (sq_pos_of_pos hρ))] at hchange
  change ENNReal.ofReal ((ρ ^ 2)⁻¹) * (∫⁻ x, F x) = _ at hchange
  rw [hcomp, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_indicator measurableSet_ball] at hchange
  have he : ENNReal.ofReal (ρ ^ 2) * ENNReal.ofReal ((ρ ^ 2)⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul (sq_nonneg ρ), mul_inv_cancel₀ (pow_ne_zero _ hρ.ne'), ENNReal.ofReal_one]
  have he₂ : ENNReal.ofReal (ρ ^ 2) * ENNReal.ofReal (ρ ^ a) = ENNReal.ofReal (ρ ^ (a + 2)) := by
    rw [← ENNReal.ofReal_mul (sq_nonneg ρ), ← Real.rpow_natCast, ← Real.rpow_add hρ]
    congr 2
    ring
  calc
    _ = ENNReal.ofReal (ρ ^ 2) * (ENNReal.ofReal ((ρ ^ 2)⁻¹) * ∫⁻ x, F x) := by rw [← mul_assoc, he, one_mul, lintegral_indicator measurableSet_ball]
    _ = ENNReal.ofReal (ρ ^ 2) * (ENNReal.ofReal (ρ ^ a) * ∫⁻ x in (Metric.ball (0 : ℂ) 1), ENNReal.ofReal (‖x‖ ^ a)) := by
      dsimp only [F]
      rw [lintegral_indicator measurableSet_ball, hchange, lintegral_indicator measurableSet_ball]
    _ = _ := by rw [← mul_assoc, he₂]

/-- The translated radial disk has its exact integrable power, uniformly before the radius. -/
theorem planar_radial_ball_bound (a : ℝ) (ha : -2 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, ∀ ρ : ℝ, 0 < ρ →
      (∫⁻ x : ℂ in Metric.ball z ρ, ENNReal.ofReal (‖x - z‖ ^ a)) ≤ ENNReal.ofReal (C * ρ ^ (a + 2)) := by
  let J : ℝ≥0∞ := ∫⁻ x : ℂ in Metric.ball 0 1, ENNReal.ofReal (‖x‖ ^ a)
  have hJ : J < ⊤ := by
    have h := (integrableOn_norm_rpow_ball_iff a 1 zero_lt_one).mpr ha
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using
      (hasFiniteIntegral_iff_norm _).mp h.hasFiniteIntegral
  refine ⟨J.toReal + 1, by positivity, ?_⟩
  intro z ρ hρ
  simp_rw [norm_sub_rev _ z]
  rw [translated_ball_rpow_integral z ρ a, planar_radial_ball_scale a ρ hρ]
  have hj : J ≤ ENNReal.ofReal (J.toReal + 1) := by
    calc
      J = ENNReal.ofReal J.toReal := (ENNReal.ofReal_toReal hJ.ne).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
  calc
    _ ≤ ENNReal.ofReal (ρ ^ (a + 2)) * ENNReal.ofReal (J.toReal + 1) := mul_le_mul' le_rfl hj
    _ = _ := by rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hρ.le _), mul_comm]

end DOZZ.Proofs

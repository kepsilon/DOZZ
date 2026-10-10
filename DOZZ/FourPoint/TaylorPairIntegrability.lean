/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Planar.RadialCriteria
public import Mathlib.MeasureTheory.Group.Measure

/-! Positive planar kernels controlling the two near-diagonal fusion sectors. -/

@[expose] public section
open MeasureTheory Set Metric
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Translation preserves the radial positive integral on a disk. -/
theorem translated_ball_rpow_integral (u : ℂ) (R b : ℝ) :
    (∫⁻ v in Metric.ball u R, ENNReal.ofReal (‖u - v‖ ^ b)) =
      ∫⁻ v in Metric.ball (0 : ℂ) R, ENNReal.ofReal (‖v‖ ^ b) := by
  let f : ℂ → ℝ≥0∞ := (Metric.ball u R).indicator (fun v => ENNReal.ofReal (‖u - v‖ ^ b))
  have hf : Measurable f := (ENNReal.measurable_ofReal.comp
    ((measurable_const.sub measurable_id).norm.pow_const b)).indicator measurableSet_ball
  have hcomp : (fun x : ℂ => f (x + u)) =
      (Metric.ball (0 : ℂ) R).indicator (fun x => ENNReal.ofReal (‖x‖ ^ b)) := by
    funext x
    have hsub : u - (x + u) = -x := by abel
    have hmem : x + u ∈ Metric.ball u R ↔ x ∈ Metric.ball (0 : ℂ) R := by
      simp only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero]
    by_cases hx : x ∈ Metric.ball (0 : ℂ) R
    · simp only [f, Set.indicator_of_mem (hmem.mpr hx), Set.indicator_of_mem hx, hsub, norm_neg]
    · simp only [f, Set.indicator_of_notMem (hmem.not.mpr hx), Set.indicator_of_notMem hx]
  have h := (measurePreserving_add_right volume u).lintegral_comp hf
  rw [show (fun x : ℂ => f (x + u)) = _ from hcomp] at h
  dsimp only [f] at h
  rw [lintegral_indicator measurableSet_ball, lintegral_indicator measurableSet_ball] at h
  exact h.symm

/-- The pair singularity has a uniformly bounded inner integral as its root moves in a disk. -/
theorem planar_pair_power_bound (c u : ℂ) (R b : ℝ)
    (hu : u ∈ Metric.ball c R) :
    (∫⁻ v in Metric.ball c R, ENNReal.ofReal (‖u - v‖ ^ b)) ≤
      ∫⁻ v in Metric.ball (0 : ℂ) (2 * R), ENNReal.ofReal (‖v‖ ^ b) := by
  have hsubset : Metric.ball c R ⊆ Metric.ball u (2 * R) := by
    intro v hv
    have h := dist_triangle v c u
    have hu' : dist c u < R := by simpa only [Metric.mem_ball, dist_comm] using hu
    change dist v c < R at hv
    exact lt_of_le_of_lt h (by linarith only [hv, hu'])
  exact (lintegral_mono_set hsubset).trans_eq (translated_ball_rpow_integral u (2 * R) b)

/-- Two radial singularities on the pair space are integrable whenever each power exceeds -2.
The inner constant is uniform in the first mark, so no independence or informal separation
of intersecting singular sets is used. -/
theorem planar_pair_power_finite (c : ℂ) (R a b : ℝ)
    (hR : 0 < R) (ha : -2 < a) (hb : -2 < b) :
    (∫⁻ u in Metric.ball c R, ∫⁻ v in Metric.ball c R,
      ENNReal.ofReal (‖c - u‖ ^ a) * ENNReal.ofReal (‖u - v‖ ^ b)) < ⊤ := by
  let J : ℝ≥0∞ := ∫⁻ v in Metric.ball (0 : ℂ) (2 * R), ENNReal.ofReal (‖v‖ ^ b)
  have hJ : J < ⊤ := by
    have h := (integrableOn_norm_rpow_ball_iff b (2 * R) (by positivity)).mpr hb
    have hfin := (hasFiniteIntegral_iff_norm _).mp h.hasFiniteIntegral
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using hfin
  have hA : (∫⁻ u in Metric.ball c R, ENNReal.ofReal (‖c - u‖ ^ a)) < ⊤ := by
    rw [translated_ball_rpow_integral c R a]
    have h := (integrableOn_norm_rpow_ball_iff a R hR).mpr ha
    have hfin := (hasFiniteIntegral_iff_norm _).mp h.hasFiniteIntegral
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)] using hfin
  have hf : Measurable (fun u : ℂ => ENNReal.ofReal (‖c - u‖ ^ a)) :=
    ENNReal.measurable_ofReal.comp ((measurable_const.sub measurable_id).norm.pow_const a)
  have hbound : (∫⁻ u in Metric.ball c R, ∫⁻ v in Metric.ball c R,
      ENNReal.ofReal (‖c - u‖ ^ a) * ENNReal.ofReal (‖u - v‖ ^ b)) ≤
        (∫⁻ u in Metric.ball c R, ENNReal.ofReal (‖c - u‖ ^ a)) * J := by
    rw [← lintegral_mul_const J hf]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_ball] with u hu
    have hv : Measurable (fun v : ℂ => ENNReal.ofReal (‖u - v‖ ^ b)) :=
      ENNReal.measurable_ofReal.comp ((measurable_const.sub measurable_id).norm.pow_const b)
    rw [lintegral_const_mul _ hv]
    exact mul_le_mul' le_rfl (planar_pair_power_bound c u R b hu)
  exact hbound.trans_lt (ENNReal.mul_lt_top hA hJ)

end DOZZ.Proofs

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.RestartPast
public import DOZZ.FourPoint.Reflected.GlobalReinsertion
/-! The retained exterior radial weight is a measurable function of the complete stopped past. -/
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace DOZZ.Proofs

/-- Reinsertion written in terms of the two path halves, without a continuity condition at
zero; this makes it a measurable observable on the whole stopped-past carrier. -/
noncomputable def reflectedPastPlaneWeight (γ : ℝ) (p : BrownianPath × BrownianPath) (x : ℂ) : ℝ :=
  if ‖x‖ = 0 then 0 else Real.exp (γ*(if 0 ≤ -Real.log ‖x‖ then p.1 (Real.toNNReal (-Real.log ‖x‖))
    else p.2 (Real.toNNReal (Real.log ‖x‖)))-γ*Q γ*|Real.log ‖x‖|)

theorem reflected_pastPlaneWeight_measurable (γ : ℝ) :
    Measurable (fun p : (BrownianPath × BrownianPath) × ℂ => reflectedPastPlaneWeight γ p.1 p.2) := by
  classical
  have hl : Measurable (fun p : (BrownianPath × BrownianPath) × ℂ => Real.log ‖p.2‖) :=
    Real.measurable_log.comp (measurable_norm.comp measurable_snd)
  have hp := continuous_eval.measurable.comp
    (measurable_fst.fst.prodMk (continuous_real_toNNReal.measurable.comp hl.neg))
  have hn := continuous_eval.measurable.comp
    (measurable_fst.snd.prodMk (continuous_real_toNNReal.measurable.comp hl))
  have he : Measurable (fun p : (BrownianPath × BrownianPath) × ℂ =>
      if 0 ≤ -Real.log ‖p.2‖ then p.1.1 (Real.toNNReal (-Real.log ‖p.2‖))
      else p.1.2 (Real.toNNReal (Real.log ‖p.2‖))) := Measurable.ite (measurableSet_le (measurable_const (a := (0 : ℝ))) hl.neg) hp hn
  exact Measurable.ite (measurableSet_eq_fun (measurable_norm.comp measurable_snd) measurable_const)
    measurable_const ((he.const_mul γ).sub
      ((continuous_abs.measurable.comp hl).const_mul (γ*Q γ))).exp

/-- Before the restart time, the stopped positive half and the complete negative half retain
exactly the full radial reinsertion weight. -/
theorem reflected_pastPlaneWeight_eq (γ : ℝ) (a : TwoSidedPath) (T : ℝ≥0) (x : ℂ)
    (hx : -Real.log ‖x‖ ≤ (T : ℝ)) :
    reflectedPastPlaneWeight γ (stopBrownianPath (radialPositiveHalf a) T,radialNegativeHalf a) x =
      reflected_global_reinsertionWeight γ a x := by
  by_cases hx0 : ‖x‖ = 0
  · simp only [reflectedPastPlaneWeight,reflected_global_reinsertionWeight,ite_eq_left hx0]
  rw [reflectedPastPlaneWeight,reflected_global_reinsertionWeight,ite_eq_right hx0,ite_eq_right hx0]
  congr 3
  by_cases hl : 0 ≤ -Real.log ‖x‖
  · rw [ite_eq_left hl]
    change a (min (Real.toNNReal (-Real.log ‖x‖)) T : ℝ) = a (-Real.log ‖x‖)
    rw [Real.coe_toNNReal _ hl,min_eq_left hx]
  · rw [ite_eq_right hl]
    have hh : 0 ≤ Real.log ‖x‖ := (le_of_lt (neg_neg_iff_pos.mp (lt_of_not_ge hl)))
    change a (-(Real.toNNReal (Real.log ‖x‖) : ℝ)) = a (-Real.log ‖x‖)
    rw [Real.coe_toNNReal _ hh]

end DOZZ.Proofs

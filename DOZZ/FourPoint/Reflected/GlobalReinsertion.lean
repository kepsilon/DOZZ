/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.GlobalLateralAdmissible
/-! Exact radial reinsertion on the full punctured plane. -/
@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The unclamped radial Wick factor, with zero prescribed at the excluded origin. -/
noncomputable def reflected_global_reinsertionWeight (γ : ℝ) (A : TwoSidedPath) (x : ℂ) : ℝ :=
  if ‖x‖ = 0 then 0 else Real.exp (γ*A (-Real.log ‖x‖)-γ*Q γ*|Real.log ‖x‖|)

theorem reflected_global_reinsertionWeight_measurable (γ : ℝ) :
    Measurable (fun p : TwoSidedPath × ℂ => reflected_global_reinsertionWeight γ p.1 p.2) := by
  have hl : Measurable (fun p : TwoSidedPath × ℂ => Real.log ‖p.2‖) :=
    Real.measurable_log.comp (measurable_norm.comp measurable_snd)
  have he : Measurable (fun p : TwoSidedPath × ℂ => p.1 (-Real.log ‖p.2‖)) :=
    continuous_eval.measurable.comp (measurable_fst.prodMk hl.neg)
  exact Measurable.ite (measurableSet_eq_fun (measurable_norm.comp measurable_snd) measurable_const)
    measurable_const (Real.measurable_exp.comp ((measurable_const.mul he).sub
      (measurable_const.mul (continuous_abs.measurable.comp hl))))

theorem reflected_global_reinsertionWeight_chart (ρ γ : ℝ) (hρ : 0 < ρ)
    (A : TwoSidedPath) (x : ℂ) (hx : x ∈ originLateralChart ρ) :
    reflected_global_reinsertionWeight γ A x = originRadialReinsertionWeight ρ γ A x := by
  have hx0 : ‖x‖ ≠ 0 := ne_of_gt (lt_trans (by linarith : 0 < 2*ρ) hx)
  rw [reflected_global_reinsertionWeight, ite_eq_right hx0,
    originRadialReinsertionWeight_chart_eq ρ γ hρ A x hx]

/-- Reinsertion cancels the exact removal density, as a samplewise measure identity. -/
theorem reflected_global_reinsertion_measure (γ : ℝ) (A : TwoSidedPath) (μ : Measure ℂ) :
    (μ.withDensity (lateralRadialWeight γ A)).withDensity
      (fun x => ENNReal.ofReal (reflected_global_reinsertionWeight γ A x)) =
      μ.restrict ({0} : Set ℂ)ᶜ := by
  have hL : Measurable (lateralRadialWeight γ A) := by
    change Measurable ((fun p : (ℝ × TwoSidedPath) × ℂ =>
      lateralRadialWeight p.1.1 p.1.2 p.2) ∘ fun x : ℂ => ((γ, A), x))
    exact measurable_lateralRadialWeight.comp (measurable_const.prodMk measurable_id)
  have hW : Measurable (fun x => ENNReal.ofReal (reflected_global_reinsertionWeight γ A x)) :=
    ((reflected_global_reinsertionWeight_measurable γ).comp
      (measurable_const.prodMk measurable_id)).ennreal_ofReal
  rw [← withDensity_mul μ hL hW]
  have he : (fun x => lateralRadialWeight γ A x *
      ENNReal.ofReal (reflected_global_reinsertionWeight γ A x)) =
      (({0} : Set ℂ)ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext x
    by_cases hx : x = 0
    · simp [hx, lateralRadialWeight, reflected_global_reinsertionWeight]
    · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      rw [lateralRadialWeight, reflected_global_reinsertionWeight, ite_eq_right hn,
        ite_eq_right hn, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      have ha : -γ*A (-Real.log ‖x‖)+γ*Q γ*|Real.log ‖x‖| +
          (γ*A (-Real.log ‖x‖)-γ*Q γ*|Real.log ‖x‖|) = 0 := by ring
      rw [ha, Real.exp_zero, ENNReal.ofReal_one, indicator_of_mem (by simpa using hx)]
  change μ.withDensity (fun x => lateralRadialWeight γ A x *
    ENNReal.ofReal (reflected_global_reinsertionWeight γ A x)) = _
  rw [he]
  exact withDensity_indicator_one (measurableSet_singleton (0 : ℂ)).compl

end DOZZ.Proofs

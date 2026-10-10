/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.PastObservable
public import DOZZ.FourPoint.Dual.LeadingRadialMoment
/-! Identifying the actual likelihood with its radial-path and stopped-past observables. -/
@[expose] public section
open MeasureTheory
open scoped NNReal
namespace DOZZ.Proofs

/-- The restart scale as a measurable function of the complete signed radial path. -/
noncomputable def dualPathRadialScale (γ ν h : ℝ) (z : ℂ) (A : TwoSidedPath) : ℝ :=
  Real.exp (γ*A (-Real.log ‖z‖+h)-γ*ν*(-Real.log ‖z‖+h)-2*(-Real.log ‖z‖))

/-- Fixed-time radial evaluation gives a measurable path likelihood. -/
theorem dual_path_radial_scale_measurable (γ ν h : ℝ) (z : ℂ) :
    Measurable (dualPathRadialScale γ ν h z) :=
  (((ContinuousMap.measurable_eval _).const_mul γ).sub measurable_const).sub measurable_const |>.exp

/-- The actual circle-average likelihood agrees almost surely with its radial-path version. -/
theorem dual_source_radial_scale_eq_path_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Xc : Ω → ℂ → ℝ → ℝ)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (γ ν h : ℝ) (z : ℂ) :
    dual_radial_scale γ ν h Xc z =ᵐ[P]
      (fun ω => dualPathRadialScale γ ν h z (originRadialPath Xc ω)) := by
  filter_upwards [originRadialPath_eval_ae hcont] with ω hω
  unfold dual_radial_scale dualPathRadialScale
  rw [hω]

/-- At the actual restart time, the path likelihood is exactly the stopped-past terminal
likelihood used in the Williams joint law. -/
theorem dual_path_radial_scale_eq_past (γ ν h : ℝ) (z : ℂ) (hz0 : z ≠ 0)
    (A : TwoSidedPath) (T : ℝ≥0) (hT : (T : ℝ) = -Real.log ‖z‖+h) :
    dualPathRadialScale γ ν h z A = dualPastRestartWeight γ ν T z
      (stopBrownianPath (radialPositiveHalf A) T, radialNegativeHalf A) := by
  have he := dual_radial_scale_eq_restart γ ν h
    (fun (_ : Unit) (_ : ℂ) t => A t) z hz0 ()
  change dualPathRadialScale γ ν h z A =
    ‖z‖^(2 : ℝ)*Real.exp (γ*(A (-Real.log ‖z‖+h)-ν*(-Real.log ‖z‖+h))) at he
  rw [he]
  unfold dualPastRestartWeight
  simp only [stopBrownianPath, ContinuousMap.coe_mk, min_self,
    radialPositiveHalf, ContinuousMap.comp_apply]
  change ‖z‖^(2 : ℝ)*Real.exp (γ*(A (-Real.log ‖z‖+h)-ν*(-Real.log ‖z‖+h))) =
    ‖z‖^(2 : ℝ)*Real.exp (γ*(A (T : ℝ)-ν*(T : ℝ)))
  rw [hT]

end DOZZ.Proofs

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.SourcePastOuterMass
public import DOZZ.FourPoint.Reflected.LeadingRadialMoment
import Mathlib.Tactic
/-! The actual retained outer mass and radial likelihood are independent of the restarted future. -/
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The source outer mass and restart scale are genuine stopped-past observables. Their
independence from the full restarted Brownian path follows from the radial law and
actual removed lateral carrier, rather than from an independence premise on the outer mass. -/
theorem reflected_source_outer_past_indep
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (N : Ω → Measure ℂ) (hN : Measurable N)
    (hi : IndepFun (originRadialPath Xc) N P)
    (heq : N =ᵐ[P] (fun ω => (M ω).withDensity (lateralRadialWeight γ (originRadialPath Xc ω))))
    (hfin : ∀ ω K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → N ω K < ⊤)
    (α₁ α₂ α₃ ν ξ h : ℝ) (z : ℂ) (T : ℝ≥0)
    (hcoord : (T : ℝ) = -Real.log ‖z‖+h)
    (hr : 0 < ‖z‖^(1-ξ)) (hz : ‖z‖ < ‖z‖^(1-ξ))
    (hT : Real.exp (-(T : ℝ)) ≤ ‖z‖^(1-ξ)) :
    IndepFun (fun ω => brownianShiftPath T (radialPositiveHalf (originRadialPath Xc ω)))
      (fun ω => (gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ,
        reflected_radial_scale γ ν h Xc z ω)) P := by
  let _ : IsProbabilityMeasure P := hX.1
  let A := originRadialPath Xc
  have hA := originRadialPath_aemeasurable P X Xc hc hcont
  have hB := (originRadialPath_isBrownian P X Xc hX hc hcont).1
  have hh := originRadialPath_halves_indep P X Xc hX hc hcont
  have hp := reflected_radial_future_indep_full_past_lateral P A hA hB hh N hN.aemeasurable hi T
  let Φ : (BrownianPath × BrownianPath) × Measure ℂ → ℝ≥0∞ × ℝ := fun p =>
    (reflectedPastOuterMassCode γ α₁ α₂ α₃ (‖z‖^(1-ξ)) z p,
      Real.exp (γ*p.1.1 T-γ*ν*T-γ^2/2*(-Real.log ‖z‖)))
  have hΦ : Measurable Φ := (reflected_pastOuterMassCode_measurable γ α₁ α₂ α₃ (‖z‖^(1-ξ)) z).prodMk
    ((((ContinuousMap.measurable_eval T).comp measurable_fst.fst).const_mul γ).sub_const
      (γ*ν*T) |>.sub_const (γ^2/2*(-Real.log ‖z‖)) |>.exp)
  have hiΦ := hp.comp measurable_id hΦ
  have ho := reflected_source_outerMass_pastCode_ae P X hX γ hγ hγ₂ M hM A N heq hfin
    α₁ α₂ α₃ ξ z T hr hz hT
  have he : (fun ω => Φ ((stopBrownianPath (radialPositiveHalf (A ω)) T,
      radialNegativeHalf (A ω)),N ω)) =ᵐ[P]
      (fun ω => (gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ,reflected_radial_scale γ ν h Xc z ω)) := by
    filter_upwards [ho,originRadialPath_eval_ae hcont] with ω hω hev
    apply Prod.ext hω
    have heT : stopBrownianPath (radialPositiveHalf (A ω)) T T = A ω (T : ℝ) := by
      change A ω (min (T : ℝ) (T : ℝ)) = A ω (T : ℝ)
      rw [min_self]
    change Real.exp (γ*(stopBrownianPath (radialPositiveHalf (A ω)) T T)-γ*ν*T-γ^2/2*(-Real.log ‖z‖)) = _
    rw [heT]
    dsimp only [reflected_radial_scale]
    rw [hev,hcoord]
  exact hiΦ.congr (ae_of_all P fun _ => rfl) he

end DOZZ.Proofs

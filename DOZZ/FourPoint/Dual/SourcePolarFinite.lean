/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.SourceRestartWilliams
public import DOZZ.FourPoint.Dual.PolarFinitenessTransport
import Mathlib.Tactic
/-! The actual source restarted polar integral is finite by its proved Williams joint law. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Finiteness of the actual translated restarted polar mass, rather than an assumed
real representative, follows from the supplied source chaos and reflection witness. -/
theorem dual_source_restarted_polar_finite_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (h α₁ α₂ α₃ ξ : ℝ) (hα₁ : α₁ < Q γ) (z : ℂ) (hz0 : z ≠ 0)
    (hz : ‖z‖ < ‖z‖^(1-ξ)) (T : ℝ≥0) (hT : (T : ℝ) = -Real.log ‖z‖+h)
    (hr : Real.exp (-(T : ℝ)) ≤ ‖z‖^(1-ξ))
    (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z)
    (hiZ : IndepFun (originRadialPath Xc) Z P)
    (B : Ω → BrownianPath × BrownianPath) (Z₀ : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α₁ B Z₀) :
    ∀ᵐ ω : Ω × Ω ∂P.prod P, (∫⁻ t,
      (if 0 < t then ENNReal.ofReal (Real.exp (γ*
        (brownianShiftPath T (radialPositiveHalf (originRadialPath Xc ω.1))
          (Real.toNNReal t)-(Q γ-α₁)*t))) else 0)
        ∂(Z ω.2).map (fun s => s-(T : ℝ))) ≠ ⊤ := by
  let _ : IsProbabilityMeasure P := hX.1
  let ν := Q γ-α₁
  let A := originRadialPath Xc
  have hA := originRadialPath_aemeasurable P X Xc hc hcont
  let R := (brownianMaximumReferenceLaw ν).prod P
  let _ := isProbabilityMeasure_brownianMaximumReferenceLaw (sub_pos.mpr hα₁)
  let D := fun ω => brownianShiftPath T (radialPositiveHalf (A ω))
  have hs : Measurable (fun a => brownianShiftPath T (radialPositiveHalf a)) :=
    continuous_brownianShiftPath.measurable.comp
      (measurable_const.prodMk continuous_radialPositiveHalf.measurable)
  have hDm : AEMeasurable D P := hs.comp_aemeasurable hA
  have hDZ : IndepFun D Z P := hiZ.comp₀ hA hZ.2.2.2.1 hs.aemeasurable measurable_id.aemeasurable
  let Y := fun ω => (dual_radial_scale γ ν h Xc z ω,
    (dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ).toReal)
  have hcoord := (hc.2.1 0 (-Real.log ‖z‖+h)).aemeasurable
  have hβ : AEMeasurable (dual_radial_scale γ ν h Xc z) P :=
    ((hcoord.const_mul γ).sub aemeasurable_const).sub aemeasurable_const |>.exp
  have hYm : AEMeasurable Y P := hβ.prodMk
    (((dual_outerMass_measure_measurable γ α₁ α₂ α₃ ξ z).comp_aemeasurable
      (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ₂ M hM)).ennreal_toReal)
  let V := fun ω : Ω × Ω => ∫⁻ t,
    (if 0 < t then ENNReal.ofReal (Real.exp (γ*(D ω.1 (Real.toNNReal t)-ν*t))) else 0)
      ∂(Z ω.2).map (fun s => s-(T : ℝ))
  have hVm : AEMeasurable V (P.prod P) :=
    dual_translated_polar_mass_aemeasurable P D hDm γ ν Z hZ hDZ T
  let J := fun q : ℝ × Ω => ENNReal.ofReal (Real.exp (γ*q.1))*twoSidedReflectionCutMass γ q.1 B Z₀ q.2
  have hJm : AEMeasurable J R :=
    (measurable_fst.aemeasurable.const_mul γ).exp.ennreal_ofReal.mul
      (actual_cut_mass_joint_aemeasurable P _ γ B Z₀
        (aemeasurable_of_twoSidedConditioned hData.1) hData.2.1.2.2.2.1 hData.2.1.2.2.2.2.1)
  have hLaw := dual_source_restart_outer_williams_law P X Xc hX hc hm hcont γ hγ hγ₂ M hM
    h α₁ α₂ α₃ ξ hα₁ z hz0 hz T hT hr Z hZ hiZ B Z₀ hData
  exact dual_copied_joint_law_finite P R Y hYm V hVm J hJm hLaw
    (dual_williams_cut_mass_finite_ae P γ α₁ hγ hγ₂ hα₁ B Z₀ hData)

end DOZZ.Proofs

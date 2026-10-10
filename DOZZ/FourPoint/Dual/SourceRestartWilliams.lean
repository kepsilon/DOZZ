/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.SourcePastIndependence
public import DOZZ.FourPoint.Reflected.CopiedPolarTransport
public import DOZZ.Correlations.Tails.WilliamsSourceInputLaw
import Mathlib.Tactic
/-! Exact source joint Williams law, including the translated inner lateral copy. -/
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The actual source likelihood/exterior pair is retained in the translated restarted
polar-mass Williams law, on the same supplied reflection witness. Future independence
and the lateral translation are proved by the source restart and stationarity theorems. -/
theorem dual_source_restart_outer_williams_law
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
    let ν := Q γ-α₁
    let D := fun ω => brownianShiftPath T (radialPositiveHalf (originRadialPath Xc ω))
    let Y := fun ω => (dual_radial_scale γ ν h Xc z ω,
      (dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ).toReal)
    (P.prod P).map (fun ω : Ω × Ω => (Y ω.1, ∫⁻ t,
      (if 0 < t then ENNReal.ofReal (Real.exp
        (γ * (D ω.1 (Real.toNNReal t) - ν * t))) else 0)
          ∂(Z ω.2).map (fun s => s - (T : ℝ)))) =
      (P.map Y).prod
        (((brownianMaximumReferenceLaw ν).prod P).map (fun q =>
          ENNReal.ofReal (Real.exp (γ*q.1))*twoSidedReflectionCutMass γ q.1 B Z₀ q.2)) := by
  let A := originRadialPath Xc
  have hA := originRadialPath_aemeasurable P X Xc hc hcont
  have hB := (originRadialPath_isBrownian P X Xc hX hc hcont).1
  let D := fun ω => brownianShiftPath T (radialPositiveHalf (A ω))
  have hs : Measurable (fun a => brownianShiftPath T (radialPositiveHalf a)) :=
    continuous_brownianShiftPath.measurable.comp
      (measurable_const.prodMk continuous_radialPositiveHalf.measurable)
  have hD : AEMeasurable D P := hs.comp_aemeasurable hA
  have hDb : IsBrownianReal (fun t p => p t) (P.map D) := by
    rw [reflected_restarted_radial_path_law P A hA hB T]
    exact radialPositiveHalf_map_isBrownian P A hA hB
  have hDZ := hiZ.comp₀ hA hZ.2.2.2.1 hs.aemeasurable measurable_id.aemeasurable
  have hcoord := (hc.2.1 0 (-Real.log ‖z‖+h)).aemeasurable
  have hβ : AEMeasurable (dual_radial_scale γ (Q γ-α₁) h Xc z) P := by
    exact ((hcoord.const_mul γ).sub aemeasurable_const).sub aemeasurable_const |>.exp
  have hYm := hβ.prodMk (((dual_outerMass_measure_measurable γ α₁ α₂ α₃ ξ z).comp_aemeasurable
    (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ₂ M hM)).ennreal_toReal)
  have hYD := (dual_source_future_indep_outer_restart P X Xc hX hc hm hcont γ hγ hγ₂ M hM
    (Q γ-α₁) h α₁ α₂ α₃ ξ z hz0 hz T hT hr).symm
  let Qν := P.map (fun ω => (B ω).1)
  have hQν : IsNegativeConditionedBrownianLaw (Q γ-α₁) Qν := hData.1.1.2
  have hl := reflected_copied_translated_williams_joint_law P D hD hDb γ Z hZ hDZ
    _ hYm hYD (Q γ-α₁) (sub_pos.mpr hα₁) Qν hQν T
  rw [isLateralGMCOf_map_eq P P γ Z Z₀ hZ hData.2.1,
    williams_source_input_law P γ α₁ hα₁ B Z₀ hData Qν hQν] at hl
  exact hl

end DOZZ.Proofs

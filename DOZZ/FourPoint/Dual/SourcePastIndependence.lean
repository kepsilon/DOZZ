/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.PastExteriorIdentity
public import DOZZ.FourPoint.Dual.PathLikelihood
import Mathlib.Tactic
/-! Source-space future independence of the actual dual exterior and restart likelihood. -/
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The actual exterior mass and restart likelihood jointly depend only on the stopped
past and lateral carrier, so are independent of the future inward Brownian path. -/
theorem dual_source_future_indep_outer_restart
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (ν h α₁ α₂ α₃ ξ : ℝ) (z : ℂ) (hz0 : z ≠ 0) (hz : ‖z‖ < ‖z‖^(1-ξ))
    (T : ℝ≥0) (hT : (T : ℝ) = -Real.log ‖z‖+h)
    (hr : Real.exp (-(T : ℝ)) ≤ ‖z‖^(1-ξ)) :
    IndepFun (fun ω => brownianShiftPath T (radialPositiveHalf (originRadialPath Xc ω)))
      (fun ω => (dual_radial_scale γ ν h Xc z ω,
        (dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ).toReal)) P := by
  let A := originRadialPath Xc
  have hA := originRadialPath_aemeasurable P X Xc hc hcont
  obtain ⟨N, hNm, hi, hfin, heq, _, _⟩ := reflected_copied_radial_plane_observable
    P X Xc hX hc hm hcont γ hγ hγ₂ M hM
  let NL : Ω → DualLocalPlaneMeasure := fun ω => ⟨N ω, hfin ω⟩
  have hNL : Measurable NL := hNm.subtype_mk
  have hiL : IndepFun A NL P := dual_indepFun_subtype_lift P A N _ hfin hi
  have hB := (originRadialPath_isBrownian P X Xc hX hc hcont).1
  have hhalves := originRadialPath_halves_indep P X Xc hX hc hcont
  have hip := dual_radial_future_indep_restart_exterior P A hA hB hhalves NL hNL.aemeasurable
    hiL T γ ν α₁ α₂ α₃ z (‖z‖^(1-ξ))
  have hconv : Measurable (fun p : ℝ × ℝ≥0∞ => (p.1,p.2.toReal)) :=
    measurable_fst.prodMk measurable_snd.ennreal_toReal
  have hir := hip.comp measurable_id hconv
  have hpast := dual_source_past_exterior_mass_eq P X hX γ hγ hγ₂ M N hM A hfin heq
    α₁ α₂ α₃ ξ z hz T hr
  have hβ := dual_source_radial_scale_eq_path_ae P Xc hcont γ ν h z
  have he : (fun ω =>
      (dualPastRestartWeight γ ν T z (stopBrownianPath (radialPositiveHalf (A ω)) T,
        radialNegativeHalf (A ω)),
        (dualPastExteriorMass γ α₁ α₂ α₃ z (‖z‖^(1-ξ))
          ((stopBrownianPath (radialPositiveHalf (A ω)) T, radialNegativeHalf (A ω)),NL ω)).toReal)) =ᵐ[P]
      (fun ω => (dual_radial_scale γ ν h Xc z ω,
        (dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ).toReal)) := by
    filter_upwards [hpast,hβ] with ω hω hβω
    refine Prod.ext ?_ (congrArg ENNReal.toReal hω)
    rw [← dual_path_radial_scale_eq_past γ ν h z hz0 (A ω) T hT]
    exact hβω.symm
  exact hir.congr (ae_of_all _ (fun _ => rfl)) he

end DOZZ.Proofs

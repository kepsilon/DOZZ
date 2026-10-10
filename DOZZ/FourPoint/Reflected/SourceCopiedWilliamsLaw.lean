/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.SourceOuterPast
public import DOZZ.FourPoint.Reflected.CopiedPolarTransport
public import DOZZ.Correlations.Tails.WilliamsSourceInputLaw
/-! The copied restarted inner polar mass retains its joint law with the literal source outer mark. -/
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The actual retained source mass and restart scale carry the independent Williams inner
law after translation of the inner lateral copy. All source Brownian/past independences are
proved from the given field, chaos and removed carrier. -/
theorem reflected_source_copied_williams_joint_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (N : Ω → Measure ℂ) (hN : Measurable N) (hi : IndepFun (originRadialPath Xc) N P)
    (heq : N =ᵐ[P] (fun ω => (M ω).withDensity (lateralRadialWeight γ (originRadialPath Xc ω))))
    (hfin : ∀ ω K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → N ω K < ⊤)
    (α₁ α₂ α₃ ξ h : ℝ) (hα₁ : α₁ < Q γ)
    (B : Ω → BrownianPath × BrownianPath)
    (hL : IsLateralGMCOf P γ (fun ω => lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)))
    (hData : IsReflectionData P γ α₁ B (fun ω => lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)))
    (Qν : Measure BrownianPath) (hQν : IsNegativeConditionedBrownianLaw (Q γ-α₁) Qν)
    (z : ℂ) (T : ℝ≥0) (hcoord : (T : ℝ) = -Real.log ‖z‖+h)
    (hr : 0 < ‖z‖^(1-ξ)) (hz : ‖z‖ < ‖z‖^(1-ξ))
    (hT : Real.exp (-(T : ℝ)) ≤ ‖z‖^(1-ξ)) :
    let A := originRadialPath Xc
    let Z := fun ω => lateralProjectedGMC γ (A ω) (M ω)
    let D := fun ω => brownianShiftPath T (radialPositiveHalf (A ω))
    let Y := fun ω => (gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ,
      reflected_radial_scale γ (Q γ-α₁) h Xc z ω)
    (P.prod P).map (fun v : Ω × Ω => (Y v.1,∫⁻ t,
      (if 0 < t then ENNReal.ofReal (Real.exp (γ*(D v.1 (Real.toNNReal t)-(Q γ-α₁)*t))) else 0)
        ∂(Z v.2).map (fun s => s-(T : ℝ)))) =
    (P.map Y).prod (((brownianMaximumReferenceLaw (Q γ-α₁)).prod P).map
      (fun q => ENNReal.ofReal (Real.exp (γ*q.1))*twoSidedReflectionCutMass γ q.1 B Z q.2)) := by
  let _ : IsProbabilityMeasure P := hX.1
  let A := originRadialPath Xc
  let Z := fun ω => lateralProjectedGMC γ (A ω) (M ω)
  let D := fun ω => brownianShiftPath T (radialPositiveHalf (A ω))
  let Y := fun ω => (gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ,
    reflected_radial_scale γ (Q γ-α₁) h Xc z ω)
  have hA := originRadialPath_aemeasurable P X Xc hc hcont
  have hs : Measurable (fun a : TwoSidedPath => brownianShiftPath T (radialPositiveHalf a)) :=
    continuous_brownianShiftPath.measurable.comp (measurable_const.prodMk continuous_radialPositiveHalf.measurable)
  have hD := hs.comp_aemeasurable hA
  have hB₀ := (originRadialPath_isBrownian P X Xc hX hc hcont).1
  have hlaw := reflected_restarted_radial_path_law P A hA hB₀ T
  have hDb : IsBrownianReal (fun t p => p t) (P.map D) := by
    rw [show P.map D = P.map (fun ω => radialPositiveHalf (A ω)) from hlaw]
    exact radialPositiveHalf_map_isBrownian P A hA hB₀
  have hDZ : IndepFun D Z P :=
    (lateralProjectedGMC_indep P X Xc hX hc hm hcont γ hγ hγ₂ M hM).comp₀ hA
      hL.2.2.2.1 hs.aemeasurable measurable_id.aemeasurable
  have hYD := (reflected_source_outer_past_indep P X hX Xc hc hcont γ hγ hγ₂ M hM
    N hN hi heq hfin α₁ α₂ α₃ (Q γ-α₁) ξ h z T hcoord hr hz hT).symm
  have hYm : AEMeasurable Y P := by
    have ho := (reflected_outerMass_measure_measurable γ α₁ α₂ α₃ ξ z).comp_aemeasurable
      (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ₂ M hM)
    have ht := (hc.2.1 0 (-Real.log ‖z‖+h)).aemeasurable
    have hb : AEMeasurable (reflected_radial_scale γ (Q γ-α₁) h Xc z) P := by
      exact ((ht.const_mul γ).sub aemeasurable_const).sub aemeasurable_const |>.exp
    exact ho.prodMk hb
  have hh := reflected_copied_translated_williams_joint_law P D hD hDb γ Z hL hDZ
    Y hYm hYD (Q γ-α₁) (sub_pos.mpr hα₁) Qν hQν T
  rw [williams_source_input_law P γ α₁ hα₁ B Z hData Qν hQν] at hh
  exact hh

end DOZZ.Proofs

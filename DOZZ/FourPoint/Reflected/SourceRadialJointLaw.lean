/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.SourceCopiedWilliamsLaw
public import DOZZ.FourPoint.Reflected.SourceRadialRestart
public import DOZZ.FourPoint.Reflected.TranslatedPolarMeasurable
/-! Exact joint law of the radial inner mass and the retained source mass. -/
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

theorem reflected_source_copied_radial_joint_law
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
    (z : ℂ) (hz0 : z ≠ 0) (T : ℝ≥0) (hcoord : (T : ℝ) = -Real.log ‖z‖+h)
    (hr : 0 < ‖z‖^(1-ξ)) (hz : ‖z‖ < ‖z‖^(1-ξ))
    (hT : Real.exp (-(T : ℝ)) ≤ ‖z‖^(1-ξ)) :
    let Y := fun ω => (gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ,
      reflected_radial_scale γ (Q γ-α₁) h Xc z ω)
    let F := fun p : (ℝ≥0∞ × ℝ) × ℝ≥0∞ => (p.1.1,ENNReal.ofReal p.1.2*p.2)
    (P.prod P).map (fun ω : Ω × Ω =>
      (gammaHalfOuterMass γ α₁ α₂ α₃ (M ω.1) z ξ,
        ENNReal.ofReal (‖z‖^(γ^2/2))*(∫⁻ x in {x : ℂ | 0 < ‖x‖ ∧ ‖x‖ < Real.exp (-(T : ℝ))},
          ENNReal.ofReal (‖x‖^(-(γ*α₁)))*
            ENNReal.ofReal (reflected_global_reinsertionWeight γ (originRadialPath Xc ω.1) x) ∂N ω.2))) =
      ((P.map Y).prod (((brownianMaximumReferenceLaw (Q γ-α₁)).prod P).map
        (fun q => ENNReal.ofReal (Real.exp (γ*q.1))*twoSidedReflectionCutMass γ q.1 B
          (fun ω => lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)) q.2))).map F := by
  let _ : IsProbabilityMeasure P := hX.1
  let A := originRadialPath Xc
  let Z := fun ω => lateralProjectedGMC γ (A ω) (M ω)
  let D := fun ω => brownianShiftPath T (radialPositiveHalf (A ω))
  let Y := fun ω => (gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ,
    reflected_radial_scale γ (Q γ-α₁) h Xc z ω)
  let I := fun ω : Ω × Ω => ∫⁻ t,
    (if 0 < t then ENNReal.ofReal (Real.exp (γ*(D ω.1 (Real.toNNReal t)-(Q γ-α₁)*t))) else 0)
      ∂(Z ω.2).map (fun s => s-(T : ℝ))
  let F := fun p : (ℝ≥0∞ × ℝ) × ℝ≥0∞ => (p.1.1,ENNReal.ofReal p.1.2*p.2)
  have hF : Measurable F := (measurable_fst.comp measurable_fst).prodMk
    (((measurable_snd.comp measurable_fst).ennreal_ofReal).mul measurable_snd)
  have hA := originRadialPath_aemeasurable P X Xc hc hcont
  have hD : AEMeasurable D P :=
    (continuous_brownianShiftPath.measurable.comp
      (measurable_const.prodMk continuous_radialPositiveHalf.measurable)).comp_aemeasurable hA
  have hI : AEMeasurable I (P.prod P) := reflected_translated_polar_aemeasurable
    P D hD Z hL.2.2.2.1 hL.2.2.2.2.1 γ (Q γ-α₁) T
  have ho := (reflected_outerMass_measure_measurable γ α₁ α₂ α₃ ξ z).comp_aemeasurable
    (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ₂ M hM)
  have ht := (hc.2.1 0 (-Real.log ‖z‖+h)).aemeasurable
  have hb : AEMeasurable (reflected_radial_scale γ (Q γ-α₁) h Xc z) P :=
    ((ht.const_mul γ).sub aemeasurable_const).sub aemeasurable_const |>.exp
  have hpack := ((ho.prodMk hb).comp_quasiMeasurePreserving
    measurePreserving_fst.quasiMeasurePreserving).prodMk hI
  change AEMeasurable (fun ω : Ω × Ω => (Y ω.1,I ω)) (P.prod P) at hpack
  have he := reflected_source_copied_radial_restart P Xc hcont γ α₁ h M N heq z hz0 T hcoord
  have hp : (fun ω : Ω × Ω =>
      (gammaHalfOuterMass γ α₁ α₂ α₃ (M ω.1) z ξ,
        ENNReal.ofReal (‖z‖^(γ^2/2))*(∫⁻ x in {x : ℂ | 0 < ‖x‖ ∧ ‖x‖ < Real.exp (-(T : ℝ))},
          ENNReal.ofReal (‖x‖^(-(γ*α₁)))*
            ENNReal.ofReal (reflected_global_reinsertionWeight γ (A ω.1) x) ∂N ω.2))) =ᵐ[P.prod P]
      F ∘ (fun ω : Ω × Ω => (Y ω.1,I ω)) := by
    filter_upwards [he] with ω hω
    exact Prod.ext rfl hω
  rw [Measure.map_congr hp,← AEMeasurable.map_map_of_aemeasurable hF.aemeasurable hpack]
  exact congrArg (fun μ => μ.map F) (reflected_source_copied_williams_joint_law
    P X hX Xc hc hm hcont γ hγ hγ₂ M hM N hN hi heq hfin α₁ α₂ α₃ ξ h hα₁
    B hL hData Qν hQν z T hcoord hr hz hT)

end DOZZ.Proofs

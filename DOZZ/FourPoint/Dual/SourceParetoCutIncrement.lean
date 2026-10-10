/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.SourceParetoWeights
public import DOZZ.FourPoint.Dual.ReflectionCutPositivity
import Mathlib.Tactic
/-! The signed Pareto estimate on the supplied field, chaos and reflection data. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
namespace DOZZ.Proofs

/-- All random moment and measurability hypotheses of the Pareto product estimate are proved
from the supplied field/chaos and reflection data. Its two scalar factors are the actual leading
charge-shift moment and first-order freezing moment. -/
theorem dual_source_pareto_cut_increment_error
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (α₁ α₂ α₃ ξ h p c : ℝ) (hα₁ : α₁ < Q γ) (hreflect : Q γ-α₁ < γ/2)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (hh : 0 ≤ h) (hp : 0 < p)
    (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α₁ B Z)
    (z : ℂ) (hz0 : z ≠ 0) (hz1 : z ≠ 1) (hz : ‖z‖ ≤ 1) :
    let ν := Q γ-α₁
    let a := 2*ν/γ
    let A := fun ω => (dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ).toReal
    let b := dual_radial_scale γ ν h Xc z
    let S := fun ω => (twoSidedReflectionCutMass γ c B Z ω).toReal
    let E := fun v : Ω × Ω => ∫ w,
      ((A v.1+b v.1*S v.2*w)^(-p)-(A v.1)^(-p)) ∂paretoMeasure 1 a
    let L := (∫⁻ ω, ENNReal.ofReal ((b ω)^a)*
      dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^(-(p+a)) ∂P).toReal
    let F := (∫⁻ ω, ENNReal.ofReal (b ω)*
      dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^(-(p+1)) ∂P).toReal
    Integrable E (P.prod P) ∧
      |(∫ v, E v ∂P.prod P)-(a*Real.Gamma (-a)*Real.Gamma (p+a)/Real.Gamma p)*
        L*(∫⁻ ω, twoSidedReflectionCutMass γ c B Z ω ^a ∂P).toReal| ≤
      (a*p/(1-a))*F*(∫⁻ ω, twoSidedReflectionCutMass γ c B Z ω ∂P).toReal := by
  let _ : IsProbabilityMeasure P := hX.1
  let ν := Q γ-α₁
  let a := 2*ν/γ
  let A := fun ω => (dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ).toReal
  let b := dual_radial_scale γ ν h Xc z
  let S := fun ω => (twoSidedReflectionCutMass γ c B Z ω).toReal
  have hν : 0 < ν := sub_pos.mpr hα₁
  have ha : 0 < a := div_pos (mul_pos (by norm_num) hν) hγ
  have ha1 : a < 1 := by
    dsimp only [a]
    rw [div_lt_one hγ]
    linarith only [hreflect]
  have h4 : 1 < 4/γ^2 := by
    rw [lt_div_iff₀ (sq_pos_of_pos hγ)]
    nlinarith only [hγ,hγ₂]
  have hS1 := dual_reflection_cut_real_moment P γ α₁ 1 c B Z hα₁ hData (by norm_num) h4
  have hSa := dual_reflection_cut_real_moment P γ α₁ a c B Z hα₁ hData ha.le (ha1.trans h4)
  have hSp : ∀ᵐ ω ∂P, 0 < S ω :=
    (dual_reflection_cut_positive_finite_ae P γ α₁ c hγ hγ₂ B Z hα₁ hData).mono
      fun ω hω => ENNReal.toReal_pos hω.1.ne' hω.2.ne
  have hSm : AEMeasurable S P :=
    (twoSidedReflectionCutMass_aemeasurable P γ c B Z
      (conditionedPair_aemeasurable P B ν hData.1) hData.2.1.2.2.2.1 hData.2.1.2.2.2.2.1).ennreal_toReal
  have hAm : AEMeasurable A P :=
    ((dual_outerMass_measure_measurable γ α₁ α₂ α₃ ξ z).comp_aemeasurable
      (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ₂ M hM)).ennreal_toReal
  have hcoord : AEMeasurable (fun ω => Xc ω 0 (-Real.log ‖z‖+h)) P :=
    (hc.2.1 0 (-Real.log ‖z‖+h)).aemeasurable
  have hbm : AEMeasurable b P := by
    dsimp only [b,dual_radial_scale]
    exact ((hcoord.const_mul γ).sub aemeasurable_const).sub aemeasurable_const |>.exp
  have hbp (ω : Ω) : 0 < b ω := by
    dsimp only [b,dual_radial_scale]
    exact Real.exp_pos _
  obtain ⟨hAp,hF0,hF1⟩ := dual_source_pareto_weights_integrable P X hX γ hγ hγ₂ M hM
    Xc hc ν h p α₁ α₂ α₃ ξ hν hh hp hξ hξ1 hα₁ hα₂ hα₃ z hz0 hz1 hz
  have hsource0 := dual_radial_scale_real_expectation P X hX γ hγ hγ₂ M hM Xc hc
    ν h a α₁ α₂ α₃ ξ (p+a) hh hξ hξ1 (add_pos hp ha).le z hz0 hz
  have hsource1 := dual_radial_scale_real_expectation P X hX γ hγ hγ₂ M hM Xc hc
    ν h 1 α₁ α₂ α₃ ξ (p+1) hh hξ hξ1 (by linarith only [hp]) z hz0 hz
  have he0 : (∫ ω, (A ω)^(-p)*(b ω/A ω)^a ∂P) =
      (∫⁻ ω, ENNReal.ofReal ((b ω)^a)*
        dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^(-(p+a)) ∂P).toReal := by
    rw [integral_congr_ae (hAp.mono fun ω hω =>
      (reflected_pareto_parameter_weights p a (A ω) (b ω) hω (hbp ω).le).1)]
    simpa only [show -(p+a) = -p-a by ring] using hsource0.2
  have he1 : (∫ ω, (A ω)^(-p)*(b ω/A ω) ∂P) =
      (∫⁻ ω, ENNReal.ofReal (b ω)*
        dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^(-(p+1)) ∂P).toReal := by
    rw [integral_congr_ae (hAp.mono fun ω hω =>
      (reflected_pareto_parameter_weights p a (A ω) (b ω) hω (hbp ω).le).2)]
    simpa only [Real.rpow_one,show -(p+1) = -p-1 by ring] using hsource1.2
  have hhpareto := reflected_pareto_product_increment_error P P p a hp ha ha1 A b S
    hAp (ae_of_all P hbp) hSp hF0 hF1 hSa.1 (by simpa only [Real.rpow_one] using hS1.1)
    hAm hbm hSm
  rw [he0,he1,hSa.2] at hhpareto
  have hS1eq : (∫ ω, S ω ∂P) = (∫⁻ ω, twoSidedReflectionCutMass γ c B Z ω ∂P).toReal := by
    simpa only [Real.rpow_one,ENNReal.rpow_one] using hS1.2
  rw [hS1eq] at hhpareto
  exact hhpareto

end DOZZ.Proofs

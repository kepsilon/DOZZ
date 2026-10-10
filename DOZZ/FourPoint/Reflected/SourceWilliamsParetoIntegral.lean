/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.WilliamsParetoIntegral
public import DOZZ.FourPoint.Reflected.WilliamsRealCutData
public import DOZZ.FourPoint.Reflected.SourceParetoWeights
public import DOZZ.FourPoint.Reflected.ReferenceParetoLaw
import Mathlib.Tactic
/-! Signed Williams expectation bounds on the supplied source and reflection carriers. -/
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The exact Williams/Pareto integral identity holds for the actual retained source
parameters. -/
theorem reflected_source_williams_pareto_integral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (α₁ α₂ α₃ ξ h p : ℝ) (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hh : 0 ≤ h) (hp : 0 < p) (hξ : 0 < ξ) (hξ₁ : ξ < 1)
    (B₀ : Measure BrownianPath) [SFinite B₀] (hB₀ : IsBrownianReal (fun t p => p t) B₀)
    (S : Ω → ℝ) (hS : ∀ᵐ ω ∂P, 0 ≤ S ω) (hSm : AEMeasurable S P)
    (z : ℂ) (hz0 : z ≠ 0) (hz1 : z ≠ 1) (hz : ‖z‖ ≤ 1) :
    let ν := Q γ-α₁
    let A := fun ω => (gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ).toReal
    let b := reflected_radial_scale γ ν h Xc z
    (∫ v : Ω × (ℝ × Ω),
      (A v.1+b v.1*Real.exp (γ*v.2.1)*S v.2.2)^(-p)-(A v.1)^(-p)
        ∂P.prod ((brownianMaximumReferenceLaw ν).prod P)) =
    ∫ v : Ω × Ω, (∫ w,
      (A v.1+b v.1*S v.2*w)^(-p)-(A v.1)^(-p) ∂paretoMeasure 1 (2*ν/γ)) ∂P.prod P := by
  let _ : IsProbabilityMeasure P := hX.1
  let ν := Q γ-α₁
  let μ := brownianMaximumReferenceLaw ν
  let _ : IsProbabilityMeasure μ := isProbabilityMeasure_brownianMaximumReferenceLaw (sub_pos.mpr hα₁)
  let A := fun ω => (gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ).toReal
  let b := reflected_radial_scale γ ν h Xc z
  obtain ⟨hAp,-,-⟩ := reflected_source_pareto_weights_integrable P X hX γ hγ hγ₂ M hM
    Xc hc ν h p α₁ α₂ α₃ ξ (sub_pos.mpr hα₁) hh hp hξ hξ₁ hα₁ hα₂ hα₃ z hz0 hz1 hz
  have hInv := (reflected_radial_scale_real_expectation P X hX γ hγ hγ₂ M hM Xc hc
    ν h 0 α₁ α₂ α₃ ξ p hh hξ hξ₁ hp.le z hz0 hz).1
  simp only [Real.rpow_zero,one_mul] at hInv
  have hAm : AEMeasurable A P :=
    ((reflected_outerMass_measure_measurable γ α₁ α₂ α₃ ξ z).comp_aemeasurable
      (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ₂ M hM)).ennreal_toReal
  have hcoord := (hc.2.1 0 (-Real.log ‖z‖+h)).aemeasurable
  have hbm : AEMeasurable b P := by
    dsimp only [b,reflected_radial_scale]
    exact ((hcoord.const_mul γ).sub aemeasurable_const).sub aemeasurable_const |>.exp
  have hbp : ∀ᵐ ω ∂P, 0 ≤ b ω := ae_of_all P fun _ => (Real.exp_pos _).le
  exact reflected_williams_pareto_integral P P B₀ hB₀ γ ν p hγ (sub_pos.mpr hα₁) hp
    A b S hAp hbp hS hAm hbm hSm hInv

end DOZZ.Proofs

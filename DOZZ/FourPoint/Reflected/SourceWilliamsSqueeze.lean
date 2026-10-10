/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.WilliamsExpectationSqueeze
public import DOZZ.FourPoint.Reflected.WilliamsRealCutData
public import DOZZ.FourPoint.Reflected.SourceParetoWeights
public import DOZZ.FourPoint.Reflected.ReferenceParetoLaw
import Mathlib.Tactic
/-! Signed Williams expectation bounds on the supplied source and reflection carriers. -/
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The actual source inverse moment and actual reflection cut supply the integrated
Williams sandwich. Its bounded-maximum error is the proved source freezing moment. -/
theorem reflected_source_williams_expectation_squeeze
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (α₁ α₂ α₃ ξ h p : ℝ) (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hh : 0 ≤ h) (hp : 0 < p) (hξ : 0 < ξ) (hξ₁ : ξ < 1)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α₁ B Z)
    (B₀ : Measure BrownianPath) [SFinite B₀] (hB₀ : IsBrownianReal (fun t p => p t) B₀)
    (H : ℝ≥0) (hH : 0 < (H : ℝ))
    (z : ℂ) (hz0 : z ≠ 0) (hz1 : z ≠ 1) (hz : ‖z‖ ≤ 1) :
    let ν := Q γ-α₁
    let A := fun ω => (gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ).toReal
    let b := reflected_radial_scale γ ν h Xc z
    let R := (brownianMaximumReferenceLaw ν).prod P
    let J := fun v : ℝ × Ω => (twoSidedReflectionMass γ B Z v.2).toReal
    let K := fun v : ℝ × Ω => (twoSidedReflectionCutMass γ H B Z v.2).toReal
    let j := fun v : ℝ × Ω => (twoSidedReflectionCutMass γ v.1 B Z v.2).toReal
    let D := fun S : ℝ × Ω → ℝ => fun v : Ω × (ℝ × Ω) =>
      (A v.1+b v.1*Real.exp (γ*v.2.1)*S v.2)^(-p)-(A v.1)^(-p)
    Integrable (D j) (P.prod R) ∧
    (∫ v, D J v ∂P.prod R) ≤ (∫ v, D j v ∂P.prod R) ∧
    (∫ v, D j v ∂P.prod R) ≤ (∫ v, D K v ∂P.prod R)+
      p*Real.exp (γ*H)*
        (∫⁻ ω, ENNReal.ofReal (b ω)*gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^(-(p+1)) ∂P).toReal*
        (∫⁻ ω, twoSidedReflectionMass γ B Z ω ∂P).toReal := by
  let _ : IsProbabilityMeasure P := hX.1
  let ν := Q γ-α₁
  let μ := brownianMaximumReferenceLaw ν
  let _ : IsProbabilityMeasure μ := isProbabilityMeasure_brownianMaximumReferenceLaw (sub_pos.mpr hα₁)
  let R := μ.prod P
  let A := fun ω => (gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ).toReal
  let b := reflected_radial_scale γ ν h Xc z
  obtain ⟨hJm,hKm,hjm,hJi,hcuts⟩ := reflected_williams_real_cut_data P μ γ α₁ hγ hγ₂ hα₁
    B Z hData B₀ hB₀ H hH
  obtain ⟨hAp,-,-⟩ := reflected_source_pareto_weights_integrable P X hX γ hγ hγ₂ M hM
    Xc hc ν h p α₁ α₂ α₃ ξ (sub_pos.mpr hα₁) hh hp hξ hξ₁ hα₁ hα₂ hα₃ z hz0 hz1 hz
  have hInv := (reflected_radial_scale_real_expectation P X hX γ hγ hγ₂ M hM Xc hc
    ν h 0 α₁ α₂ α₃ ξ p hh hξ hξ₁ hp.le z hz0 hz).1
  simp only [Real.rpow_zero,one_mul] at hInv
  have hF := reflected_radial_scale_real_expectation P X hX γ hγ hγ₂ M hM Xc hc
    ν h 1 α₁ α₂ α₃ ξ (p+1) hh hξ hξ₁ (by linarith only [hp]) z hz0 hz
  have hAm : AEMeasurable A P :=
    ((reflected_outerMass_measure_measurable γ α₁ α₂ α₃ ξ z).comp_aemeasurable
      (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ₂ M hM)).ennreal_toReal
  have hcoord := (hc.2.1 0 (-Real.log ‖z‖+h)).aemeasurable
  have hbm : AEMeasurable b P := by
    dsimp only [b,reflected_radial_scale]
    exact ((hcoord.const_mul γ).sub aemeasurable_const).sub aemeasurable_const |>.exp
  have hbp : ∀ᵐ ω ∂P, 0 ≤ b ω := ae_of_all P fun _ => (Real.exp_pos _).le
  have hFi : Integrable (fun ω => b ω*(A ω)^(-p-1)) P := by
    simpa only [Real.rpow_one,show -(p+1) = -p-1 by ring] using hF.1
  have hbnd := reflected_williams_expectation_squeeze P R p γ H hp hγ.le A b
    (fun v : ℝ × Ω => v.1) _ _ _ hAp hbp hcuts hAm hbm
      measurable_fst.aemeasurable hJm hKm hjm hInv hFi hJi
  have heF : (∫ ω, b ω*(A ω)^(-p-1) ∂P) =
      (∫⁻ ω, ENNReal.ofReal (b ω)*gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^(-(p+1)) ∂P).toReal := by
    simpa only [Real.rpow_one,show -(p+1) = -p-1 by ring] using hF.2
  have h4 : 1 < 4/γ^2 := by
    rw [lt_div_iff₀ (sq_pos_of_pos hγ)]
    nlinarith only [hγ,hγ₂]
  have heJ : (∫ v : ℝ × Ω, (twoSidedReflectionMass γ B Z v.2).toReal ∂R) =
      (∫⁻ ω, twoSidedReflectionMass γ B Z ω ∂P).toReal := by
    have he := integral_prod_mul (fun _ : ℝ => (1 : ℝ))
      (fun ω => (twoSidedReflectionMass γ B Z ω).toReal) (μ := μ) (ν := P)
    simp only [one_mul,integral_const,probReal_univ,smul_eq_mul] at he
    rw [he]
    simpa only [Real.rpow_one,ENNReal.rpow_one] using
      (reflected_reflection_real_moment P γ α₁ 1 B Z hα₁ hData h4).2
  rw [heF,heJ] at hbnd
  exact hbnd

end DOZZ.Proofs

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.SourceRadialInverseMoment
public import DOZZ.FourPoint.Reflected.ProductInverseExpectation
public import DOZZ.FourPoint.Reflected.SourceOuterMoments
/-! The actual copied radial inverse-moment difference is the signed Williams expectation. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

theorem reflected_source_copied_radial_signed_expectation
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
    (hT : Real.exp (-(T : ℝ)) ≤ ‖z‖^(1-ξ)) (p : ℝ) (hp : 0 ≤ p)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (hz1 : z ≠ 1)
    (hzn : ‖z‖ ≤ 1) (hr1 : ‖z‖^(1-ξ) ≤ 1) :
    (∫⁻ ω : Ω × Ω, (gammaHalfOuterMass γ α₁ α₂ α₃ (M ω.1) z ξ+
      ENNReal.ofReal (‖z‖^(γ^2/2))*(∫⁻ x in {x : ℂ | 0 < ‖x‖ ∧ ‖x‖ < Real.exp (-(T : ℝ))},
        ENNReal.ofReal (‖x‖^(-(γ*α₁)))*
          ENNReal.ofReal (reflected_global_reinsertionWeight γ (originRadialPath Xc ω.1) x) ∂N ω.2))^(-p) ∂P.prod P).toReal-
      (∫⁻ ω, gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ^(-p) ∂P).toReal =
    ∫ v : Ω × (ℝ × Ω),
      ((gammaHalfOuterMass γ α₁ α₂ α₃ (M v.1) z ξ).toReal+
        reflected_radial_scale γ (Q γ-α₁) h Xc z v.1*Real.exp (γ*v.2.1)*
          (twoSidedReflectionCutMass γ v.2.1 B
            (fun ω => lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)) v.2.2).toReal)^(-p)-
        (gammaHalfOuterMass γ α₁ α₂ α₃ (M v.1) z ξ).toReal^(-p)
      ∂P.prod ((brownianMaximumReferenceLaw (Q γ-α₁)).prod P) := by
  let _ : IsProbabilityMeasure P := hX.1
  let ν := Q γ-α₁
  let _ : IsProbabilityMeasure (brownianMaximumReferenceLaw ν) :=
    isProbabilityMeasure_brownianMaximumReferenceLaw (sub_pos.mpr hα₁)
  let μ := (brownianMaximumReferenceLaw ν).prod P
  let A := fun ω => gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ
  let b := reflected_radial_scale γ ν h Xc z
  let Z := fun ω => lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)
  let J := fun v : ℝ × Ω => ENNReal.ofReal (Real.exp (γ*v.1))*twoSidedReflectionCutMass γ v.1 B Z v.2
  have hA : AEMeasurable A P :=
    (reflected_outerMass_measure_measurable γ α₁ α₂ α₃ ξ z).comp_aemeasurable
      (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ₂ M hM)
  have ht := (hc.2.1 0 (-Real.log ‖z‖+h)).aemeasurable
  have hb : AEMeasurable b P :=
    ((ht.const_mul γ).sub aemeasurable_const).sub aemeasurable_const |>.exp
  have hcut := reflected_williams_variable_cut_aemeasurable P (brownianMaximumReferenceLaw ν)
    γ B Z (conditionedPair_aemeasurable P B ν hData.1) hL.2.2.2.1 hL.2.2.2.2.1
  have hJ : AEMeasurable J μ :=
    (((measurable_fst.const_mul γ).exp.ennreal_ofReal).aemeasurable).mul hcut
  have hAf : ∀ᵐ ω ∂P, A ω ≠ ⊤ :=
    (reflected_source_outerMass_positive_finite_ae P X hX γ hγ hγ₂ M hM
      α₁ α₂ α₃ ξ hα₁ hα₂ hα₃ z hz0 hz1 hzn hr1).mono fun _ hω => hω.2.ne
  have hbf : ∀ᵐ ω ∂P, 0 ≤ b ω := Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le
  have hJf : ∀ᵐ v ∂μ, J v ≠ ⊤ := by
    filter_upwards [measurePreserving_snd.quasiMeasurePreserving.ae
      (reflected_reflection_mass_positive_finite_ae P γ α₁ B Z hγ hγ₂ hα₁ hData)] with v hv
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ne_top_of_le_ne_top hv.2.ne (twoSidedReflectionCutMass_le_mass γ v.1 B Z v.2))
  obtain ⟨C,_,hC⟩ := reflected_outerMass_inverse_moment_uniform P X hX γ hγ hγ₂ M hM
    α₁ α₂ α₃ p hp
  have hInvFin : (∫⁻ ω, A ω^(-p) ∂P) < ⊤ :=
    lt_of_le_of_lt (hC z ξ hzn hr1) ENNReal.ofReal_lt_top
  have he := (reflected_product_inverse_increment_expectation P μ A b J hA hb hJ hAf hbf hJf p hp hInvFin).2.2
  rw [reflected_source_copied_radial_inverse_moment P X hX Xc hc hm hcont γ hγ hγ₂ M hM
    N hN hi heq hfin α₁ α₂ α₃ ξ h hα₁ B hL hData Qν hQν z hz0 T hcoord hr hz hT p]
  simpa only [A,b,J,Z,ν,μ,ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.exp_pos _).le,
    mul_assoc] using he

end DOZZ.Proofs

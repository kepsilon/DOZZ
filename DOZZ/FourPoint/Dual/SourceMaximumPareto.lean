/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.IncrementIntegrability
public import DOZZ.FourPoint.Dual.ReferencePareto
public import DOZZ.FourPoint.Dual.SourceParetoWeights
/-! Exact independent-maximum transport for the actual source outer mass. -/
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- The actual source outer mass and likelihood allow Fubini transport of every
independent fixed nonnegative inner mass from the maximum to its Pareto variable. -/
theorem dual_source_fixed_maximum_increment_eq_pareto
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (α₁ α₂ α₃ ξ h p : ℝ) (hα₁ : α₁ < Q γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (hh : 0 ≤ h) (hp : 0 < p)
    (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (S : Ω → ℝ) (hSm : AEMeasurable S P) (hS : ∀ᵐ ω ∂P, 0 ≤ S ω)
    (W : Measure BrownianPath) (hW : IsBrownianReal (fun t p => p t) W)
    (z : ℂ) (hz0 : z ≠ 0) (hz1 : z ≠ 1) (hz : ‖z‖ ≤ 1) (hPareto : Integrable (fun v : Ω × Ω => ∫ w,
      ((dualOuterMass γ α₁ α₂ α₃ (M v.1) z ξ).toReal+
        dual_radial_scale γ (Q γ-α₁) h Xc z v.1*S v.2*w)^(-p)-
        (dualOuterMass γ α₁ α₂ α₃ (M v.1) z ξ).toReal^(-p)
        ∂paretoMeasure 1 (2*(Q γ-α₁)/γ)) (P.prod P)) :
    (∫ v : Ω × (ℝ × Ω),
      ((dualOuterMass γ α₁ α₂ α₃ (M v.1) z ξ).toReal+
        dual_radial_scale γ (Q γ-α₁) h Xc z v.1*(Real.exp (γ*v.2.1)*S v.2.2))^(-p)-
        (dualOuterMass γ α₁ α₂ α₃ (M v.1) z ξ).toReal^(-p)
        ∂P.prod ((brownianMaximumReferenceLaw (Q γ-α₁)).prod P)) =
    ∫ v : Ω × Ω, (∫ w,
      ((dualOuterMass γ α₁ α₂ α₃ (M v.1) z ξ).toReal+
        dual_radial_scale γ (Q γ-α₁) h Xc z v.1*S v.2*w)^(-p)-
        (dualOuterMass γ α₁ α₂ α₃ (M v.1) z ξ).toReal^(-p)
        ∂paretoMeasure 1 (2*(Q γ-α₁)/γ)) ∂P.prod P := by
  let _ : IsProbabilityMeasure P := hX.1
  let _ := isProbabilityMeasure_brownianMaximumReferenceLaw (sub_pos.mpr hα₁)
  let A := fun ω => (dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ).toReal
  let b := dual_radial_scale γ (Q γ-α₁) h Xc z
  let V := fun v : ℝ × Ω => Real.exp (γ*v.1)*S v.2
  have hr : ‖z‖^(1-ξ) ≤ 1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow (norm_nonneg z) hz
      (sub_nonneg.mpr hξ1.le)
  have hA : ∀ᵐ ω ∂P, 0 < A ω :=
    (dual_source_outerMass_positive_finite_ae P X hX γ hγ hγ₂ M hM
      α₁ α₂ α₃ ξ hα₁ hα₂ hα₃ z hz0 hz1 hz hr).mono
        (fun ω hω => ENNReal.toReal_pos hω.1.ne' hω.2.ne)
  have hAm : AEMeasurable A P :=
    ((dual_outerMass_measure_measurable γ α₁ α₂ α₃ ξ z).comp_aemeasurable
      (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ₂ M hM)).ennreal_toReal
  have hcoord := (hc.2.1 0 (-Real.log ‖z‖+h)).aemeasurable
  have hbm : AEMeasurable b P := by
    dsimp only [b, dual_radial_scale]
    exact ((hcoord.const_mul γ).sub aemeasurable_const).sub aemeasurable_const |>.exp
  have hVm : AEMeasurable V ((brownianMaximumReferenceLaw (Q γ-α₁)).prod P) := by
    convert (measurable_fst.aemeasurable.const_mul γ).exp.mul hSm.comp_snd using 1
  have hInv : Integrable (fun ω => (A ω)^(-p)) P := by
    have hi := (dual_radial_scale_real_expectation P X hX γ hγ hγ₂ M hM Xc hc
      (Q γ-α₁) h 0 α₁ α₂ α₃ ξ p hh hξ hξ1 hp.le z hz0 hz).1
    simpa only [Real.rpow_zero, one_mul] using hi
  have hV : ∀ᵐ v : ℝ × Ω ∂(brownianMaximumReferenceLaw (Q γ-α₁)).prod P, 0 ≤ V v :=
    (measurePreserving_snd.quasiMeasurePreserving.ae hS).mono
      (fun v hv => mul_nonneg (Real.exp_pos _).le hv)
  have hInt := dual_negative_increment_integrable P _ p hp.le A b V hA
    (ae_of_all _ (fun _ => (Real.exp_pos _).le)) hV hAm hbm hVm hInv
  exact dual_maximum_product_increment_eq_pareto P P W hW γ (Q γ-α₁)
    hγ (sub_pos.mpr hα₁) p A b S hInt hPareto

end DOZZ.Proofs

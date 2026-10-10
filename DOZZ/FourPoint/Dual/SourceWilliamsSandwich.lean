/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.MaximumExpectation
public import DOZZ.FourPoint.Dual.SourceParetoWeights
/-! Integrated maximum sandwich on the actual source reflection witness. -/
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- The actual source retained mass, radial likelihood and random last-cut Williams mass
have an integrable signed inverse-power increment. All inputs come from the supplied GMC
and reflection data. -/
theorem dual_source_williams_expectation_sandwich
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (α₁ α₂ α₃ ξ h p c : ℝ) (hα₁ : α₁ < Q γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (hh : 0 ≤ h) (hp : 0 < p)
    (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α₁ B Z)
    (z : ℂ) (hz0 : z ≠ 0) (hz1 : z ≠ 1) (hz : ‖z‖ ≤ 1) :
    let R := (brownianMaximumReferenceLaw (Q γ-α₁)).prod P
    let A := fun ω => (dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ).toReal
    let b := dual_radial_scale γ (Q γ-α₁) h Xc z
    let E := fun (J : ℝ × Ω → ℝ) (v : Ω × (ℝ × Ω)) =>
      (A v.1+b v.1*(Real.exp (γ*v.2.1)*J v.2))^(-p)-(A v.1)^(-p)
    (∫ v, E (fun q => (twoSidedReflectionMass γ B Z q.2).toReal) v ∂P.prod R) ≤
      (∫ v, E (fun q => (twoSidedReflectionCutMass γ q.1 B Z q.2).toReal) v ∂P.prod R) ∧
    (∫ v, E (fun q => (twoSidedReflectionCutMass γ q.1 B Z q.2).toReal) v ∂P.prod R) ≤
      (∫ v, E (fun q => (twoSidedReflectionCutMass γ c B Z q.2).toReal) v ∂P.prod R) +
      p*Real.exp (γ*c)*(∫ ω, b ω*(A ω)^(-p-1) ∂P)*
        (∫ ω, (twoSidedReflectionMass γ B Z ω).toReal ∂P) := by
  let _ : IsProbabilityMeasure P := hX.1
  let _ := isProbabilityMeasure_brownianMaximumReferenceLaw (sub_pos.mpr hα₁)
  let A := fun ω => (dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ).toReal
  let b := dual_radial_scale γ (Q γ-α₁) h Xc z
  let R := (brownianMaximumReferenceLaw (Q γ-α₁)).prod P
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
  have hInv : Integrable (fun ω => (A ω)^(-p)) P := by
    have hi := (dual_radial_scale_real_expectation P X hX γ hγ hγ₂ M hM Xc hc
      (Q γ-α₁) h 0 α₁ α₂ α₃ ξ p hh hξ hξ1 hp.le z hz0 hz).1
    simpa only [Real.rpow_zero, one_mul] using hi
  have h4 : 1 < 4/γ^2 := by
    rw [lt_div_iff₀ (sq_pos_of_pos hγ)]
    nlinarith only [hγ, hγ₂]
  have hJ₀ := reflected_reflection_real_moment P γ α₁ 1 B Z hα₁ hData h4
  have hJ : Integrable (fun ω => (twoSidedReflectionMass γ B Z ω).toReal) P := by
    simpa only [Real.rpow_one] using hJ₀.1
  have hJm := (twoSidedReflectionMass_aemeasurable_of_lateral P γ B Z
    (aemeasurable_of_twoSidedConditioned hData.1) hData.2.1).ennreal_toReal
  have hJcm := (twoSidedReflectionCutMass_aemeasurable P γ c B Z
    (aemeasurable_of_twoSidedConditioned hData.1) hData.2.1.2.2.2.1
      hData.2.1.2.2.2.2.1).ennreal_toReal
  have hjm := dual_williams_cut_real_aemeasurable P γ α₁ hα₁ B Z hData
  have hJfin := reflected_reflection_mass_positive_finite_ae P γ α₁ B Z
    hγ hγ₂ hα₁ hData
  have hcut : ∀ᵐ q : ℝ × Ω ∂R,
      0 ≤ (twoSidedReflectionCutMass γ q.1 B Z q.2).toReal ∧
      (twoSidedReflectionCutMass γ q.1 B Z q.2).toReal ≤ (twoSidedReflectionMass γ B Z q.2).toReal ∧
      0 ≤ (twoSidedReflectionCutMass γ c B Z q.2).toReal ∧
      (twoSidedReflectionCutMass γ c B Z q.2).toReal ≤ (twoSidedReflectionMass γ B Z q.2).toReal ∧
      (c ≤ q.1 → (twoSidedReflectionCutMass γ c B Z q.2).toReal ≤
        (twoSidedReflectionCutMass γ q.1 B Z q.2).toReal) := by
    filter_upwards [dual_williams_cut_real_bounds P γ α₁ c hγ hγ₂ hα₁ B Z hData,
      measurePreserving_snd.quasiMeasurePreserving.ae hJfin] with q hq hf
    exact ⟨hq.1, hq.2.1, ENNReal.toReal_nonneg,
      ENNReal.toReal_mono hf.2.ne (twoSidedReflectionCutMass_le_mass γ c B Z q.2), hq.2.2⟩
  have hF : Integrable (fun ω => b ω*(A ω)^(-p-1)) P := by
    have hf := (dual_radial_scale_real_expectation P X hX γ hγ hγ₂ M hM Xc hc
      (Q γ-α₁) h 1 α₁ α₂ α₃ ξ (p+1) hh hξ hξ1 (by linarith only [hp]) z hz0 hz).1
    simpa only [Real.rpow_one, show -(p+1) = -p-1 by ring] using hf
  have hs := dual_williams_increment_expectation_sandwich P R p γ c hp hγ.le A b
    (fun q => q.1) (fun q => (twoSidedReflectionMass γ B Z q.2).toReal)
    (fun q => (twoSidedReflectionCutMass γ c B Z q.2).toReal)
    (fun q => (twoSidedReflectionCutMass γ q.1 B Z q.2).toReal)
    hA (ae_of_all _ (fun _ => (Real.exp_pos _).le)) hcut hAm hbm
    measurable_fst.aemeasurable hJm.comp_snd hJcm.comp_snd hjm hInv hF (hJ.comp_snd _)
  have he : (∫ q : ℝ × Ω, (twoSidedReflectionMass γ B Z q.2).toReal ∂R) =
      ∫ ω, (twoSidedReflectionMass γ B Z ω).toReal ∂P := by
    simpa only [probReal_univ, one_smul] using
      (integral_fun_snd (μ := brownianMaximumReferenceLaw (Q γ-α₁)) (ν := P)
        (fun ω => (twoSidedReflectionMass γ B Z ω).toReal))
  dsimp only at hs ⊢
  rw [he] at hs
  exact hs

end DOZZ.Proofs

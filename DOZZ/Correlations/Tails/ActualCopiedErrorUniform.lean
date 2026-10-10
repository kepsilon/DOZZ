/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.ActualCopiedErrorMoment
public import DOZZ.Correlations.Tails.CompleteEnvelopeUniform
public import DOZZ.Correlations.Tails.ImprovedChargeUniform
public import DOZZ.Correlations.Tails.OffCenterPinLaw
public import DOZZ.Correlations.Tails.CopiedErrorMassBound

/-! Uniform improved moments of the actual copied insertion error. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

theorem actual_copied_multiplier_error_uniform
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (K : Set ℂ) (hK : IsCompact K) (hz : ∀ z ∈ K, 2 ≤ ‖z‖)
    (Family : ℂ → Set (ℂ → ℝ)) (radius supBound derivBound lowerBound : ℝ)
    (hFamily : UniformPositiveC1Family K Family radius supBound derivBound lowerBound)
    (ρ : ℝ) (hρ : 0 < ρ) (hρR : ρ ≤ min radius 1)
    (Amax g R : ℝ) (hg : 0 < g) (hR : 0 < R)
    (p q : ℝ) (hpq : p.HolderConjugate q) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ z ∈ K, ∀ F ∈ Family z,
      ∀ N : Ω → Measure ℂ, IsGMCOf P (translatedField X Xc z) γ N →
      ∀ α r : ℝ, |α-1/γ| ≤ Amax → 0 < r → r*q+g ≤ 4/γ^2 →
        r*q+g ≤ 2/γ*(Q γ-(α-1/γ)) → r*p ≤ R →
      (∫⁻ u : Ω × Ω,
        (ENNReal.ofReal (Real.exp (γ*Xc u.2 z 0-γ^2*Real.log ‖z‖)) *
          ∫⁻ x in Metric.ball 0 ρ, ENNReal.ofReal
            |copiedMultiplier z γ (Xc u.1 z 0) (Xc u.2 z 0) F x -
              F z*Real.exp (-4*Real.log ‖z‖)| * (ENNReal.ofReal ‖x‖)^(-γ*α) ∂N u.1)^r
        ∂P.prod P) ≤ C := by
  let : IsProbabilityMeasure P := hX.1
  have hfst := measurePreserving_fst (μ := P) (ν := P)
  have hX' := isEquatorGFF_measurePreserving P (P.prod P) Prod.fst hfst X hX
  have hM' := isGMCOf_measurePreserving P (P.prod P) Prod.fst hfst X hX γ M hM
  obtain ⟨L,hL,hEnv⟩ := complete_envelope_moment_uniform_compact (P.prod P)
    K hK hz γ derivBound supBound R hFamily.2.2.1 hFamily.2.1 hR
  obtain ⟨D,hD,hMass⟩ := uniform_correlated_improved_charge_moment (P.prod P)
    (X ∘ Prod.fst) hX' γ hγ hγ2 (M ∘ Prod.fst) hM' ρ hρ
    (hρR.trans (min_le_right _ _)) Amax g hg p q hpq L hL
  refine ⟨D,hD,?_⟩
  intro z hzk F hF N hN α r hα hr hbulk hins hrR
  have hzn := hz z hzk
  let A : Ω × Ω → ℝ := fun q => Xc q.1 z 0
  let B : Ω × Ω → ℝ := fun q => Xc q.2 z 0
  let C : Ω × Ω → ℝ := fun q =>
    (derivBound+supBound*(pinCorrectionEnvelope z γ (A q) (B q)+4))*
      Real.exp (pinCorrectionEnvelope z γ (A q) (B q)+4)
  let S : Ω × Ω → ℝ := fun q => Real.exp (γ*B q-γ^2*Real.log ‖z‖)
  let E : Ω × Ω → ℝ≥0∞ := fun q => ENNReal.ofReal (S q*C q)
  have hd : 0 ≤ derivBound := hFamily.2.2.1
  have hs : 0 ≤ supBound := hFamily.2.1
  have hC (q : Ω × Ω) : 0 ≤ C q := by
    have hD : 0 ≤ pinCorrectionEnvelope z γ (A q) (B q) := by
      unfold pinCorrectionEnvelope
      exact add_nonneg (mul_nonneg
        (div_nonneg (abs_nonneg _) (offCenter_pin_variance_pos z hzn).le)
        (abs_nonneg _)) (sq_nonneg _)
    dsimp [C]
    positivity
  have hpin : Measurable (fun ω => Xc ω z 0) :=
    (hc.1 0).comp (measurable_id.prodMk measurable_const)
  have hA : Measurable A := hpin.comp measurable_fst
  have hB : Measurable B := hpin.comp measurable_snd
  have hD : Measurable (fun q => pinCorrectionEnvelope z γ (A q) (B q)) := by
    unfold pinCorrectionEnvelope
    exact ((continuous_abs.measurable.comp (hB.sub hA)).const_mul _).add_const _
  have hCm : Measurable C := (((hD.add_const 4).const_mul supBound).const_add derivBound).mul
    (hD.add_const 4).exp
  have hSm : Measurable S := ((hB.const_mul γ).sub_const _).exp
  have hE : Measurable E := (hSm.mul hCm).ennreal_ofReal
  have hpinL := offCenter_pin_law P X Xc hX hc z hzn
  have hAL := hpinL.comp hfst.hasLaw
  have hBL := hpinL.comp (measurePreserving_snd (μ := P) (ν := P)).hasLaw
  have hAm : (∫ u, A u ∂P.prod P) = 0 := by
    simpa only [A, Function.comp_def, integral_id_gaussianReal] using hAL.integral_eq
  have hBm : (∫ u, B u ∂P.prod P) = 0 := by
    simpa only [B, Function.comp_def, integral_id_gaussianReal] using hBL.integral_eq
  have hAv : variance A (P.prod P) = 2*Real.log ‖z‖ := by
    simpa only [A, Function.comp_def, variance_id_gaussianReal,
      Real.coe_toNNReal _ (offCenter_pin_variance_pos z hzn).le] using hAL.variance_eq
  have hBv : variance B (P.prod P) = 2*Real.log ‖z‖ := by
    simpa only [B, Function.comp_def, variance_id_gaussianReal,
      Real.coe_toNNReal _ (offCenter_pin_variance_pos z hzn).le] using hBL.variance_eq
  have hEm : (∫⁻ u, E u^(r*p) ∂P.prod P) ≤ L :=
    hEnv z hzk A B hAL.hasGaussianLaw hBL.hasGaussianLaw hAm hBm hAv hBv
      (r*p) (mul_pos hr hpq.pos) hrR
  have hY := translated_field_isEquatorGFF P X Xc hX hc z
  have hY' := isEquatorGFF_measurePreserving P (P.prod P) Prod.fst hfst _ hY
  have hN' := isGMCOf_measurePreserving P (P.prod P) Prod.fst hfst _ hY γ _ hN
  have hm := hMass _ (N ∘ Prod.fst) hY' hN' α r hα hr hbulk hins E hE.aemeasurable hEm
  apply le_trans (lintegral_mono fun u => ?_) hm
  apply ENNReal.rpow_le_rpow _ hr.le
  have he := copied_multiplier_error_mass_le K Family radius supBound derivBound
    lowerBound hFamily z hzk hzn F hF γ α (A u) (B u) ρ hγ.ne' hρR (N u.1)
  have h := mul_le_mul' (le_refl (ENNReal.ofReal (S u))) he
  simpa only [E, ENNReal.ofReal_mul (Real.exp_nonneg _), mul_assoc, S, C, A, B,
    Function.comp_def] using h


end DOZZ.Proofs

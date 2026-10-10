/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.FirstOrderSingularError
public import DOZZ.Correlations.Tails.CompleteCopiedEnvelope
public import DOZZ.Correlations.Tails.CopiedWeightTestLimit

/-! Improved moments of the actual copied-multiplier error near the insertion. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

theorem actual_copied_multiplier_error_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (K : Set ℂ) (Family : ℂ → Set (ℂ → ℝ))
    (radius supBound derivBound lowerBound : ℝ)
    (hFamily : UniformPositiveC1Family K Family radius supBound derivBound lowerBound)
    (z : ℂ) (hzk : z ∈ K) (hz : 2 ≤ ‖z‖) (F : ℂ → ℝ) (hF : F ∈ Family z)
    (N : Ω → Measure ℂ) (hN : IsGMCOf P (translatedField X Xc z) γ N)
    (α : ℝ) (hα : α < Q γ) (r : ℝ) (hr : 0 < r)
    (hrange : r < min (reflectionExponent γ α+2/γ^2) (4/γ^2))
    (ρ : ℝ) (hρ : 0 < ρ) (hρR : ρ ≤ min radius 1) :
    (∫⁻ q : Ω × Ω,
      (ENNReal.ofReal (Real.exp (γ*Xc q.2 z 0-γ^2*Real.log ‖z‖)) *
        ∫⁻ x in Metric.ball 0 ρ, ENNReal.ofReal
          |copiedMultiplier z γ (Xc q.1 z 0) (Xc q.2 z 0) F x -
            F z*Real.exp (-4*Real.log ‖z‖)| * (ENNReal.ofReal ‖x‖)^(-γ*α) ∂N q.1)^r
      ∂P.prod P) < ⊤ := by
  let : IsProbabilityMeasure P := hX.1
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
        (div_nonneg (abs_nonneg _) (offCenter_pin_variance_pos z hz).le)
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
  obtain ⟨hG, hmean⟩ := circleAverage_isGaussianProcess P X Xc hX hc
  have hpinG := hG.hasGaussianLaw_eval (z, (0 : ℝ))
  have hpinL : HasLaw (fun ω => Xc ω z 0)
      (gaussianReal 0 (variance (fun ω => Xc ω z 0) P).toNNReal) P := by
    refine ⟨hpinG.aemeasurable, ?_⟩
    rw [hpinG.map_eq_gaussianReal, hmean]
  have hAL := hpinL.comp (measurePreserving_fst (μ := P) (ν := P)).hasLaw
  have hBL := hpinL.comp (measurePreserving_snd (μ := P) (ν := P)).hasLaw
  have hAm : (∫ q, A q ∂P.prod P) = 0 := by
    simpa only [A, Function.comp_def, integral_id_gaussianReal] using hAL.integral_eq
  have hBm : (∫ q, B q ∂P.prod P) = 0 := by
    simpa only [B, Function.comp_def, integral_id_gaussianReal] using hBL.integral_eq
  have hEm (s : ℝ) (hs' : 0 < s) : (∫⁻ q, E q^s ∂P.prod P) < ⊤ :=
    complete_copied_error_envelope_moment (P.prod P) A B hAL.hasGaussianLaw
      hBL.hasGaussianLaw hAm hBm z hz γ derivBound supBound s hd hs hs'.le
  have hY := translated_field_isEquatorGFF P X Xc hX hc z
  have hfst := measurePreserving_fst (μ := P) (ν := P)
  have hY' := isEquatorGFF_measurePreserving P (P.prod P) Prod.fst hfst _ hY
  have hN' := isGMCOf_measurePreserving P (P.prod P) Prod.fst hfst _ hY γ _ hN
  have hm := correlated_improved_charge_moment (P.prod P) _ hY'
    γ hγ hγ2 (N ∘ Prod.fst) hN' α hα r hr hrange 0 ρ hρ E hE.aemeasurable hEm
  apply lt_of_le_of_lt (lintegral_mono fun q => ?_) hm
  apply ENNReal.rpow_le_rpow _ hr.le
  have he := first_order_singular_mass_le γ α (C q) hγ.ne' (hC q)
    (fun x => copiedMultiplier z γ (A q) (B q) F x-F z*Real.exp (-4*Real.log ‖z‖)) ρ
    (fun x hx => copied_multiplier_local_bound K Family radius supBound derivBound
      lowerBound hFamily z hzk hz F hF γ (A q) (B q) x
      ((show ‖x‖ < ρ from by simpa only [Metric.mem_ball, dist_zero_right] using hx).le.trans hρR))
    (N q.1)
  have h := mul_le_mul' (le_refl (ENNReal.ofReal (S q))) he
  simpa only [E, ENNReal.ofReal_mul (Real.exp_nonneg _), mul_assoc, S, A, B,
    Function.comp_def] using h


end DOZZ.Proofs

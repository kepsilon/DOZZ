/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.ActualCopiedErrorUniform
public import DOZZ.Correlations.Tails.CopiedErrorMeasurability
public import DOZZ.Correlations.Tails.PrefactoredAnnularRemainder
public import DOZZ.GMC.WeightedCutoff.RadiusDecomposition

/-! The actual copied multiplier and localization remainders have one uniform moment bound. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

theorem total_copied_remainder_uniform
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (K : Set ℂ) (hK : IsCompact K) (hz : ∀ z ∈ K, 2 ≤ ‖z‖)
    (Family : ℂ → Set (ℂ → ℝ)) (radius supBound derivBound lowerBound : ℝ)
    (hFamily : UniformPositiveC1Family K Family radius supBound derivBound lowerBound)
    (ρ : ℝ) (hρ : 0 < ρ) (hρR : ρ ≤ min radius 1)
    (A Amax g R pH qH : ℝ) (hg : 0 < g) (hR : 0 < R)
    (hRbulk : R < 4/γ^2) (hpq : pH.HolderConjugate qH) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ z ∈ K, ∀ F ∈ Family z,
      ∀ N : Ω → Measure ℂ, IsGMCOf P (translatedField X Xc z) γ N →
      ∀ α r : ℝ, 0 ≤ α → α ≤ A → |α-1/γ| ≤ Amax → 0 < r → r ≤ R →
        r*qH+g ≤ 4/γ^2 → r*qH+g ≤ 2/γ*(Q γ-(α-1/γ)) →
      let E := fun q : Ω × Ω =>
        ENNReal.ofReal (Real.exp (γ*Xc q.2 z 0-γ^2*Real.log ‖z‖)) *
          (∫⁻ x in Metric.ball (0 : ℂ) ρ, ENNReal.ofReal
            |copiedMultiplier z γ (Xc q.1 z 0) (Xc q.2 z 0) F x-
              F z*Real.exp (-4*Real.log ‖z‖)| * (ENNReal.ofReal ‖x‖)^(-γ*α) ∂N q.1)+
        ENNReal.ofReal (F z*‖z‖^(-4 : ℝ)*Real.exp (γ*Xc q.2 z 0-γ^2*Real.log ‖z‖))*
          (∫⁻ x in Metric.ball (0 : ℂ) 1 \ Metric.ball (0 : ℂ) (ρ/4),
            (ENNReal.ofReal ‖x‖)^(-γ*α) ∂N q.1)
      AEMeasurable E (P.prod P) ∧ (∫⁻ q, E q^r ∂P.prod P) ≤ C := by
  let : IsProbabilityMeasure P := hX.1
  obtain ⟨D,hD,hError⟩ := actual_copied_multiplier_error_uniform P X Xc hX hc
    γ hγ hγ2 M hM K hK hz Family radius supBound derivBound lowerBound hFamily
    ρ hρ hρR Amax g (R*pH) hg (mul_pos hR hpq.pos) pH qH hpq
  have hδ : 0 < ρ/4 := by positivity
  have hδ1 : ρ/4 ≤ 1 := by linarith only [hρR.trans (min_le_right _ _),hρ]
  obtain ⟨L,hL,hAnn⟩ := prefactored_annular_remainder_moment_uniform P X Xc hX hc
    γ hγ hγ2 M hM K hK hz (ρ/4) A supBound R hδ hδ1 hFamily.2.1 hR hRbulk
  have htwo : (2 : ℝ≥0∞)^R ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hR.le (by norm_num)
  refine ⟨(2 : ℝ≥0∞)^R*(D+L),ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr htwo)
    (ENNReal.add_lt_top.mpr ⟨hD,hL⟩),?_⟩
  intro z hzk F hF N hN α r hα hαA hαmax hr hrR hbulk hins
  dsimp only
  let E₁ := fun q : Ω × Ω =>
    ENNReal.ofReal (Real.exp (γ*Xc q.2 z 0-γ^2*Real.log ‖z‖)) *
      (∫⁻ x in Metric.ball (0 : ℂ) ρ, ENNReal.ofReal
        |copiedMultiplier z γ (Xc q.1 z 0) (Xc q.2 z 0) F x-
          F z*Real.exp (-4*Real.log ‖z‖)| * (ENNReal.ofReal ‖x‖)^(-γ*α) ∂N q.1)
  let E₂ := fun q : Ω × Ω =>
    ENNReal.ofReal (F z*‖z‖^(-4 : ℝ)*Real.exp (γ*Xc q.2 z 0-γ^2*Real.log ‖z‖))*
      (∫⁻ x in Metric.ball (0 : ℂ) 1 \ Metric.ball (0 : ℂ) (ρ/4),
        (ENNReal.ofReal ‖x‖)^(-γ*α) ∂N q.1)
  obtain ⟨hFm,hFb,_,_,_⟩ := hFamily.2.2.2.2 z hzk F hF
  have hFz : 0 ≤ F z ∧ F z ≤ supBound := ⟨(hFb z).1,
    (le_abs_self (F z)).trans (hFb z).2⟩
  have hE₁ := copied_error_mass_aemeasurable P X Xc hX hc γ hγ hγ2 z N hN F hFm α ρ
  have hE₂ := prefactored_annular_remainder_aemeasurable P X Xc hX hc
    γ hγ hγ2 z (F z) α (ρ/4) N hN
  change AEMeasurable E₁ (P.prod P) at hE₁
  change AEMeasurable E₂ (P.prod P) at hE₂
  change AEMeasurable (fun q => E₁ q+E₂ q) (P.prod P) ∧ _
  refine ⟨hE₁.add hE₂,?_⟩
  have h₁ : (∫⁻ q, E₁ q^r ∂P.prod P) ≤ D := hError z hzk F hF N hN α r hαmax hr hbulk hins
    (mul_le_mul_of_nonneg_right hrR hpq.pos.le)
  have h₂ : (∫⁻ q, E₂ q^r ∂P.prod P) ≤ L := hAnn z hzk (F z) hFz.1 hFz.2 N hN α r hα hαA hr hrR
  calc _ ≤ ∫⁻ q, (2 : ℝ≥0∞)^R*(E₁ q^r+E₂ q^r) ∂P.prod P :=
        lintegral_mono fun q => ennreal_rpow_add_le_uniform_order_cap _ _ r R hr.le hrR
    _ = (2 : ℝ≥0∞)^R*((∫⁻ q, E₁ q^r ∂P.prod P)+(∫⁻ q, E₂ q^r ∂P.prod P)) := by
        rw [lintegral_const_mul' _ _ htwo,lintegral_add_right' _ (hE₂.pow_const r)]
    _ ≤ (2 : ℝ≥0∞)^R*(D+L) := mul_le_mul' le_rfl (add_le_add h₁ h₂)


end DOZZ.Proofs

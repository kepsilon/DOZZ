/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.LocalizationMasses
public import DOZZ.Correlations.Tails.PrefactoredCopiedComparison
public import DOZZ.Correlations.Tails.CopiedLocalizedMeasurability
public import DOZZ.Correlations.Tails.CopiedErrorMeasurability
public import DOZZ.Correlations.Tails.PrefactoredAnnularRemainder

/-! Actual law, measurability and pointwise comparisons for the one-insertion localization. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

theorem localized_insertion_comparison_data
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (K : Set ℂ) (Family : ℂ → Set (ℂ → ℝ))
    (radius supBound derivBound lowerBound : ℝ)
    (hFamily : UniformPositiveC1Family K Family radius supBound derivBound lowerBound)
    (z : ℂ) (hzk : z ∈ K) (hz : 2 ≤ ‖z‖) (F : ℂ → ℝ) (hF : F ∈ Family z)
    (N : Ω → Measure ℂ) (hN : IsGMCOf P (translatedField X Xc z) γ N)
    (α ρ : ℝ) (hα : 0 ≤ α) (hρ : 0 < ρ) (hρR : ρ ≤ min radius 1)
    (χ : BoundedContinuousFunction ℂ ℝ) (hχc : HasCompactSupport (χ : ℂ → ℝ))
    (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (hχs : tsupport (χ : ℂ → ℝ) ⊆ Metric.ball 0 ρ)
    (hχone : ∀ x ∈ Metric.closedBall (0 : ℂ) (ρ/4), χ x = 1) :
    P.map (localizedOriginal M χ F z γ α) =
        (P.prod P).map (localizedCopy N Xc χ F z γ α) ∧
    AEMeasurable (localizedOriginal M χ F z γ α) P ∧
    AEMeasurable (localizedCopy N Xc χ F z γ α) (P.prod P) ∧
    AEMeasurable (originalAnnular M F z γ α (ρ/4)) P ∧
    AEMeasurable (copiedRemainder N Xc F z γ α ρ) (P.prod P) ∧
    (∀ᵐ ω ∂P, localizedOriginal M χ F z γ α ω ≤ localSingularMass M F z γ α ω ∧
      localSingularMass M F z γ α ω ≤ localizedOriginal M χ F z γ α ω+
        originalAnnular M F z γ α (ρ/4) ω) ∧
    (∀ᵐ q ∂P.prod P, localizedCopy N Xc χ F z γ α q ≤
        canonicalLeading N Xc (F z) z γ α q+copiedRemainder N Xc F z γ α ρ q ∧
      canonicalLeading N Xc (F z) z γ α q ≤
        localizedCopy N Xc χ F z γ α q+copiedRemainder N Xc F z γ α ρ q) := by
  let : IsProbabilityMeasure P := hX.1
  have hFm := (hFamily.2.2.2.2 z hzk F hF).1
  have hF0 (x : ℂ) : 0 ≤ F x := (hFamily.2.2.2.2 z hzk F hF).2.1 x |>.1
  have hχzero (x : ℂ) (hx : x ∉ Metric.ball (0 : ℂ) ρ) : χ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (hχs h))
  have hone (x : ℂ) (hx : x ∈ Metric.ball (0 : ℂ) (ρ/4)) : χ x = 1 :=
    hχone x (Metric.ball_subset_closedBall hx)
  have hρ1 : ρ ≤ 1 := hρR.trans (min_le_right _ _)
  have hχchart := hχs.trans (Metric.ball_subset_ball hρR)
  have hl := localized_copied_singular_law P X Xc hX hc hm γ hγ hγ2 M hM
    K Family radius supBound derivBound lowerBound hFamily z hzk hz F hF N hN
    χ hχc (fun x => (hχ x).1) hχchart (γ*α) (mul_nonneg hγ.le hα)
  have hLm : AEMeasurable (localizedOriginal M χ F z γ α) P := by
    have hk : Measurable (fun y : ℂ => ENNReal.ofReal (χ (y-z)*F y)*
      (ENNReal.ofReal ‖y-z‖)^(-γ*α)) := by fun_prop
    have h := (Measure.measurable_lintegral hk).comp_aemeasurable
      (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ2 M hM)
    change AEMeasurable (fun ω => ∫⁻ y, ENNReal.ofReal (χ (y-z)*F y)*(ENNReal.ofReal ‖y-z‖)^(-γ*α) ∂M ω) P
    simpa only [Function.comp_def] using h
  have hAm : AEMeasurable (originalAnnular M F z γ α (ρ/4)) P := by
    have hk : Measurable (fun y : ℂ => ENNReal.ofReal (F y)*(ENNReal.ofReal ‖y-z‖)^(-γ*α)) := by fun_prop
    have hd : MeasurableSet (Metric.ball z 1 \ Metric.ball z (ρ/4)) :=
      Metric.isOpen_ball.measurableSet.diff Metric.isOpen_ball.measurableSet
    have h := (Measure.measurable_lintegral (hk.indicator hd)).comp_aemeasurable
      (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ2 M hM)
    change AEMeasurable (fun ω => ∫⁻ y in Metric.ball z 1 \ Metric.ball z (ρ/4), ENNReal.ofReal (F y)*(ENNReal.ofReal ‖y-z‖)^(-γ*α) ∂M ω) P
    simpa only [lintegral_indicator hd,Function.comp_def] using h
  have hCm := localized_copied_mass_aemeasurable P X Xc hX hc γ hγ hγ2 z N hN
    F χ hFm χ.continuous.measurable α
  have hE₁ := copied_error_mass_aemeasurable P X Xc hX hc γ hγ hγ2 z N hN F hFm α ρ
  have hE₂ := prefactored_annular_remainder_aemeasurable P X Xc hX hc γ hγ hγ2
    z (F z) α (ρ/4) N hN
  refine ⟨?_,hLm,hCm,hAm,hE₁.add hE₂,ae_of_all P ?_,ae_of_all (P.prod P) ?_⟩
  · change P.map (fun ω => ∫⁻ y, ENNReal.ofReal (χ (y-z)*F y)*(ENNReal.ofReal ‖y-z‖)^(-γ*α) ∂M ω) =
      (P.prod P).map (fun q => ENNReal.ofReal (Real.exp (γ*Xc q.2 z 0-γ^2*Real.log ‖z‖))*
        ∫⁻ x, ENNReal.ofReal (χ x*copiedMultiplier z γ (Xc q.1 z 0) (Xc q.2 z 0) F x)*
          (ENNReal.ofReal ‖x‖)^(-γ*α) ∂N q.1)
    simpa only [neg_mul] using hl
  · intro ω
    exact original_localized_mass_comparison M z γ α (ρ/4) ρ hρ1 F hFm χ hχ hχzero hone ω
  · intro q
    have h := prefactored_copied_localization_comparison (N q.1) z
      (by linarith only [hz] : 0 < ‖z‖) γ α (Xc q.1 z 0) (Xc q.2 z 0) (ρ/4) ρ
      (by linarith only [hρ]) hρ1 F hFm hF0 χ hχ hχzero hone
    have hi : localSingularMass N (fun _ => 1) 0 γ α q.1 =
        ∫⁻ x in Metric.ball (0 : ℂ) 1, (ENNReal.ofReal ‖x‖)^(-γ*α) ∂N q.1 := by
      rw [localSingularMass,← lintegral_indicator Metric.isOpen_ball.measurableSet]
      simp only [ENNReal.ofReal_one,one_mul,sub_zero,ENNReal.rpow_eq_pow]
      rfl
    simpa only [localizedCopy,canonicalLeading,copiedRemainder,hi] using h


end DOZZ.Proofs

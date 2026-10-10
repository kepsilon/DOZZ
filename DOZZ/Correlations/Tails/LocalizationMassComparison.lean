/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.LocalizationBump
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! Pointwise localization comparisons retain infinite singular masses. -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

theorem localized_mass_comparison
    (μ : Measure ℂ) (z : ℂ) (δ : ℝ)
    (χ : ℂ → ℝ) (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hχzero : ∀ x ∉ Metric.ball z 1, χ x = 0)
    (hχone : ∀ x ∈ Metric.ball z δ, χ x = 1)
    (w : ℂ → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ x, ENNReal.ofReal (χ x)*w x ∂μ) ≤ (∫⁻ x in Metric.ball z 1, w x ∂μ) ∧
    (∫⁻ x in Metric.ball z 1, w x ∂μ) ≤
      (∫⁻ x, ENNReal.ofReal (χ x)*w x ∂μ)+
        (∫⁻ x in Metric.ball z 1 \ Metric.ball z δ, w x ∂μ) := by
  have hball := (Metric.isOpen_ball (x := z) (ε := (1 : ℝ))).measurableSet
  have hdiff := hball.diff ((Metric.isOpen_ball (x := z) (ε := δ)).measurableSet)
  constructor
  · rw [← lintegral_indicator hball]
    apply lintegral_mono
    intro x
    dsimp only
    by_cases hx : x ∈ Metric.ball z 1
    · rw [indicator_of_mem hx]
      exact mul_le_of_le_one_left' (ENNReal.ofReal_le_one.mpr (hχ x).2)
    · rw [indicator_of_notMem hx,hχzero x hx,ENNReal.ofReal_zero,zero_mul]
  · rw [← lintegral_indicator hball,← lintegral_indicator hdiff]
    rw [← lintegral_add_right _ (hw.indicator hdiff)]
    apply lintegral_mono
    intro x
    dsimp only
    by_cases hx : x ∈ Metric.ball z 1
    · rw [indicator_of_mem hx]
      by_cases hxδ : x ∈ Metric.ball z δ
      · rw [hχone x hxδ,ENNReal.ofReal_one,one_mul]
        exact le_self_add
      · exact le_add_of_le_right (by rw [indicator_of_mem (show x ∈ Metric.ball z 1 \ Metric.ball z δ from ⟨hx,hxδ⟩)])
    · rw [indicator_of_notMem hx]
      exact zero_le

theorem copied_mass_comparison
    (μ : Measure ℂ) (δ ρ : ℝ) (hδρ : δ ≤ ρ) (hρ1 : ρ ≤ 1)
    (χ : ℂ → ℝ) (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hχzero : ∀ x ∉ Metric.ball (0 : ℂ) ρ, χ x = 0)
    (hχone : ∀ x ∈ Metric.ball (0 : ℂ) δ, χ x = 1)
    (u v e : ℂ → ℝ≥0∞) (hv : Measurable v) (he : Measurable e)
    (huv : ∀ x ∈ Metric.ball (0 : ℂ) ρ, u x ≤ v x+e x ∧ v x ≤ u x+e x) :
    (∫⁻ x, ENNReal.ofReal (χ x)*u x ∂μ) ≤
      (∫⁻ x in Metric.ball (0 : ℂ) 1, v x ∂μ)+(∫⁻ x in Metric.ball (0 : ℂ) ρ, e x ∂μ) ∧
    (∫⁻ x in Metric.ball (0 : ℂ) 1, v x ∂μ) ≤
      (∫⁻ x, ENNReal.ofReal (χ x)*u x ∂μ)+
        (∫⁻ x in Metric.ball (0 : ℂ) ρ, e x ∂μ)+
        (∫⁻ x in Metric.ball (0 : ℂ) 1 \ Metric.ball (0 : ℂ) δ, v x ∂μ) := by
  have hb := (Metric.isOpen_ball (x := (0 : ℂ)) (ε := (1 : ℝ))).measurableSet
  have hρm := (Metric.isOpen_ball (x := (0 : ℂ)) (ε := ρ)).measurableSet
  have hd := hb.diff ((Metric.isOpen_ball (x := (0 : ℂ)) (ε := δ)).measurableSet)
  have hsub : Metric.ball (0 : ℂ) ρ ⊆ Metric.ball 0 1 := Metric.ball_subset_ball hρ1
  constructor
  · rw [← lintegral_indicator hb,← lintegral_indicator hρm,← lintegral_add_left (hv.indicator hb)]
    apply lintegral_mono
    intro x
    dsimp only
    by_cases hx : x ∈ Metric.ball (0 : ℂ) ρ
    · rw [indicator_of_mem hx,indicator_of_mem (hsub hx)]
      exact (mul_le_of_le_one_left' (ENNReal.ofReal_le_one.mpr (hχ x).2)).trans (huv x hx).1
    · rw [hχzero x hx,ENNReal.ofReal_zero,zero_mul]
      exact zero_le
  · rw [← lintegral_indicator hb,← lintegral_indicator hρm,← lintegral_indicator hd,
      ← lintegral_add_right _ (he.indicator hρm),← lintegral_add_right _ (hv.indicator hd)]
    apply lintegral_mono
    intro x
    dsimp only
    by_cases hx : x ∈ Metric.ball (0 : ℂ) 1
    · rw [indicator_of_mem hx]
      by_cases hxδ : x ∈ Metric.ball (0 : ℂ) δ
      · have hxρ := Metric.ball_subset_ball hδρ hxδ
        rw [hχone x hxδ,ENNReal.ofReal_one,one_mul,indicator_of_mem hxρ]
        exact (huv x hxρ).2.trans le_self_add
      · exact le_add_of_le_right (by rw [indicator_of_mem (show x ∈ Metric.ball (0 : ℂ) 1 \ Metric.ball 0 δ from ⟨hx,hxδ⟩)])
    · rw [indicator_of_notMem hx]
      exact zero_le


end DOZZ.Proofs

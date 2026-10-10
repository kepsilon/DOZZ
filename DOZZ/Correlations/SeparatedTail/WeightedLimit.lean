/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.SeparatedTail.MixedFatou
public import DOZZ.GMC.SharpMoments.LimitWeightedFatou
public import DOZZ.GMC.SharpMoments.WeightedLocalRange

/-! Mixed moments of two bounded weights pass from regularized GMC to the actual GMC. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Metric Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The common-subsequence mixed Fatou lemma applies to any two bounded weights on bounded balls. -/
theorem separatedTail_bounded_weight_mixed_moment_limit_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (z2 z3 : ℂ) (w2 w3 : ℂ → ℝ≥0) (hw2 : Measurable w2) (hw3 : Measurable w3)
    (b2 b3 : ℝ≥0) (hb2 : ∀ y, w2 y ≤ b2) (hb3 : ∀ y, w3 y ≤ b3)
    (a2 a3 : ℝ) (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3)
    (C : ℝ≥0∞) (n₀ : ℕ)
    (hbound : ∀ n : ℕ, n₀ ≤ n →
      (∫⁻ ω, (∫⁻ x in ball z2 1, (w2 (x-z2) : ℝ≥0∞)
        ∂regularizedGMC P Xc γ n ω)^a2 *
        (∫⁻ x in ball z3 1, (w3 (x-z3) : ℝ≥0∞)
          ∂regularizedGMC P Xc γ n ω)^a3 ∂P) ≤ C) :
    (∫⁻ ω, (∫⁻ x in ball z2 1, (w2 (x-z2) : ℝ≥0∞) ∂M ω)^a2 *
      (∫⁻ x in ball z3 1, (w3 (x-z3) : ℝ≥0∞) ∂M ω)^a3 ∂P) ≤ C := by
  have hm (z : ℂ) (w : ℂ → ℝ≥0) (hw : Measurable w) (n : ℕ) :
      AEMeasurable (fun ω => ∫⁻ x in ball z 1, (w (x-z) : ℝ≥0∞)
        ∂regularizedGMC P Xc γ ((n+n₀ : ℕ) : ℝ) ω) P := by
    have hwm := (hw.comp (measurable_id.sub_const z)).coe_nnreal_ennreal
    have h : Measurable (fun ω => ∫⁻ x, (ball z 1).indicator
        (fun x => (w (x-z) : ℝ≥0∞)) x ∂regularizedGMC P Xc γ ((n+n₀ : ℕ) : ℝ) ω) :=
      (Measure.measurable_lintegral (hwm.indicator isOpen_ball.measurableSet)).comp
        (regularizedGMC_measurable P X hX Xc hXc γ _)
    simpa only [lintegral_indicator isOpen_ball.measurableSet] using h.aemeasurable
  have hfin (z : ℂ) (w : ℂ → ℝ≥0) (b : ℝ≥0) (hb : ∀ y, w y ≤ b) (n : ℕ) :
      ∀ᵐ ω ∂P, (∫⁻ x in ball z 1, (w (x-z) : ℝ≥0∞)
        ∂regularizedGMC P Xc γ ((n+n₀ : ℕ) : ℝ) ω) ≠ ⊤ := by
    filter_upwards [regularizedGMC_finite_ae P X hX Xc hXc γ ((n+n₀ : ℕ) : ℝ)] with ω hω
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _))
      (weightedSetLIntegral_le_const_mul _ z 1 w b hb)
  have hgfin (z : ℂ) (w : ℂ → ℝ≥0) (b : ℝ≥0) (hb : ∀ y, w y ≤ b) :
      ∀ᵐ ω ∂P, (∫⁻ x in ball z 1, (w (x-z) : ℝ≥0∞) ∂M ω) ≠ ⊤ := by
    exact ae_of_all P fun ω => by
      have := hM.1 ω
      exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _))
        (weightedSetLIntegral_le_const_mul _ z 1 w b hb)
  apply separatedTail_mixed_moment_le_of_tendstoInMeasure P _ _ _ _
    (hm z2 w2 hw2) (hm z3 w3 hw3) (hfin z2 w2 b2 hb2) (hfin z3 w3 b3 hb3)
    (hgfin z2 w2 b2 hb2) (hgfin z3 w3 b3 hb3)
    ((regularizedGMC_weighted_mass_tendstoInMeasure P X hX γ hγ hγ2 M hM Xc hXc
      z2 1 w2 hw2 b2 hb2).comp (tendsto_add_atTop_nat n₀))
    ((regularizedGMC_weighted_mass_tendstoInMeasure P X hX γ hγ hγ2 M hM Xc hXc
      z3 1 w3 hw3 b3 hb3).comp (tendsto_add_atTop_nat n₀)) a2 a3 ha2 ha3 C
  exact fun n => hbound (n+n₀) (Nat.le_add_left n₀ n)

end DOZZ.Proofs

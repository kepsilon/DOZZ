/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # Comparing two weighted masses on a region where the weights are close

On a measurable region where two weights are bounded and uniformly close away from one point, the
difference of the two weighted masses, against two finite measures without an atom at that point,
is at most the uniform distance times the mass of the region plus the difference of the integrals
of one fixed bounded function against the two measures. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

theorem goodPart_lintegral_toReal_eq (μ : Measure ℂ) [IsFiniteMeasure μ] (Good : Set ℂ)
    (hGood : MeasurableSet Good) (H : ℂ → ℝ≥0∞) (hH : Measurable H) (L : ℝ)
    (hbound : ∀ x ∈ Good, x ≠ 0 → H x ≤ ENNReal.ofReal L) (h0 : μ {0} = 0) :
    (∫⁻ x in Good, H x ∂μ).toReal = ∫ x in Good, (H x).toReal ∂μ := by
  have hne : ∀ᵐ x ∂μ.restrict Good, x ≠ 0 :=
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp h0)
  have hlt : ∀ᵐ x ∂μ.restrict Good, H x < ⊤ := by
    filter_upwards [hne, ae_restrict_mem hGood] with x hx0 hx
    exact lt_of_le_of_lt (hbound x hx hx0) ENNReal.ofReal_lt_top
  exact (integral_toReal hH.aemeasurable hlt).symm

theorem goodPart_integrableOn (μ : Measure ℂ) [IsFiniteMeasure μ] (Good : Set ℂ)
    (hGood : MeasurableSet Good) (H : ℂ → ℝ≥0∞) (hH : Measurable H) (L : ℝ)
    (hbound : ∀ x ∈ Good, x ≠ 0 → H x ≤ ENNReal.ofReal L) (h0 : μ {0} = 0) :
    IntegrableOn (fun x => (H x).toReal) Good μ := by
  have hne : ∀ᵐ x ∂μ.restrict Good, x ≠ 0 :=
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp h0)
  refine Measure.integrableOn_of_bounded (M := max L 0) (measure_ne_top _ _)
    (ENNReal.measurable_toReal.comp hH).aestronglyMeasurable ?_
  filter_upwards [hne, ae_restrict_mem hGood] with x hx0 hx
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  calc (H x).toReal ≤ (ENNReal.ofReal L).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (hbound x hx hx0)
    _ = max L 0 := ENNReal.toReal_ofReal'

/-- The difference of two weighted masses on a region where the weights are uniformly close. -/
theorem goodPart_ofReal_abs_le (μr μ : Measure ℂ) [IsFiniteMeasure μr] [IsFiniteMeasure μ]
    (Good : Set ℂ) (hGood : MeasurableSet Good) (G F : ℂ → ℝ≥0∞) (hG : Measurable G)
    (hF : Measurable F) (L e : ℝ) (he : 0 ≤ e)
    (hbound : ∀ x ∈ Good, x ≠ 0 → G x ≤ ENNReal.ofReal L ∧ F x ≤ ENNReal.ofReal L ∧
      |(G x).toReal - (F x).toReal| ≤ e)
    (h0r : μr {0} = 0) (h0 : μ {0} = 0) :
    ENNReal.ofReal |(∫⁻ x in Good, G x ∂μr).toReal - (∫⁻ x in Good, F x ∂μ).toReal| ≤
      ENNReal.ofReal e * μr Good +
        ENNReal.ofReal |∫ x, Good.indicator (fun x => (F x).toReal) x ∂μr -
          ∫ x, Good.indicator (fun x => (F x).toReal) x ∂μ| := by
  have hGr := goodPart_lintegral_toReal_eq μr Good hGood G hG L (fun x hx hx0 =>
    (hbound x hx hx0).1) h0r
  have hFr := goodPart_lintegral_toReal_eq μr Good hGood F hF L (fun x hx hx0 =>
    (hbound x hx hx0).2.1) h0r
  have hF0 := goodPart_lintegral_toReal_eq μ Good hGood F hF L (fun x hx hx0 =>
    (hbound x hx hx0).2.1) h0
  have hGi := goodPart_integrableOn μr Good hGood G hG L (fun x hx hx0 => (hbound x hx hx0).1) h0r
  have hFi := goodPart_integrableOn μr Good hGood F hF L (fun x hx hx0 => (hbound x hx hx0).2.1)
    h0r
  have hind : ∀ ν : Measure ℂ, ∫ x, Good.indicator (fun x => (F x).toReal) x ∂ν =
      ∫ x in Good, (F x).toReal ∂ν := fun ν => integral_indicator hGood
  rw [hGr, hF0, hind, hind]
  have hne : ∀ᵐ x ∂μr.restrict Good, x ≠ 0 :=
    ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.mp h0r)
  have hdiff : |∫ x in Good, (G x).toReal ∂μr - ∫ x in Good, (F x).toReal ∂μr| ≤
      e * (μr Good).toReal := by
    rw [← integral_sub hGi hFi, ← Real.norm_eq_abs]
    refine norm_setIntegral_le_of_norm_le_const_ae (measure_lt_top _ _) ?_
    filter_upwards [hne, ae_restrict_mem hGood] with x hx0 hx
    rw [Real.norm_eq_abs]
    exact (hbound x hx hx0).2.2
  have htri : |∫ x in Good, (G x).toReal ∂μr - ∫ x in Good, (F x).toReal ∂μ| ≤
      |∫ x in Good, (G x).toReal ∂μr - ∫ x in Good, (F x).toReal ∂μr| +
        |∫ x in Good, (F x).toReal ∂μr - ∫ x in Good, (F x).toReal ∂μ| := by
    have := abs_add_le (∫ x in Good, (G x).toReal ∂μr - ∫ x in Good, (F x).toReal ∂μr)
      (∫ x in Good, (F x).toReal ∂μr - ∫ x in Good, (F x).toReal ∂μ)
    rwa [sub_add_sub_cancel] at this
  calc ENNReal.ofReal |∫ x in Good, (G x).toReal ∂μr - ∫ x in Good, (F x).toReal ∂μ|
      ≤ ENNReal.ofReal (e * (μr Good).toReal +
          |∫ x in Good, (F x).toReal ∂μr - ∫ x in Good, (F x).toReal ∂μ|) :=
        ENNReal.ofReal_le_ofReal (htri.trans (add_le_add_left hdiff _))
    _ ≤ ENNReal.ofReal (e * (μr Good).toReal) +
          ENNReal.ofReal |∫ x in Good, (F x).toReal ∂μr - ∫ x in Good, (F x).toReal ∂μ| :=
        ENNReal.ofReal_add_le
    _ = ENNReal.ofReal e * μr Good +
          ENNReal.ofReal |∫ x in Good, (F x).toReal ∂μr - ∫ x in Good, (F x).toReal ∂μ| := by
        rw [ENNReal.ofReal_mul he, ENNReal.ofReal_toReal (measure_ne_top _ _)]

end DOZZ.Proofs

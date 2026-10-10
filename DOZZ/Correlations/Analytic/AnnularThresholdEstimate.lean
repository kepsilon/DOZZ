/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.PoleSubtracted.MomentBounds
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import DOZZ.Correlations.Analytic.ComplexMassIncrement

/-! The threshold and Hölder estimate for the complex annular increments. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- Splitting at an annular mass threshold converts a small positive moment and a higher
moment envelope into an explicit bound for the complex increment. -/
theorem annular_threshold_estimate
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y D B F : Ω → ℝ≥0∞) (hY : Measurable Y)
    (hB : AEMeasurable B P) (u : ℝ≥0∞) (hu : u ≠ 0) (hu' : u ≠ ⊤)
    (m q : ℝ) (hm : 0 < m) (hq : 1 < q)
    (hsmall : ∀ᵐ ω ∂P, Y ω < u → F ω ≤ u * D ω)
    (hlarge : ∀ᵐ ω ∂P, F ω ≤ B ω) :
    (∫⁻ ω, F ω ∂P) ≤ u * (∫⁻ ω, D ω ∂P) +
      (∫⁻ ω, B ω ^ q ∂P) ^ (1 / q) *
        ((∫⁻ ω, Y ω ^ m ∂P) / u ^ m) ^ (1 / (q / (q - 1))) := by
  let S := {ω | u ≤ Y ω}
  have hS : MeasurableSet S := hY measurableSet_Ici
  let I : Ω → ℝ≥0∞ := S.indicator (fun _ => 1)
  have hI : Measurable I := measurable_const.indicator hS
  have hp : 0 < q / (q - 1) := div_pos (by linarith) (by linarith)
  have hIp : (∫⁻ ω, I ω ^ (q / (q - 1)) ∂P) = P S := by
    have he : (fun ω => I ω ^ (q / (q - 1))) = I := by
      funext ω
      by_cases hω : ω ∈ S
      · simp only [I, Set.indicator_of_mem hω, ENNReal.one_rpow]
      · simp only [I, Set.indicator_of_notMem hω, ENNReal.zero_rpow_of_pos hp]
    rw [he, lintegral_indicator_const hS]
    exact one_mul _
  have hmark : P S ≤ (∫⁻ ω, Y ω ^ m ∂P) / u ^ m := by
    have hs : S ⊆ {ω | u ^ m ≤ Y ω ^ m} :=
      fun ω hω => ENNReal.rpow_le_rpow hω hm.le
    exact (measure_mono hs).trans (meas_ge_le_lintegral_div
      (hY.aemeasurable.pow_const m) ((ENNReal.rpow_pos (pos_iff_ne_zero.mpr hu) hu').ne')
      (ENNReal.rpow_ne_top_of_nonneg hm.le hu'))
  have hbound : ∀ᵐ ω ∂P, F ω ≤ u * D ω + B ω * I ω := by
    filter_upwards [hsmall, hlarge] with ω hs hl
    by_cases hω : ω ∈ S
    · simpa only [I, Set.indicator_of_mem hω, mul_one] using
        hl.trans le_add_self
    · have hy : Y ω < u := lt_of_not_ge hω
      exact (hs hy).trans le_self_add
  calc
    (∫⁻ ω, F ω ∂P) ≤ ∫⁻ ω, u * D ω + B ω * I ω ∂P := lintegral_mono_ae hbound
    _ = u * (∫⁻ ω, D ω ∂P) + ∫⁻ ω, B ω * I ω ∂P := by
      have hbi : AEMeasurable (fun ω => B ω * I ω) P := by
        simpa only [Pi.mul_def] using hB.mul hI.aemeasurable
      rw [lintegral_add_right' (fun ω => u * D ω) hbi,
        lintegral_const_mul' _ _ hu']
    _ ≤ u * (∫⁻ ω, D ω ∂P) +
        (∫⁻ ω, B ω ^ q ∂P) ^ (1 / q) * (P S) ^ (1 / (q / (q - 1))) := by
      exact add_le_add_right (by
        simpa only [hIp] using lintegral_mul_le_holder hB hI.aemeasurable hq) _
    _ ≤ _ := add_le_add_right
      (mul_le_mul_right (ENNReal.rpow_le_rpow hmark
        (show 0 ≤ 1 / (q / (q - 1)) from (one_div_pos.mpr hp).le)) _) _


end DOZZ.Proofs

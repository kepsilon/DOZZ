/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.AnnularThresholdEstimate

/-! The threshold estimate for the a.e. measurable masses of an arbitrary GMC version. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- Passing to a measurable representative permits the threshold estimate for the literal
mass of any `IsGMCOf` version. -/
theorem annular_threshold_estimate_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y D B F : Ω → ℝ≥0∞) (hY : AEMeasurable Y P)
    (hB : AEMeasurable B P) (u : ℝ≥0∞) (hu : u ≠ 0) (hu' : u ≠ ⊤)
    (m q : ℝ) (hm : 0 < m) (hq : 1 < q)
    (hsmall : ∀ᵐ ω ∂P, Y ω < u → F ω ≤ u * D ω)
    (hlarge : ∀ᵐ ω ∂P, F ω ≤ B ω) :
    (∫⁻ ω, F ω ∂P) ≤ u * (∫⁻ ω, D ω ∂P) +
      (∫⁻ ω, B ω ^ q ∂P) ^ (1 / q) *
        ((∫⁻ ω, Y ω ^ m ∂P) / u ^ m) ^ (1 / (q / (q - 1))) := by
  have hs : ∀ᵐ ω ∂P, hY.mk Y ω < u → F ω ≤ u * D ω := by
    filter_upwards [hsmall, hY.ae_eq_mk] with ω hω he
    simpa only [← he] using hω
  have he : (∫⁻ ω, hY.mk Y ω ^ m ∂P) = ∫⁻ ω, Y ω ^ m ∂P := by
    apply lintegral_congr_ae
    filter_upwards [hY.ae_eq_mk] with ω hω
    rw [hω]
  simpa only [he] using annular_threshold_estimate P (hY.mk Y) D B F
    hY.measurable_mk hB u hu hu' m q hm hq hs hlarge

end DOZZ.Proofs

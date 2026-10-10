/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.DifferenceExteriorExpectation
public import DOZZ.FourPoint.Fusion.NormalizedLittleO
public import DOZZ.FourPoint.Fusion.TimeIntegrability
/-! # Negligibility of the signed KRV exterior error -/
@[expose] public section
open MeasureTheory Set Filter Topology
namespace DOZZ.Proofs
/-- The uniform first-order exterior bound is negligible at every exponent below one. -/
theorem fusion_exteriorDifference_normalized_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hα₁ : α₁ < 2 / γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (p : ℝ) (hp : 0 ≤ p) (κ : ℝ) (hκ : κ < 1) :
    Tendsto (fun z : ℂ => (∫ t in Icc (0 : ℝ) 1, ∫ ω,
      (fusionUnrootedSegment γ α₁ α₂ α₃ t z (M ω) ^ (-p - 1)).toReal *
        (∫ x in (Metric.ball (0 : ℂ) (1 / 2))ᶜ, fusionDifferenceKernel γ α₁ α₂ α₃ z x ∂M ω) ∂P) /
      ‖z‖ ^ κ) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
  let E := fun z : ℂ => ∫ t in Icc (0 : ℝ) 1, ∫ ω,
    (fusionUnrootedSegment γ α₁ α₂ α₃ t z (M ω) ^ (-p - 1)).toReal *
      (∫ x in (Metric.ball (0 : ℂ) (1 / 2))ᶜ, fusionDifferenceKernel γ α₁ α₂ α₃ z x ∂M ω) ∂P
  obtain ⟨C, _, hb⟩ := fusion_difference_exterior_expectation_bound P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hα₁ hα₂ hα₃ p hp
  have hE : ∀ z : ℂ, z ≠ 0 → ‖z‖ ≤ 1 / 4 → ‖E z‖ ≤ C * ‖z‖ := by
    intro z hz hz4
    have h := norm_integral_le_of_norm_le (integrable_const (μ := volume.restrict (Icc (0 : ℝ) 1)) (C * ‖z‖))
      (by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        exact (hb t ht z hz hz4).2)
    simpa only [integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Icc,
      sub_zero, ENNReal.ofReal_one, ENNReal.toReal_one, one_smul] using h
  have ho : IsComplexLittleOAtZero κ (fun z => (E z : ℂ)) := by
    apply power_bound_littleO _ κ (1 - κ) C (1 / 4) (by linarith) (by norm_num)
    intro z hz hz4
    simpa only [Complex.norm_real, Real.norm_eq_abs, Real.rpow_one,
      show κ + (1 - κ) = (1 : ℝ) by ring] using hE z hz hz4
  have h := Complex.continuous_re.continuousAt.tendsto.comp (fusion_normalized_tendsto_of_littleO κ _ ho)
  simpa only [Function.comp_def, ← Complex.ofReal_div, Complex.ofReal_re, Complex.zero_re] using h
end DOZZ.Proofs

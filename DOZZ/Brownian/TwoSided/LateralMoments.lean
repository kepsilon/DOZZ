/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.TwoSided.SourceMoments

/-! Uniform positive and inverse moments of the given lateral unit masses. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

/-- A uniform reference inverse moment supplies a uniform annulus inverse moment by retaining
the same-radius disk inside the unit annulus. -/
theorem twosided_source_annulus_inverse_le_reference
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (γ p : ℝ) (M : Ω → Measure ℂ) (Z : Ω → Measure ℝ)
    (hS : IsSourceLateralProjection P X γ M Z) (hγ : 0 < γ) (hγ2 : γ < 2) (hp : p ≤ 0) :
    (∫⁻ ω, (M ω (lateralLogAnnulus 0 1)) ^ p ∂P) ≤
      gmcMassMoment P M (Metric.ball 0 (1 / 8)) p := by
  have hnorm : ‖((3 / 4 : ℝ) : ℂ)‖ + (1 / 8 : ℝ) < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by norm_num)]
    norm_num
  have he := gmc_local_ball_moment_center_eq P X hS.1 γ hγ hγ2 M hS.2.1
    ((3 / 4 : ℝ) : ℂ) 0 (by norm_num : (0 : ℝ) < 1 / 8)
    (by norm_num : (0 : ℝ) < 1 / 8) le_rfl (by norm_num) hnorm (by norm_num) p
  rw [← he]
  apply lintegral_mono
  intro ω
  exact ennreal_rpow_antitone_of_nonpos
    (measure_mono lateralUnitBlock_retained_disk_subset_annulus) hp

/-- Charge-uniform reference inverse bounds transfer to each actual lateral witness. -/
theorem twosided_lateral_unit_inverse_uniform
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Kγ : Set ℝ)
    (Z : ℝ → Ω → Measure ℝ) (hZ : ∀ γ ∈ Kγ, IsLateralGMCOf P γ (Z γ))
    (p : ℝ) (hp : p < 0) (C : ℝ≥0∞) (hC : C < ⊤)
    (hRef : ∀ γ ∈ Kγ, ∀ X M, IsEquatorGFF P X → IsGMCOf P X γ M →
      gmcMassMoment P M (Metric.ball 0 (1 / 8)) p ≤ C) :
    ∃ C' : ℝ≥0∞, C' < ⊤ ∧ ∀ γ ∈ Kγ,
      (∫⁻ ω, (Z γ ω (Ioc 0 1)) ^ p ∂P) ≤ C' := by
  obtain ⟨C', hC', hb⟩ := lateralGMC_uniform_interval_moments_of_all_source_annular
    P Kγ {p} isCompact_singleton Z hZ 0 1 C hC (by
      intro γ hγ q hq X M hS
      have hqp : q = p := mem_singleton_iff.mp hq
      subst q
      exact (twosided_source_annulus_inverse_le_reference P X γ p M (Z γ) hS
        (hZ γ hγ).1 (hZ γ hγ).2.1 hp.le).trans (hRef γ hγ X M hS.1 hS.2.1))
  refine ⟨C', hC', ?_⟩
  intro γ hγ
  simpa only [add_zero] using hb γ hγ p (mem_singleton p) 0

/-- Moving the unit interval into the reference chart allows positive moments to transfer
from one uniform reference bound, without assuming charge regularity of the given family. -/
theorem twosided_lateral_unit_positive_uniform
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Kγ : Set ℝ)
    (Z : ℝ → Ω → Measure ℝ) (hZ : ∀ γ ∈ Kγ, IsLateralGMCOf P γ (Z γ))
    (p : ℝ) (hp : 0 ≤ p) (C : ℝ≥0∞) (hC : C < ⊤)
    (hRef : ∀ γ ∈ Kγ, ∀ X M, IsEquatorGFF P X → IsGMCOf P X γ M →
      gmcMassMoment P M (Metric.ball 0 (1 / 8)) p ≤ C) :
    ∃ C' : ℝ≥0∞, C' < ⊤ ∧ ∀ γ ∈ Kγ,
      (∫⁻ ω, (Z γ ω (Ioc 0 1)) ^ p ∂P) ≤ C' := by
  have hsub : lateralLogAnnulus (Real.log 8) (1 + Real.log 8) ⊆ Metric.ball 0 (1 / 8) := by
    simpa only [sub_zero, zero_add] using lateral_shifted_annulus_subset_reference_ball 0 1
  obtain ⟨C', hC', hb⟩ := lateralGMC_uniform_interval_moments_of_all_source_annular
    P Kγ {p} isCompact_singleton Z hZ (Real.log 8) (1 + Real.log 8) C hC (by
      intro γ hγ q hq X M hS
      have hqp : q = p := mem_singleton_iff.mp hq
      subst q
      apply le_trans _ (hRef γ hγ X M hS.1 hS.2.1)
      exact lintegral_mono fun ω => ENNReal.rpow_le_rpow (measure_mono hsub) hp)
  refine ⟨C', hC', ?_⟩
  intro γ hγ
  simpa only [add_neg_cancel, add_neg_cancel_right] using hb γ hγ p (mem_singleton p)
    (-Real.log 8)

end DOZZ.Proofs

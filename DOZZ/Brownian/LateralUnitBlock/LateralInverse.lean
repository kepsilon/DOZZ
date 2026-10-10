/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Lateral.AnnularComparison
public import DOZZ.GMC.Annulus.LocalScale

/-!
# The precise reference inverse moment needed by the conditional unit-block estimate

A fixed disk of radius `1/8` centered at `3/4` lies strictly inside the source annulus
for `[0,1]`. Its inverse moment equals the reference disk inverse moment by exact local
scaling. This supplies the geometric and radial transfer, while retaining the reference
inverse-moment premise explicitly.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

/-- A single fixed chart disk is retained in the unit logarithmic annulus. -/
theorem lateralUnitBlock_retained_disk_subset_annulus :
    Metric.ball ((3 / 4 : ℝ) : ℂ) (1 / 8) ⊆ lateralLogAnnulus 0 1 := by
  have he : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
    have h := Real.add_one_le_exp (1 : ℝ)
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le
      (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ Real.exp 1)
  have hn : ‖((3 / 4 : ℝ) : ℂ)‖ = (3 / 4 : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by norm_num)]
  intro z hz
  rw [Metric.mem_ball, dist_eq_norm] at hz
  apply (mem_lateralLogAnnulus_iff 0 1 z).mpr
  have hlo := norm_sub_norm_le ((3 / 4 : ℝ) : ℂ) z
  rw [hn, norm_sub_rev] at hlo
  have hhi := norm_add_le (z - ((3 / 4 : ℝ) : ℂ)) ((3 / 4 : ℝ) : ℂ)
  rw [sub_add_cancel, hn] at hhi
  constructor
  · linarith
  · simpa only [neg_zero, Real.exp_zero] using (show ‖z‖ < 1 by linarith)

/-- The source annulus has a finite inverse moment once the source reference disk does. -/
theorem lateralUnitBlock_source_annulus_inverse_finite_of_reference
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (γ q : ℝ) (M : Ω → Measure ℂ) (Z : Ω → Measure ℝ)
    (hS : IsSourceLateralProjection P X γ M Z)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hq : 0 < q)
    (hReference : gmcMassMoment P M (Metric.ball 0 (1 / 8)) (-q) < ⊤) :
    (∫⁻ ω, (M ω (lateralLogAnnulus 0 1)) ^ (-q) ∂P) < ⊤ := by
  have hnorm : ‖((3 / 4 : ℝ) : ℂ)‖ + (1 / 8 : ℝ) < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by norm_num)]
    norm_num
  have hball := (gmc_local_ball_moment_finite_iff P X hS.1 γ hγ hγ2 M hS.2.1
    ((3 / 4 : ℝ) : ℂ) (by norm_num : (0 : ℝ) < 1 / 8)
    (by norm_num : (0 : ℝ) < 1 / 8) le_rfl (by norm_num : (1 / 8 : ℝ) < 1)
    hnorm (-q)).mpr hReference
  apply lt_of_le_of_lt _ hball
  apply lintegral_mono
  intro ω
  change (M ω (lateralLogAnnulus 0 1)) ^ (-q) ≤
    (M ω (Metric.ball ((3 / 4 : ℝ) : ℂ) (1 / 8))) ^ (-q)
  rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
  exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow
    (measure_mono lateralUnitBlock_retained_disk_subset_annulus) hq.le)

/-- The source projection transfers precisely this one reference inverse moment to the
closed lateral unit interval, with no parameter uniformity or stronger moment input. -/
theorem lateralUnitBlock_source_lateral_unit_inverse_finite_of_reference
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (γ q : ℝ) (M : Ω → Measure ℂ) (Z : Ω → Measure ℝ)
    (hS : IsSourceLateralProjection P X γ M Z)
    (hZ : IsLateralGMCOf P γ Z) (hq : 0 < q)
    (hReference : gmcMassMoment P M (Metric.ball 0 (1 / 8)) (-q) < ⊤) :
    (∫⁻ ω, (Z ω (Icc 0 1)) ^ (-q) ∂P) < ⊤ := by
  rw [lateralGMC_Icc_moment_eq_Ioc P γ Z hZ 0 1 (-q) (by norm_num)]
  exact sourceLateral_interval_moment_finite_of_annular P X γ M Z hS hZ.2.2.2.1 0 1 (-q)
    (lateralUnitBlock_source_annulus_inverse_finite_of_reference P X γ q M Z hS hZ.1 hZ.2.1 hq hReference)

/-- A reference inverse-moment hypothesis applies to the actual source witness in the lateral
predicate. The hypothesis is kept as an explicit argument; the reference inverse moment is
proved separately. -/
theorem lateralUnitBlock_lateral_unit_inverse_finite_of_reference
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (γ q : ℝ) (Z : Ω → Measure ℝ) (hZ : IsLateralGMCOf P γ Z) (hq : 0 < q)
    (hReference : ∀ (X : Ω → Distr) (M : Ω → Measure ℂ),
      IsEquatorGFF P X → IsGMCOf P X γ M →
        gmcMassMoment P M (Metric.ball 0 (1 / 8)) (-q) < ⊤) :
    (∫⁻ ω, (Z ω (Icc 0 1)) ^ (-q) ∂P) < ⊤ := by
  obtain ⟨X, M, hS⟩ := hZ.2.2.2.2.2.2.2.2
  exact lateralUnitBlock_source_lateral_unit_inverse_finite_of_reference P X γ q M Z hS hZ hq
    (hReference X M hS.1 hS.2.1)

end DOZZ.Proofs

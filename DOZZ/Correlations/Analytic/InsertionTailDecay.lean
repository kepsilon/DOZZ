/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.SeibergMoment
public import DOZZ.GMC.SharpMoments.WeightedLocalRange
public import DOZZ.GMC.SharpMoments.WeightedUniformGrid

/-! Small positive moments of shrinking insertion disks from a strict charge gap. -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- Increasing the insertion charge by a positive gap gives a deterministic small-radius factor.
Only the root singleton is removed; no first moment is assumed. -/
theorem weighted_mass_charge_gap (μ : Measure ℂ) (γ a δ : ℝ)
    (hγ : 0 < γ) (hδ : 0 < δ) (z : ℂ) (hroot : μ {z} = 0)
    (ρ R : ℝ) (hρ : 0 < ρ) (hρR : ρ ≤ R) :
    weightedGmcBallMass γ μ a z ρ ≤ ENNReal.ofReal (ρ ^ (γ * δ)) *
      weightedGmcBallMass γ μ (a + δ) z R := by
  have hne : ∀ᵐ x ∂μ, x ≠ z := by
    rw [ae_iff]
    simpa only [not_not, ofPred_eq_eq_singleton] using hroot
  have hm : Measurable (fun x : ℂ => ENNReal.ofReal ‖x - z‖ ^ (-γ * (a + δ))) :=
    (ENNReal.measurable_ofReal.comp (measurable_id.sub_const z).norm).pow_const _
  unfold weightedGmcBallMass
  calc
    _ ≤ ∫⁻ x in Metric.ball z ρ, ENNReal.ofReal (ρ ^ (γ * δ)) *
        (ENNReal.ofReal ‖x - z‖ ^ (-γ * (a + δ))) ∂μ := by
      apply setLIntegral_mono_ae' Metric.isOpen_ball.measurableSet
      filter_upwards [hne] with x hx hball
      have hd : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
      have hr : ‖x - z‖ ≤ ρ := by
        exact (show ‖x - z‖ < ρ by simpa only [Metric.mem_ball, dist_eq_norm] using hball).le
      rw [ENNReal.rpow_eq_pow, ENNReal.ofReal_rpow_of_pos hd,
        ENNReal.ofReal_rpow_of_pos hd, ← ENNReal.ofReal_mul (Real.rpow_nonneg hρ.le _)]
      apply ENNReal.ofReal_le_ofReal
      calc
        _ = ‖x - z‖ ^ (γ * δ) * ‖x - z‖ ^ (-γ * (a + δ)) := by
          rw [← Real.rpow_add hd]
          congr 1
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow hd.le hr (mul_pos hγ hδ).le) (Real.rpow_nonneg hd.le _)
    _ = ENNReal.ofReal (ρ ^ (γ * δ)) *
        ∫⁻ x in Metric.ball z ρ, ENNReal.ofReal ‖x - z‖ ^ (-γ * (a + δ)) ∂μ :=
      lintegral_const_mul _ hm
    _ ≤ _ := by
      have hmono : (∫⁻ x in Metric.ball z ρ, ENNReal.ofReal ‖x - z‖ ^ (-γ * (a + δ)) ∂μ) ≤
          ∫⁻ x in Metric.ball z R, ENNReal.ofReal ‖x - z‖ ^ (-γ * (a + δ)) ∂μ :=
        lintegral_mono_set (Metric.ball_subset_ball hρR)
      simpa only [ENNReal.rpow_eq_pow] using
        mul_le_mul (le_refl (ENNReal.ofReal (ρ ^ (γ * δ)))) hmono zero_le zero_le

/-- A single larger-charge moment gives uniform polynomial decay for all smaller charges. -/
theorem weighted_small_ball_moment_decay
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (a δ : ℝ) (hδ : 0 < δ) (ha : a + δ < Q γ)
    (z : ℂ) (R : ℝ) (hR : 0 < R) (m : ℝ) (hm : 0 < m)
    (hms : m < min (4 / γ ^ 2) (2 / γ * (Q γ - (a + δ)))) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ α ≤ a, ∀ ρ : ℝ, 0 < ρ → ρ ≤ min R 1 →
      weightedGmcBallMoment P M γ α z ρ m ≤ ENNReal.ofReal (ρ ^ (γ * δ * m)) * C := by
  let C := weightedGmcBallMoment P M γ (a + δ) z R m
  have hC : C < ⊤ := (equatorGFF_GMC_weighted_local_moment_range
    P X hX γ hγ hγ2 M hM (a + δ) ha m hm z R hR).mpr hms
  refine ⟨C, hC, fun α hα ρ hρ hρR => ?_⟩
  have hatom := gmc_singleton_mass_eq_zero_ae P X hX γ hγ hγ2 M hM z
  have hmeas := gmc_weighted_mass_aemeasurable P X hX γ hγ hγ2 M hM (a + δ) z R
  unfold weightedGmcBallMoment
  calc
    _ ≤ ∫⁻ ω, (ENNReal.ofReal (ρ ^ (γ * δ)) * weightedGmcBallMass γ (M ω) (a + δ) z R) ^ m ∂P := by
      apply lintegral_mono_ae
      filter_upwards [hatom] with ω hω
      apply ENNReal.rpow_le_rpow _ hm.le
      exact (weightedGmcBallMass_mono_charge (M ω) hγ.le z
        (hρR.trans (min_le_right _ _)) hα).trans
        (weighted_mass_charge_gap (M ω) γ a δ hγ hδ z hω ρ R hρ
          (hρR.trans (min_le_left _ _)))
    _ = ENNReal.ofReal (ρ ^ (γ * δ * m)) * C := by
      simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hm.le]
      rw [lintegral_const_mul'' _ (hmeas.pow_const m), ENNReal.ofReal_rpow_of_pos
        (Real.rpow_pos_of_pos hρ _), ← Real.rpow_mul hρ.le]
      rfl

end DOZZ.Proofs

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.SeibergMomentBound
public import DOZZ.Correlations.Analytic.RetainedRegions

/-! A fixed exterior disk supplies all negative moments of retained Coulomb masses. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- A sufficiently large retained region contains the fixed exterior disk used for negative
moments. This inclusion is uniform in the charge vector. -/
theorem exterior_ball_subset_retainedRegion
    {N : ℕ} (z : Fin N → ℂ) (R : ℝ) (hR : 1 ≤ R)
    (hz : ∀ i, 2 * ‖z i‖ ≤ R) (r : ℝ) (hr : 0 ≤ r) (hout : R + 2 ≤ Real.exp r) :
    Metric.ball (((R + 1 : ℝ)) : ℂ) (1 / 8) ⊆ retainedRegion z r := by
  intro x hx
  rw [Metric.mem_ball, dist_eq_norm] at hx
  have hc : ‖(((R + 1 : ℝ)) : ℂ)‖ = R + 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hupper := norm_sub_norm_le x (((R + 1 : ℝ)) : ℂ)
  have hlower := norm_sub_norm_le (((R + 1 : ℝ)) : ℂ) x
  rw [norm_sub_rev, hc] at hlower
  rw [hc] at hupper
  refine ⟨by linarith, fun i => ?_⟩
  have hi := norm_sub_norm_le x (z i)
  have he : Real.exp (-r) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hr)
  linarith [hz i]

/-- The fixed-disk lower bound persists after restricting to a retained region containing that
disk. This applies to every charge vector, without a first-moment condition. -/
theorem retained_coulomb_mass_ge_exterior_ball
    {N : ℕ} (μ : Measure ℂ) (γ : ℝ) (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf : ℝ)
    (O : Set ℂ) (R : ℝ) (hR : 1 ≤ R) (hz : ∀ i, 2 * ‖z i‖ ≤ R)
    (hO : Metric.ball (((R + 1 : ℝ)) : ℂ) (1 / 8) ⊆ O) :
    ENNReal.ofReal ((2 : ℝ) ^ (-∑ j, |γ * α j|)) *
        ENNReal.ofReal ((R + 2) ^ (-|γ * αinf|)) *
        μ (Metric.ball (((R + 1 : ℝ)) : ℂ) (1 / 8)) ≤
      ∫⁻ x in O, coulombWeight γ α z αinf x ∂μ := by
  have hl := coulombMass_ge_exterior_ball (μ.restrict O) γ α z αinf hR hz
  rw [Measure.restrict_apply Metric.isOpen_ball.measurableSet,
    Set.inter_eq_left.mpr hO, coulombMass_eq_lintegral_coulombWeight] at hl
  exact hl

/-- All nonpositive real moments of a retained weighted mass are finite as soon as one fixed
exterior disk is retained. -/
theorem retained_coulomb_mass_nonpos_moment_finite
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α : Fin N → ℝ) (z : Fin N → ℂ) (αinf : ℝ) (O : Set ℂ)
    (R : ℝ) (hR : 1 ≤ R) (hz : ∀ i, 2 * ‖z i‖ ≤ R)
    (hO : Metric.ball (((R + 1 : ℝ)) : ℂ) (1 / 8) ⊆ O) (p : ℝ) (hp : p ≤ 0) :
    (∫⁻ ω, (∫⁻ x in O, coulombWeight γ α z αinf x ∂M ω) ^ p ∂P) < ⊤ := by
  let c := ENNReal.ofReal ((2 : ℝ) ^ (-∑ j, |γ * α j|)) *
    ENNReal.ofReal ((R + 2) ^ (-|γ * αinf|))
  let B := Metric.ball (((R + 1 : ℝ)) : ℂ) (1 / 8)
  have hc0 : c ≠ 0 := mul_ne_zero
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)).ne'
    (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by linarith) _)).ne'
  have hct : c ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hm := gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM B
    Metric.isOpen_ball.measurableSet
  have hi : (∫⁻ ω, M ω B ^ p ∂P) < ⊤ :=
    gmc_ball_moment_lt_top_any_center P X hX γ hγ hγ2 M hM _ (1 / 8)
      (by norm_num) le_rfl p (lt_of_le_of_lt hp (by positivity))
  calc
    _ ≤ ∫⁻ ω, (c * M ω B) ^ p ∂P := lintegral_mono (fun ω =>
      ennreal_rpow_antitone_of_nonpos
        (retained_coulomb_mass_ge_exterior_ball (M ω) γ α z αinf O R hR hz hO) hp)
    _ = c ^ p * (∫⁻ ω, M ω B ^ p ∂P) := by
      simp_rw [ennreal_mul_rpow_of_ne_zero_ne_top _ _ hc0 hct p]
      exact lintegral_const_mul'' _ (hm.pow_const p)
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.rpow_ne_top_of_ne_zero hc0 hct).lt_top hi

end DOZZ.Proofs

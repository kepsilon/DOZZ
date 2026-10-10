/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.TaylorKernelMass

/-! A small-region Taylor mass is controlled by the sharp one-root weighted GMC mass. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- On the small origin disk, the negative degenerate charge supplies its exact radius power. -/
theorem gammaHalf_local_kernel_bound (γ α₁ α₂ α₃ : ℝ) (z x : ℂ) (ρ : ℝ)
    (hρ : 0 < ρ) (hρ2 : ρ ≤ 1 / 2) (hz : ‖z‖ ≤ ρ) (hx : ‖x‖ ≤ ρ) (hx0 : x ≠ 0) :
    ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ≤
      ENNReal.ofReal ((2 : ℝ) ^ |γ * α₂| * (2 * ρ) ^ (γ ^ 2 / 2)) *
        (ENNReal.ofReal ‖x‖) ^ (-γ * α₁) := by
  have hn : normPlus x = 1 := max_eq_left (hx.trans (by linarith only [hρ2]))
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hlow : 1 / 2 ≤ ‖x - 1‖ := by
    have hh := norm_sub_norm_le (1 : ℂ) x
    rw [norm_one, norm_sub_rev] at hh
    linarith only [hh, hx, hρ2]
  have hhigh : ‖x - 1‖ ≤ 2 := by
    have hh := norm_sub_le x (1 : ℂ)
    rw [norm_one] at hh
    linarith only [hh, hx, hρ2]
  have hdistpos : 0 < ‖x - 1‖ := lt_of_lt_of_le (by norm_num) hlow
  have hxz : ‖x - z‖ ≤ 2 * ρ := by
    have hh := norm_sub_le x z
    linarith only [hh, hx, hz]
  have heq : gammaHalfKernel γ α₁ α₂ α₃ z x =
      ‖x - z‖ ^ (γ ^ 2 / 2) * ‖x‖ ^ (-γ * α₁) * ‖x - 1‖ ^ (-γ * α₂) := by
    unfold gammaHalfKernel
    rw [hn, Real.one_rpow, mul_one, neg_mul γ α₁, neg_mul γ α₂,
      Real.rpow_neg hxpos.le, Real.rpow_neg hdistpos.le]
    field_simp
  have hp := Real.rpow_le_rpow (norm_nonneg _) hxz (by positivity : 0 ≤ γ ^ 2 / 2)
  have htail : ‖x - 1‖ ^ (-γ * α₂) ≤ (2 : ℝ) ^ |γ * α₂| := by
    have hh := coulombWeight_rpow_le (L := 2) (y := ‖x - 1‖) (by norm_num)
      (by norm_num; exact hlow) hhigh (-γ * α₂)
    simpa only [neg_mul, abs_neg] using hh
  have hW : 0 ≤ ‖x‖ ^ (-γ * α₁) := Real.rpow_nonneg (norm_nonneg _) _
  have hscale : 0 ≤ (2 : ℝ) ^ |γ * α₂| * (2 * ρ) ^ (γ ^ 2 / 2) := by positivity
  rw [ENNReal.ofReal_rpow_of_pos hxpos, ← ENNReal.ofReal_mul hscale, heq]
  apply ENNReal.ofReal_le_ofReal
  have h := mul_le_mul_of_nonneg_right hp hW
  have hh := mul_le_mul h htail (Real.rpow_nonneg (norm_nonneg _) _) (by positivity)
  nlinarith only [hh]

/-- The local mass comparison is valid for atomless measures with the exact extended one-root
weight at the origin. No regularization or replacement measure is used. -/
theorem gammaHalf_local_mass_bound (γ α₁ α₂ α₃ : ℝ) (z : ℂ) (ρ : ℝ)
    (hρ : 0 < ρ) (hρ2 : ρ ≤ 1 / 2) (hz : ‖z‖ ≤ ρ) (μ : Measure ℂ) (h0 : μ {0} = 0) :
    (∫⁻ x in Metric.ball 0 ρ, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂μ) ≤
      ENNReal.ofReal ((2 : ℝ) ^ |γ * α₂| * (2 * ρ) ^ (γ ^ 2 / 2)) *
        weightedGmcBallMass γ μ α₁ 0 ρ := by
  have hx0 : ∀ᵐ x ∂μ, x ≠ 0 := by apply ae_iff.mpr; simpa using h0
  unfold weightedGmcBallMass
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_of_ae hx0, ae_restrict_mem measurableSet_ball] with x hnonzero hx
  have hn : ‖x‖ ≤ ρ := by
    have hh : ‖x‖ < ρ := by simpa only [Metric.mem_ball, dist_zero_right] using hx
    exact hh.le
  simpa only [sub_zero, ENNReal.rpow_eq_pow] using
    gammaHalf_local_kernel_bound γ α₁ α₂ α₃ z x ρ hρ hρ2 hz hn hnonzero

end DOZZ.Proofs

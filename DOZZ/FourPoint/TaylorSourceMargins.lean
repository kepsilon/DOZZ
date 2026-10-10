/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.TaylorMomentBudget
public import DOZZ.FourPoint.TaylorPairIntegrability

/-! Source-level parameter choice and convergent near-diagonal kernels in the strict domain. -/

@[expose] public section
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Choose all exponents before the spatial scale, on the literal corrected Taylor domain. -/
theorem twoRooted_region_parameters (γ α : ℝ)
    (hγ : 0 < γ) (hγsq : 2 < γ ^ 2) (hα : γ / 2 < α) (hα2 : α < 2 / γ) :
    ∃ q δ ε η : ℝ, 1 < q ∧ 0 < δ ∧ δ < 1 ∧ 0 < ε ∧ 0 < η ∧
      η < 2 - γ * (Q γ - α) ∧ η ≤ δ * (γ * (α - γ / 2)) ∧
        η ≤ (α - 2 / γ) ^ 2 / 2 ∧
          γ * (Q γ - α) - 2 + η ≤
            -2 - 2 * ε + (1 - δ) * (γ / 2 + Q γ - α) ^ 2 / (2 * q) := by
  obtain ⟨_, hκ, hκ2⟩ := twoRooted_time_exponent γ α hγ hγsq hα hα2
  obtain ⟨heq, hgain⟩ := twoRooted_intermediate_gain γ α hγ hα2
  have hW : 2 * (γ * (Q γ - α)) < (γ / 2 + Q γ - α) ^ 2 := by
    rw [← heq] at hgain
    linarith only [hgain]
  obtain ⟨_, hn⟩ := twoRooted_near_gain γ α hγ hα2
  exact taylor_region_margins (γ * (Q γ - α)) ((γ / 2 + Q γ - α) ^ 2)
    (γ * (α - γ / 2)) ((α - 2 / γ) ^ 2 / 2) (zero_lt_one.trans hκ) hκ2 hW
    (mul_pos hγ (sub_pos.mpr hα)) hn

/-- The two positive near-diagonal envelopes in source `ibo` and the last sector are finite.
The strict gamma^2 > 2 bound is used in the first diagonal exponent, not discarded. -/
theorem twoRooted_planar_kernels_finite (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hγsq : 2 < γ ^ 2) :
    ((∫⁻ u in Metric.ball (1 : ℂ) (1 / 4), ∫⁻ v in Metric.ball (1 : ℂ) (1 / 4),
      ENNReal.ofReal (‖u - v‖ ^ ((3 * γ / 2 - Q γ) ^ 2 / 2 - 2))) < ⊤) ∧
    ((∫⁻ u in Metric.ball (1 : ℂ) (1 / 4), ∫⁻ v in Metric.ball (1 : ℂ) (1 / 4),
      ENNReal.ofReal (‖1 - u‖ ^ (-(γ ^ 2 / 4))) *
        ENNReal.ofReal (‖u - v‖ ^ ((2 * γ - Q γ) ^ 2 / 2 - γ ^ 2))) < ⊤) := by
  obtain ⟨hν3, _, hfirst, hsecond⟩ := twoRooted_diagonal_exponents γ hγ hγ2 hγsq
  constructor
  · have hb : -2 < (3 * γ / 2 - Q γ) ^ 2 / 2 - 2 := by
      have hsq : 0 < (3 * γ / 2 - Q γ) ^ 2 := sq_pos_of_pos hν3
      linarith only [hsq]
    have h := planar_pair_power_finite 1 (1 / 4) 0
      ((3 * γ / 2 - Q γ) ^ 2 / 2 - 2) (by norm_num) (by norm_num) hb
    simpa only [Real.rpow_zero, ENNReal.ofReal_one, one_mul] using h
  · exact planar_pair_power_finite 1 (1 / 4) (-(γ ^ 2 / 4))
      ((2 * γ - Q γ) ^ 2 / 2 - γ ^ 2) (by norm_num)
      (by linarith only [hfirst]) (by linarith only [hsecond])

end DOZZ.Proofs

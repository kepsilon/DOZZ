/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.RetainedAnnuliNestedUniform
public import DOZZ.FourPoint.RetainedAnnuliNestedCharts

/-! Nested retained masses in arbitrary bounded charts. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- The nested retained-annulus bound is uniform on arbitrary bounded center sets. The outer
Gaussian exponent depends on the sum of the orders; bounded translation costs a fixed factor. -/
theorem nested_retained_inverse_uniform_bounded_centers
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (B R σ d A : ℝ) (hB : 0 ≤ B) (hR : 0 < R) (hR1 : R < 1)
    (hσ : 0 < σ) (hσ8 : σ ≤ 1 / 8) (hd : 0 < d) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b : ℝ), 0 ≤ a → a ≤ A → 0 ≤ b → b ≤ A → ∀ (z : ℂ), ‖z‖ ≤ B → ∀ (c : ℝ), 0 < c → c ≤ 1 →
      ∀ (u v : ℂ) (ρ : ℝ), 0 < ρ → ρ ≤ 1 / 8 →
        ‖u‖ + ρ ≤ R → ‖v‖ + σ ≤ R → ρ + σ + d ≤ ‖u - v‖ →
        (∫⁻ ω, (M ω (Metric.ball (z + c • u) (c * ρ))) ^ (-a) *
          (M ω (Metric.ball (z + c • v) (c * σ))) ^ (-b) ∂P) ≤
          ENNReal.ofReal (C * c ^ (γ * Q γ * (-(a + b)) - γ ^ 2 * (a + b) ^ 2 / 2) *
            ρ ^ (γ * Q γ * (-a) - γ ^ 2 * a ^ 2 / 2)) := by
  obtain ⟨C₀, hC₀, hunit⟩ := nested_retained_inverse_uniform_orders
    P X hX γ hγ hγ2 M hM R σ d A hR hR1 hσ hσ8 hd hA
  let L : ℝ := B + 1
  let k : ℝ := Real.exp (γ ^ 2 * (2 * gmcCircleChartRemainder L) / 2 *
    ((2 * A) ^ 2 + 2 * A))
  let t : ℝ := (1 + L) ^ 4
  have ht : 0 < t := by dsimp only [t, L]; positivity
  have hk : 0 < k := Real.exp_pos _
  let C : ℝ := k * t ^ (2 * A) * C₀
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro a b ha haA hb hbA z hz c hc hc1 u v ρ hρ hρ8 hu hv hsep
  have hcR : c * R < 1 := (mul_le_of_le_one_left hR.le hc1).trans_lt hR1
  have hsub (w : ℂ) (s : ℝ) (hw : ‖w‖ + s ≤ R) :
      Metric.ball (c • w) (c * s) ⊆ Metric.ball 0 1 := by
    intro x hx
    have hx' : ‖x - c • w‖ < c * s := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hx
    have hsum := norm_add_le (x - c • w) (c • w)
    rw [sub_add_cancel, norm_smul, Real.norm_eq_abs, abs_of_pos hc] at hsum
    have hh := mul_le_mul_of_nonneg_left hw hc.le
    change dist x 0 < 1
    rw [dist_zero_right]
    linarith only [hx', hsum, hh, hcR]
  have htr := gmc_joint_ball_inverse_translate P X hX γ hγ hγ2 M hM
    z 0 (c • u) (c • v) (c * ρ) (c * σ) 1 L a b (by dsimp only [L]; positivity)
    (by positivity) (by positivity) ((mul_le_of_le_one_left hρ.le hc1).trans hρ8)
    ((mul_le_of_le_one_left hσ.le hc1).trans hσ8)
    (by dsimp only [L]; linarith only [hz])
    (by simp only [norm_zero, zero_add]; dsimp only [L]; linarith only [hB])
    (hsub u ρ hu) (hsub v σ hv) ha hb
  have href := hunit a b ha haA hb hbA 0 c hc hc1 (by simpa only [norm_zero, zero_add] using hcR)
    u v ρ hρ hρ8 hu hv hsep
  rw [affine_ball_image 0 u c ρ hc, affine_ball_image 0 v c σ hc] at href
  simp only [zero_add] at href
  simp only [add_zero, add_comm (c • u) z, add_comm (c • v) z] at htr
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hcost := inverse_gaussian_bill_mono γ (2 * gmcCircleChartRemainder L)
    (a + b) (2 * A) (mul_nonneg (by norm_num) (gmcCircleChartRemainder_nonneg hL))
    (add_nonneg ha hb) (by linarith only [haA, hbA])
  have ht1 : 1 ≤ t := one_le_pow₀ (by dsimp only [L]; linarith only [hB])
  have hpow := ENNReal.rpow_le_rpow_of_exponent_le
    (show 1 ≤ ENNReal.ofReal t from by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal ht1)
    (show a + b ≤ 2 * A by linarith only [haA, hbA])
  simp only [add_assoc] at htr hcost
  have hh := htr.trans (mul_le_mul' (mul_le_mul' hcost hpow) href)
  change _ ≤ ENNReal.ofReal k * ENNReal.ofReal t ^ (2 * A) *
    ENNReal.ofReal (C₀ * c ^ (γ * Q γ * (-(a + b)) - γ ^ 2 * (a + b) ^ 2 / 2) *
      ρ ^ (γ * Q γ * (-a) - γ ^ 2 * a ^ 2 / 2)) at hh
  refine hh.trans_eq ?_
  rw [ENNReal.ofReal_rpow_of_pos ht, ← ENNReal.ofReal_mul hk.le,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  dsimp only [C]
  ring

end DOZZ.Proofs

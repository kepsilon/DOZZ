/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.RetainedAnnuliAffineMoments
public import DOZZ.GMC.BallAnnulus.Ball

/-! Uniform inverse orders on a bounded interval, with the exact radius exponent. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

/-- A varying inverse order is controlled by one fixed higher inverse moment. -/
theorem inverse_order_le_one_add (x : ℝ≥0∞) (a A : ℝ)
    (ha : 0 ≤ a) (haA : a ≤ A) : x ^ (-a) ≤ 1 + x ^ (-A) := by
  rcases le_total x 1 with hx | hx
  · exact (ENNReal.rpow_le_rpow_of_exponent_ge hx (neg_le_neg haA)).trans le_add_self
  · have hh := ENNReal.rpow_le_rpow_of_exponent_le hx (neg_nonpos.mpr ha)
    rw [ENNReal.rpow_zero] at hh
    exact hh.trans le_self_add

/-- The geometric and Gaussian scale exponent agrees with `γ Q p`. -/
theorem scale_exponent_eq (γ p : ℝ) (hγ : γ ≠ 0) :
    2 * p + γ ^ 2 * p / 2 - γ ^ 2 * p ^ 2 / 2 = γ * Q γ * p - γ ^ 2 * p ^ 2 / 2 := by
  unfold Q
  field_simp

/-- The inverse scale exponent decreases as the nonnegative inverse order increases. -/
theorem inverse_scale_exponent_antitone (γ a A : ℝ) (hγ : 0 < γ)
    (ha : 0 ≤ a) (haA : a ≤ A) :
    γ * Q γ * (-A) - γ ^ 2 * A ^ 2 / 2 ≤ γ * Q γ * (-a) - γ ^ 2 * a ^ 2 / 2 := by
  have hQ : 0 < Q γ := by
    unfold Q
    exact add_pos (div_pos (by norm_num) hγ) (div_pos hγ (by norm_num))
  have hlin := mul_le_mul_of_nonneg_left (neg_le_neg haA) (mul_pos hγ hQ).le
  have hsq : a ^ 2 ≤ A ^ 2 := by nlinarith only [ha, haA]
  have hquad := mul_le_mul_of_nonneg_left hsq (sq_nonneg γ)
  linarith only [hlin, hquad]

/-- The common Gaussian inverse-product factor is monotone in the total nonnegative order. -/
theorem inverse_gaussian_bill_mono (γ C q Q : ℝ) (hC : 0 ≤ C)
    (hq : 0 ≤ q) (hqQ : q ≤ Q) :
    ENNReal.ofReal (Real.exp (γ ^ 2 * C / 2 * (q ^ 2 + q))) ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 * C / 2 * (Q ^ 2 + Q))) := by
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  nlinarith only [hq, hqQ]

/-- The sharp small-ball inverse moment bound is uniform over all orders in `[0,A]` and all
centers with norm at most `B`. The radius exponent retains the actual order `a`. -/
theorem ball_inverse_moment_uniform_orders
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (B A : ℝ) (hB : 0 ≤ B) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 ≤ a → a ≤ A → ∀ z : ℂ, ‖z‖ ≤ B →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 8 →
        gmcMassMoment P M (Metric.ball z ρ) (-a) ≤
          ENNReal.ofReal (C * ρ ^ (γ * Q γ * (-a) - γ ^ 2 * a ^ 2 / 2)) := by
  have : IsProbabilityMeasure P := hX.1
  have hQ : 0 < Q γ := by
    unfold Q
    exact add_pos (div_pos (by norm_num) hγ) (div_pos hγ (by norm_num))
  have hbulk : 0 < 4 / γ ^ 2 := div_pos (by norm_num) (sq_pos_of_pos hγ)
  have hmoment := gmc_ball_moment_lt_top_any_center P X hX γ hγ hγ2 M hM 0 (1 / 8)
    (by norm_num) le_rfl (-A) ((neg_nonpos.mpr hA).trans_lt hbulk)
  let D : ℝ := 1 + (gmcMassMoment P M (Metric.ball 0 (1 / 8)) (-A)).toReal
  have hD : 0 < D := by dsimp only [D]; positivity
  have href (a : ℝ) (ha : 0 ≤ a) (haA : a ≤ A) :
      gmcMassMoment P M (Metric.ball 0 (1 / 8)) (-a) ≤ ENNReal.ofReal D := by
    calc
      _ ≤ ∫⁻ ω, (1 + M ω (Metric.ball 0 (1 / 8)) ^ (-A)) ∂P :=
        lintegral_mono fun ω => inverse_order_le_one_add _ a A ha haA
      _ = 1 + gmcMassMoment P M (Metric.ball 0 (1 / 8)) (-A) := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
        rfl
      _ = ENNReal.ofReal D := by
        rw [← ENNReal.ofReal_toReal hmoment.ne, ← ENNReal.ofReal_one,
          ← ENNReal.ofReal_add zero_le_one ENNReal.toReal_nonneg]
  let L : ℝ := B + 1
  let k : ℝ := γ ^ 2 * (2 * gmcCircleChartRemainder L) / 2
  let t : ℝ := (1 + L) ^ 4
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hk : 0 ≤ k := by
    dsimp only [k]
    exact div_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg (by norm_num)
      (gmcCircleChartRemainder_nonneg hL))) (by norm_num)
  have ht : 1 ≤ t := one_le_pow₀ (by dsimp only [L]; linarith only [hB])
  let T : ℝ := Real.exp (k * (A ^ 2 + A)) * t ^ A
  have hT : 0 < T := mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (zero_lt_one.trans_le ht) _)
  refine ⟨T * D, mul_pos hT hD, ?_⟩
  intro a ha haA z hz ρ hρ hρ8
  let ξ : ℝ := γ * Q γ * (-a) - γ ^ 2 * a ^ 2 / 2
  have hξ : ξ ≤ 0 := by
    dsimp only [ξ]
    exact sub_nonpos.mpr (le_trans (mul_nonpos_of_nonneg_of_nonpos (mul_pos hγ hQ).le
      (neg_nonpos.mpr ha)) (by positivity))
  have hscale := gmc_affine_openBall_moment_scale P X hX γ hγ hγ2 M hM
    (a := 0) (c := 8 * ρ) (R := 1 / 8) (by positivity) (by linarith only [hρ8])
    (by norm_num) (by norm_num) (by simp only [norm_zero, zero_add]; linarith only [hρ8]) (-a)
  rw [show (8 * ρ) * (1 / 8 : ℝ) = ρ by ring, scale_exponent_eq γ (-a) hγ.ne', neg_sq]
    at hscale
  have hscaleFactor : (8 * ρ) ^ ξ ≤ ρ ^ ξ := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) hρ.le]
    exact mul_le_of_le_one_left (Real.rpow_pos_of_pos hρ _).le
      (Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) hξ)
  have hzero : gmcMassMoment P M (Metric.ball 0 ρ) (-a) ≤ ENNReal.ofReal (D * ρ ^ ξ) := by
    rw [hscale]
    exact (mul_le_mul' (ENNReal.ofReal_le_ofReal hscaleFactor) (href a ha haA)).trans_eq
      (by rw [← ENNReal.ofReal_mul (Real.rpow_pos_of_pos hρ _).le, mul_comm])
  have htr := gmc_ball_moment_transfer P X hX γ hγ hγ2 M hM z 0 ρ L hρ hρ8 hL
    (by dsimp only [L]; linarith only [hz, hρ8])
    (by simp only [norm_zero, zero_add]; dsimp only [L]; linarith only [hB, hρ8])
    (-a) ((neg_nonpos.mpr ha).trans_lt hbulk)
  have habs : |(-a) ^ 2 - (-a)| = a ^ 2 + a := by
    rw [neg_sq, sub_neg_eq_add, abs_of_nonneg (add_nonneg (sq_nonneg a) ha)]
  rw [habs] at htr
  have hstep : ENNReal.ofReal (Real.exp (k * (a ^ 2 + a))) * ENNReal.ofReal t ^ a ≤
      ENNReal.ofReal T := by
    have he : a ^ 2 + a ≤ A ^ 2 + A := by nlinarith only [ha, haA]
    have hE := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left he hk))
    have hP := ENNReal.rpow_le_rpow_of_exponent_le
      (show 1 ≤ ENNReal.ofReal t from by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal ht) haA
    refine (mul_le_mul' hE hP).trans_eq ?_
    rw [ENNReal.ofReal_rpow_of_pos (zero_lt_one.trans_le ht),
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  have htr' : gmcMassMoment P M (Metric.ball z ρ) (-a) ≤
      ENNReal.ofReal (Real.exp (k * (a ^ 2 + a))) * ENNReal.ofReal t ^ a *
        gmcMassMoment P M (Metric.ball 0 ρ) (-a) := by
    simpa only [k, t, gmcCircleChartRemainder, abs_neg, abs_of_nonneg ha] using htr
  refine (htr'.trans (mul_le_mul' hstep hzero)).trans_eq ?_
  rw [← ENNReal.ofReal_mul hT.le]
  congr 1
  ring

end DOZZ.Proofs

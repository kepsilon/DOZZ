/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.RetainedAnnuliAffineMoments
public import DOZZ.GMC.BallAnnulus.Ball

/-! Retained nested masses: exact shared outer scaling, then separated normalized disks. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- Joint inverse moments of retained disks on two scales in the unit chart. A fixed gap is
required only after dividing by the outer scale. The outer exponent uses `a+b`; the inner ratio
uses `a`. Thus the common outer Gaussian is retained exactly, including the cross term.

The constant precedes the center, outer scale, and inner radius. This is the joint annular
comparison, with retained subdisks supplying the negative moments. -/
theorem nested_retained_annuli_inverse_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (R σ d a b : ℝ) (hR : 0 < R) (hR1 : R < 1) (hσ : 0 < σ) (hσ8 : σ ≤ 1 / 8)
    (hd : 0 < d) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ) (c : ℝ), 0 < c → c ≤ 1 → ‖z‖ + c * R < 1 →
      ∀ (u v : ℂ) (ρ : ℝ), 0 < ρ → ρ ≤ 1 / 8 →
        ‖u‖ + ρ ≤ R → ‖v‖ + σ ≤ R → ρ + σ + d ≤ ‖u - v‖ →
        (∫⁻ ω, (M ω ((fun y => z + c • y) '' Metric.ball u ρ)) ^ (-a) *
          (M ω ((fun y => z + c • y) '' Metric.ball v σ)) ^ (-b) ∂P) ≤
          ENNReal.ofReal (C * c ^ (γ * Q γ * (-(a + b)) - γ ^ 2 * (a + b) ^ 2 / 2) *
            ρ ^ (γ * Q γ * (-a) - γ ^ 2 * a ^ 2 / 2)) := by
  let K : Set ℂ := Metric.closedBall 0 R
  have hK : IsCompact K := isCompact_closedBall _ _
  have hbulk : 0 < 4 / γ ^ 2 := div_pos (by norm_num) (sq_pos_of_pos hγ)
  obtain ⟨Ca, hCa, hMa⟩ := equatorGFF_GMC_ball_moment_bound P X hX γ hγ hγ2 M hM
    (-a) ((neg_nonpos.mpr ha).trans_lt hbulk) K hK
  obtain ⟨Cb, hCb, hMb⟩ := equatorGFF_GMC_ball_moment_bound P X hX γ hγ hγ2 M hM
    (-b) ((neg_nonpos.mpr hb).trans_lt hbulk) K hK
  let k : ℝ := Real.exp (γ ^ 2 * max 0 (Real.log (1 / d) + gmcCircleChartRemainder R) / 2 *
    ((a + b) ^ 2 + a + b))
  let C : ℝ := k * Ca * Cb * σ ^ (γ * Q γ * (-b) - γ ^ 2 * b ^ 2 / 2)
  have hk : 0 < k := Real.exp_pos _
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro z c hc hc1 hz u v ρ hρ hρ8 hu hv hsep
  let U : Fin 2 → Set ℂ := ![Metric.ball u ρ, Metric.ball v σ]
  have hU : ∀ j, IsOpen (U j) := by intro j; fin_cases j <;> exact Metric.isOpen_ball
  have hUR : ∀ j, U j ⊆ Metric.closedBall 0 R := by
    intro j
    fin_cases j
    · exact (ball_subset_closedBall_norm_add u ρ).trans
        (Metric.closedBall_subset_closedBall hu)
    · exact (ball_subset_closedBall_norm_add v σ).trans
        (Metric.closedBall_subset_closedBall hv)
  have hscale := affine_open_set_joint_moment P X hX γ hγ hγ2 M hM hc hc1
    hR hR1 hz U hU hUR (-a) (-b)
  have hsum : -a + -b = -(a + b) := by ring
  simp only [U, Matrix.cons_val_zero, Matrix.cons_val_one, hsum, neg_sq] at hscale
  rw [hscale]
  have huK : u ∈ K := by
    change dist u 0 ≤ R
    rw [dist_zero_right]
    linarith only [hu, hρ]
  have hvK : v ∈ K := by
    change dist v 0 ≤ R
    rw [dist_zero_right]
    linarith only [hv, hσ]
  have hma := (hMa u huK ρ hρ (hρ8.trans (by norm_num))).2
  have hmb := (hMb v hvK σ hσ (hσ8.trans (by norm_num))).2
  have hjoint := joint_retained_annuli_inverse_bound P X hX γ hγ hγ2 M hM
    u v ρ σ R d a b hρ hσ hρ8 hσ8 hR.le hd hu hv hsep ha hb
  have hj := hjoint.trans (mul_le_mul' (mul_le_mul' le_rfl hma) hmb)
  refine (mul_le_mul' le_rfl hj).trans_eq ?_
  simp only [Real.rpow_eq_pow, neg_sq, ← mul_assoc]
  rw [← ENNReal.ofReal_mul (Real.rpow_pos_of_pos hc _).le,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  dsimp only [C, k]
  ring

end DOZZ.Proofs

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.RetainedAnnuliNested
public import DOZZ.FourPoint.RetainedAnnuliUniformOrders

/-! A single nested-annulus constant for a bounded interval of allocated inverse orders. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- The unit-chart joint nested bound with its constant before the two allocated orders.
Only the constant uses their common upper bound; both scale exponents retain the actual orders. -/
theorem nested_retained_inverse_uniform_orders
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (R σ d A : ℝ) (hR : 0 < R) (hR1 : R < 1) (hσ : 0 < σ) (hσ8 : σ ≤ 1 / 8)
    (hd : 0 < d) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a b : ℝ), 0 ≤ a → a ≤ A → 0 ≤ b → b ≤ A →
      ∀ (z : ℂ) (c : ℝ), 0 < c → c ≤ 1 → ‖z‖ + c * R < 1 →
        ∀ (u v : ℂ) (ρ : ℝ), 0 < ρ → ρ ≤ 1 / 8 →
          ‖u‖ + ρ ≤ R → ‖v‖ + σ ≤ R → ρ + σ + d ≤ ‖u - v‖ →
          (∫⁻ ω, (M ω ((fun y => z + c • y) '' Metric.ball u ρ)) ^ (-a) *
            (M ω ((fun y => z + c • y) '' Metric.ball v σ)) ^ (-b) ∂P) ≤
            ENNReal.ofReal (C * c ^ (γ * Q γ * (-(a + b)) - γ ^ 2 * (a + b) ^ 2 / 2) *
              ρ ^ (γ * Q γ * (-a) - γ ^ 2 * a ^ 2 / 2)) := by
  obtain ⟨Cb, hCb, hball⟩ := ball_inverse_moment_uniform_orders P X hX γ hγ hγ2 M hM
    R A hR.le hA
  let k : ℝ := Real.exp (γ ^ 2 * max 0 (Real.log (1 / d) + gmcCircleChartRemainder R) / 2 *
    ((2 * A) ^ 2 + 2 * A))
  let D : ℝ := Cb * σ ^ (γ * Q γ * (-A) - γ ^ 2 * A ^ 2 / 2)
  have hk : 0 < k := Real.exp_pos _
  have hD : 0 < D := by dsimp only [D]; positivity
  let C : ℝ := k * Cb * D
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro a b ha haA hb hbA z c hc hc1 hz u v ρ hρ hρ8 hu hv hsep
  let U : Fin 2 → Set ℂ := ![Metric.ball u ρ, Metric.ball v σ]
  have hU : ∀ j, IsOpen (U j) := by intro j; fin_cases j <;> exact Metric.isOpen_ball
  have hUR : ∀ j, U j ⊆ Metric.closedBall 0 R := by
    intro j
    fin_cases j
    · exact (ball_subset_closedBall_norm_add u ρ).trans (Metric.closedBall_subset_closedBall hu)
    · exact (ball_subset_closedBall_norm_add v σ).trans (Metric.closedBall_subset_closedBall hv)
  have hscale := affine_open_set_joint_moment P X hX γ hγ hγ2 M hM hc hc1
    hR hR1 hz U hU hUR (-a) (-b)
  simp only [U, Matrix.cons_val_zero, Matrix.cons_val_one,
    show -a + -b = -(a + b) by ring, neg_sq] at hscale
  rw [hscale]
  have hun : ‖u‖ ≤ R := by linarith only [hu, hρ]
  have hvn : ‖v‖ ≤ R := by linarith only [hv, hσ]
  have hma := hball a ha haA u hun ρ hρ hρ8
  have hmb := hball b hb hbA v hvn σ hσ hσ8
  have hmb' : gmcMassMoment P M (Metric.ball v σ) (-b) ≤ ENNReal.ofReal D := by
    refine hmb.trans (ENNReal.ofReal_le_ofReal ?_)
    apply mul_le_mul_of_nonneg_left _ hCb.le
    exact Real.rpow_le_rpow_of_exponent_ge hσ (hσ8.trans (by norm_num))
      (inverse_scale_exponent_antitone γ b A hγ hb hbA)
  have hjoint := joint_retained_annuli_inverse_bound P X hX γ hγ hγ2 M hM
    u v ρ σ R d a b hρ hσ hρ8 hσ8 hR.le hd hu hv hsep ha hb
  have hcost := inverse_gaussian_bill_mono γ
    (max 0 (Real.log (1 / d) + gmcCircleChartRemainder R)) (a + b) (2 * A)
    (le_max_left _ _) (add_nonneg ha hb) (by linarith only [haA, hbA])
  simp only [add_assoc] at hjoint hcost
  have hj := hjoint.trans (mul_le_mul' (mul_le_mul' hcost hma) hmb')
  refine (mul_le_mul' le_rfl hj).trans_eq ?_
  change ENNReal.ofReal (c ^ (γ * Q γ * (-(a + b)) - γ ^ 2 * (a + b) ^ 2 / 2)) *
    (ENNReal.ofReal k * ENNReal.ofReal (Cb * ρ ^ (γ * Q γ * (-a) - γ ^ 2 * a ^ 2 / 2)) *
      ENNReal.ofReal D) = _
  simp only [← mul_assoc]
  rw [← ENNReal.ofReal_mul (Real.rpow_pos_of_pos hc _).le,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  dsimp only [C]
  ring

end DOZZ.Proofs

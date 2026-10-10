/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.ImprovedChargeMoment
public import DOZZ.Correlations.Tails.OffCenterMultiplier

/-! First-order multiplier errors are dominated by a smaller insertion charge. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal

namespace DOZZ.Proofs

/-- The estimate remains valid at the center, where the singular weight can be infinite.
The vanishing first-order error is handled before multiplying by that weight. -/
theorem first_order_singular_weight_le (γ α C : ℝ) (hγ : γ ≠ 0)
    (hC : 0 ≤ C) (e : ℂ → ℝ) (x : ℂ) (he : |e x| ≤ C * ‖x‖) :
    ENNReal.ofReal |e x| * (ENNReal.ofReal ‖x‖)^(-γ*α) ≤
      ENNReal.ofReal C * (ENNReal.ofReal ‖x‖)^(-γ*(α-1/γ)) := by
  by_cases hx : x = 0
  · have he0 : |e x| = 0 := le_antisymm
      (by simpa only [hx, norm_zero, mul_zero] using he) (abs_nonneg _)
    rw [he0, ENNReal.ofReal_zero, zero_mul]
    exact zero_le
  · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hne : ENNReal.ofReal ‖x‖ ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hn)
    calc
      _ ≤ ENNReal.ofReal (C * ‖x‖) * (ENNReal.ofReal ‖x‖)^(-γ*α) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal he) le_rfl
      _ = ENNReal.ofReal C * (ENNReal.ofReal ‖x‖)^(1+(-γ*α)) := by
        rw [ENNReal.ofReal_mul hC, ENNReal.rpow_add _ _ hne ENNReal.ofReal_ne_top,
          ENNReal.rpow_one, mul_assoc]
      _ = _ := by
        have hexp : 1+(-γ*α) = -γ*(α-1/γ) := by field_simp; ring
        rw [hexp]

/-- Integrating the pointwise estimate gives the exact improved-charge dominating mass. -/
theorem first_order_singular_mass_le (γ α C : ℝ) (hγ : γ ≠ 0)
    (hC : 0 ≤ C) (e : ℂ → ℝ) (ρ : ℝ)
    (he : ∀ x ∈ Metric.ball 0 ρ, |e x| ≤ C * ‖x‖) (μ : Measure ℂ) :
    (∫⁻ x in Metric.ball 0 ρ,
      ENNReal.ofReal |e x| * (ENNReal.ofReal ‖x‖)^(-γ*α) ∂μ) ≤
      ENNReal.ofReal C * weightedGmcBallMass γ μ (α-1/γ) 0 ρ := by
  calc
    _ ≤ ∫⁻ x in Metric.ball 0 ρ,
        ENNReal.ofReal C * (ENNReal.ofReal ‖x‖)^(-γ*(α-1/γ)) ∂μ := by
      apply setLIntegral_mono' Metric.isOpen_ball.measurableSet
      intro x hx
      exact first_order_singular_weight_le γ α C hγ hC e x (he x hx)
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      simp only [weightedGmcBallMass, sub_zero, ENNReal.rpow_eq_pow]


end DOZZ.Proofs

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.SeibergWeight
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Tactic

/-! # Dominated convergence at the negative insertion

An insertion of negative charge contributes a uniformly bounded factor when its
location stays in the unit disk. The dominating mass retains the original positive
charge at zero; it is almost surely finite throughout the strict Seiberg domain.
-/

@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- The negative half-charge factor is bounded independently of its moving location. -/
theorem crossing_negative_factor_le (γ : ℝ) (z x : ℂ)
    (hz : ‖z‖ ≤ 1) (hxz : x ≠ z) :
    ENNReal.rpow (ENNReal.ofReal (normPlus x / ‖x - z‖)) (γ * (-γ / 2)) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (γ * (-γ / 2))) := by
  have hn : 0 < normPlus x := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hd : 0 < ‖x - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxz)
  have hb : 1 / 2 ≤ normPlus x / ‖x - z‖ := by
    rw [le_div_iff₀ hd]
    have hh := norm_sub_le x z
    have h1 : 1 ≤ normPlus x := le_max_left _ _
    have h2 : ‖x‖ ≤ normPlus x := le_max_right _ _
    linarith only [hh, h1, h2, hz]
  rw [coulombWeight_rpow_ofReal (div_pos hn hd)]
  apply ENNReal.ofReal_le_ofReal
  exact Real.rpow_le_rpow_of_nonpos (by norm_num) hb (by nlinarith only [sq_nonneg γ])

/-- Removing the bounded negative-charge factor yields a fixed three-point majorant. -/
theorem crossing_coulombWeight_le (γ a b c : ℝ) (z x : ℂ)
    (hz : ‖z‖ ≤ 1) (hxz : x ≠ z) :
    coulombWeight γ ![-γ / 2, a, b] ![z, 0, 1] c x ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (γ * (-γ / 2))) *
        coulombWeight γ ![a, b] ![0, 1] c x := by
  simp only [coulombWeight, Fin.prod_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.prod_univ_zero, mul_one]
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul' (crossing_negative_factor_le γ z x hz hxz) le_rfl

/-- Integrating the negative-factor bound gives a finite fixed mass majorant. -/
theorem crossing_coulombMass_le (ν : Measure ℂ) (γ a b c : ℝ) (z : ℂ)
    (hz : ‖z‖ ≤ 1) (ha : ν {z} = 0) :
    coulombMass γ ν ![-γ / 2, a, b] ![z, 0, 1] c ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (γ * (-γ / 2))) *
        coulombMass γ ν ![a, b] ![0, 1] c := by
  simp only [coulombMass_eq_lintegral_coulombWeight]
  rw [← lintegral_const_mul _ (measurable_coulombWeight _ _ _ _)]
  apply lintegral_mono_ae
  have h : ∀ᵐ x ∂ν, x ≠ z := by rw [ae_iff]; simpa using ha
  exact h.mono fun x hx => crossing_coulombWeight_le γ a b c z x hz hx

/-- For an atomless measure with a finite unshifted mass, the half-charge mass
converges at the collision along every bounded sequence. -/
theorem crossing_coulombMass_tendsto_seq (ν : Measure ℂ) (γ a b c : ℝ)
    (z : ℕ → ℂ) (hz : Tendsto z atTop (𝓝 0)) (hb : ∀ n, ‖z n‖ ≤ 1)
    (h0 : ν {0} = 0) (h1 : ν {1} = 0) (hn : ∀ n, ν {z n} = 0)
    (hfin : coulombMass γ ν ![a, b] ![0, 1] c ≠ ⊤) :
    Tendsto (fun n => coulombMass γ ν ![-γ / 2, a, b] ![z n, 0, 1] c)
      atTop (𝓝 (coulombMass γ ν ![-γ / 2, a, b] ![0, 0, 1] c)) := by
  simp only [coulombMass_eq_lintegral_coulombWeight]
  let C := ENNReal.ofReal ((1 / 2 : ℝ) ^ (γ * (-γ / 2)))
  refine tendsto_lintegral_of_dominated_convergence
    (fun x => C * coulombWeight γ ![a, b] ![0, 1] c x)
    (fun n => measurable_coulombWeight _ _ _ _) ?_ ?_ ?_
  · intro n
    have ha : ∀ᵐ x ∂ν, x ≠ z n := by rw [ae_iff]; simpa using hn n
    exact ha.mono fun x hx => crossing_coulombWeight_le γ a b c (z n) x (hb n) hx
  · rw [lintegral_const_mul C (measurable_coulombWeight _ _ _ _)]
    exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin.lt_top).ne
  · have ha : ∀ᵐ x ∂ν, x ≠ (0 : ℂ) := by rw [ae_iff]; simpa using h0
    have ha1 : ∀ᵐ x ∂ν, x ≠ (1 : ℂ) := by rw [ae_iff]; simpa using h1
    filter_upwards [ha, ha1] with x hx hx1
    have hf : ContinuousAt (fun w : ℂ =>
        ENNReal.rpow (ENNReal.ofReal (normPlus x / ‖x - w‖)) (γ * (-γ / 2))) 0 := by
      change ContinuousAt (fun w : ℂ =>
        (ENNReal.ofReal (normPlus x / ‖x - w‖)) ^ (γ * (-γ / 2))) 0
      apply ENNReal.continuous_rpow_const.continuousAt.comp
      apply ENNReal.continuous_ofReal.continuousAt.comp
      apply ContinuousAt.div continuousAt_const
      · fun_prop
      · simpa only [sub_zero] using norm_ne_zero_iff.mpr hx
    have ht := hf.tendsto.comp hz
    simp only [coulombWeight, Fin.prod_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.prod_univ_zero, mul_one]
    have hp : 0 < normPlus x := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hx0p : 0 < ‖x - 0‖ := by simpa only [sub_zero] using norm_pos_iff.mpr hx
    have hx1p : 0 < ‖x - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx1)
    have hr : ENNReal.rpow (ENNReal.ofReal (normPlus x / ‖x - 0‖)) (γ * a) *
        ENNReal.rpow (ENNReal.ofReal (normPlus x / ‖x - 1‖)) (γ * b) *
        ENNReal.rpow (ENNReal.ofReal (normPlus x)) (γ * c) ≠ ⊤ := by
      rw [coulombWeight_rpow_ofReal (div_pos hp hx0p),
        coulombWeight_rpow_ofReal (div_pos hp hx1p), coulombWeight_rpow_ofReal hp]
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
    simp only [mul_assoc] at hr ⊢
    exact ENNReal.Tendsto.mul_const ht (Or.inr hr)

end DOZZ.Proofs

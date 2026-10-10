/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Dual.OuterMassLimit
public import DOZZ.FourPoint.TaylorFixedDisk
import Mathlib.Tactic

/-! # A fixed disk retained by the dual outer mass -/

public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The same positive disk weight works for every moving root and every retained radius at most one. -/
theorem dual_outerMass_fixed_disk_lower (γ α₁ α₂ α₃ ξ : ℝ) (μ : Measure ℂ)
    (z : ℂ) (hz : ‖z‖ ≤ 1) (hr : ‖z‖ ^ (1 - ξ) ≤ 1) :
    ENNReal.ofReal ((2 : ℝ) ^ (-∑ i : Fin 3, |γ * (![-2 / γ, α₁, α₂] : Fin 3 → ℝ) i|) *
      (4 : ℝ) ^ (-|γ * α₃|)) * μ (Metric.ball (3 : ℂ) (1 / 8)) ≤
        dualOuterMass γ α₁ α₂ α₃ μ z ξ := by
  let D : Set ℂ := {x | ‖z‖ ^ (1 - ξ) ≤ ‖x‖}
  have hsub : Metric.ball (3 : ℂ) (1 / 8) ⊆ D := by
    intro x hx
    have hdist : ‖x - 3‖ < 1 / 8 := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hx
    have hh := norm_sub_norm_le (3 : ℂ) x
    have hn3 : ‖(3 : ℂ)‖ = 3 := by norm_num
    rw [hn3, norm_sub_rev] at hh
    exact le_trans hr (by linarith only [hh, hdist])
  have hy : ∀ i : Fin 3, ‖(![z, 0, 1] : Fin 3 → ℂ) i‖ ≤ 1 := by
    intro i
    fin_cases i
    · exact hz
    · simp
    · simp
  have h := coulombMass_fixed_disk_lower γ (μ.restrict D)
    (![-2 / γ, α₁, α₂] : Fin 3 → ℝ) ![z, 0, 1] α₃ hy
  rw [Measure.restrict_apply measurableSet_ball, inter_eq_left.mpr hsub] at h
  exact h

/-- Uniform inverse moments of the literal retained mass, at every nonnegative inverse order. -/
theorem dual_outerMass_inverse_moment_uniform
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ q : ℝ) (hq : 0 ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ) (ξ : ℝ), ‖z‖ ≤ 1 → ‖z‖ ^ (1 - ξ) ≤ 1 →
      (∫⁻ ω, dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^ (-q) ∂P) ≤
        ENNReal.ofReal C := by
  let w : ℝ := (2 : ℝ) ^ (-∑ i : Fin 3, |γ * (![-2 / γ, α₁, α₂] : Fin 3 → ℝ) i|) *
    (4 : ℝ) ^ (-|γ * α₃|)
  have hw : 0 < w := by dsimp only [w]; positivity
  have hp : -q < 4 / γ ^ 2 := lt_of_le_of_lt (neg_nonpos.mpr hq) (by positivity)
  obtain ⟨Cb, hCb, hball⟩ := equatorGFF_GMC_ball_moment_bound P X hX γ hγ hγ₂ M hM
    (-q) hp {(3 : ℂ)} isCompact_singleton
  let e : ℝ := γ * Q γ * (-q) - γ ^ 2 * (-q) ^ 2 / 2
  let C : ℝ := w ^ (-q) * (Cb * (1 / 8 : ℝ) ^ e)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro z ξ hz hr
  have hb (ω : Ω) : dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^ (-q) ≤
      ENNReal.ofReal (w ^ (-q)) * M ω (Metric.ball (3 : ℂ) (1 / 8)) ^ (-q) := by
    have hlow := dual_outerMass_fixed_disk_lower γ α₁ α₂ α₃ ξ (M ω) z hz hr
    have hanti : dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^ (-q) ≤
        (ENNReal.ofReal w * M ω (Metric.ball (3 : ℂ) (1 / 8))) ^ (-q) := by
      rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
      exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hlow hq)
    have hfinite : M ω (Metric.ball (3 : ℂ) (1 / 8)) ≠ ⊤ := by
      let _ := hM.1 ω
      exact measure_ne_top _ _
    rwa [ENNReal.mul_rpow_of_ne_top ENNReal.ofReal_ne_top hfinite,
      ENNReal.ofReal_rpow_of_pos hw] at hanti
  have hbound := (hball 3 (Set.mem_singleton _) (1 / 8) (by norm_num) (by norm_num)).2
  calc
    (∫⁻ ω, dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^ (-q) ∂P) ≤
        ∫⁻ ω, ENNReal.ofReal (w ^ (-q)) * M ω (Metric.ball (3 : ℂ) (1 / 8)) ^ (-q) ∂P :=
      lintegral_mono hb
    _ = ENNReal.ofReal (w ^ (-q)) * gmcMassMoment P M (Metric.ball (3 : ℂ) (1 / 8)) (-q) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (w ^ (-q)) * ENNReal.ofReal (Cb * (1 / 8 : ℝ) ^ e) :=
      mul_le_mul' le_rfl hbound
    _ = ENNReal.ofReal C := (ENNReal.ofReal_mul (Real.rpow_pos_of_pos hw _).le).symm

end DOZZ.Proofs

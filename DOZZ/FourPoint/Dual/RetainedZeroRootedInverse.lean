/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Dual.RetainedZeroRooted
import Mathlib.Tactic

/-! # Uniform inverse moments of the rooted dual exterior mass

A fixed insertion-free disk controls the source's rooted inverse moment for
all rooting points, including exterior points and the totalized diagonal.
-/

public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- Uniform inverse moments of the literal retained mass, at every nonnegative inverse order. -/
theorem dual_rooted_retainedZero_inverse_moment_uniform
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ q : ℝ) (hq : 0 ≤ q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℂ) (r : ℝ), r ≤ 1 →
      (∫⁻ ω, dualRetainedZeroMass γ α₁ α₂ α₃ r (gmcRootedMeasure γ u (M ω)) ^ (-q) ∂P) ≤
        ENNReal.ofReal C := by
  let w : ℝ := Real.exp (-γ ^ 2 * Real.log 2) * ((2 : ℝ) ^ (-∑ i : Fin 3, |γ * (![-2 / γ, α₁, α₂] : Fin 3 → ℝ) i|) *
    (4 : ℝ) ^ (-|γ * α₃|))
  have hw : 0 < w := by dsimp only [w]; positivity
  have hp : -q < 4 / γ ^ 2 := lt_of_le_of_lt (neg_nonpos.mpr hq) (by positivity)
  obtain ⟨Cb, hCb, hball⟩ := equatorGFF_GMC_ball_moment_bound P X hX γ hγ hγ₂ M hM
    (-q) hp {(3 : ℂ)} isCompact_singleton
  let e : ℝ := γ * Q γ * (-q) - γ ^ 2 * (-q) ^ 2 / 2
  let C : ℝ := w ^ (-q) * (Cb * (1 / 8 : ℝ) ^ e)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro u r hr
  have hb (ω : Ω) : dualRetainedZeroMass γ α₁ α₂ α₃ r (gmcRootedMeasure γ u (M ω)) ^ (-q) ≤
      ENNReal.ofReal (w ^ (-q)) * M ω (Metric.ball (3 : ℂ) (1 / 8)) ^ (-q) := by
    have hlow := dual_rooted_retainedZero_fixed_disk_lower γ α₁ α₂ α₃ r (M ω) u hr
    have hanti : dualRetainedZeroMass γ α₁ α₂ α₃ r (gmcRootedMeasure γ u (M ω)) ^ (-q) ≤
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
    (∫⁻ ω, dualRetainedZeroMass γ α₁ α₂ α₃ r (gmcRootedMeasure γ u (M ω)) ^ (-q) ∂P) ≤
        ∫⁻ ω, ENNReal.ofReal (w ^ (-q)) * M ω (Metric.ball (3 : ℂ) (1 / 8)) ^ (-q) ∂P :=
      lintegral_mono hb
    _ = ENNReal.ofReal (w ^ (-q)) * gmcMassMoment P M (Metric.ball (3 : ℂ) (1 / 8)) (-q) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (w ^ (-q)) * ENNReal.ofReal (Cb * (1 / 8 : ℝ) ^ e) :=
      mul_le_mul' le_rfl hbound
    _ = ENNReal.ofReal C := (ENNReal.ofReal_mul (Real.rpow_pos_of_pos hw _).le).symm


end DOZZ.Proofs

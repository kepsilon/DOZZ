/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.AnnularLower
public import DOZZ.FourPoint.Reflected.ChargeShift
import Mathlib.Tactic
/-! # Freezing controls the actual first-order shifted outer mass -/
public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- Applying the local freezing estimate `reflected_freezing_local_input` to the retained annulus
gives the required extra power for the actual gamma-tilted outer inverse moment. -/
theorem reflected_shifted_outer_freezing_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hα₁ : α₁ < Q γ) (hreflect : Q γ - α₁ < γ / 2)
    (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ (z : ℂ) (ξ : ℝ),
      0 < ‖z‖ ^ (1 - ξ) → ‖z‖ ^ (1 - ξ) < ε₀ → ‖z‖ ≤ ‖z‖ ^ (1 - ξ) / 2 →
      (∫⁻ ω, gammaHalfOuterMass γ (α₁ + γ) α₂ α₃ (M ω) z ξ ^
        (-((α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ + 1)) ∂P) ≤
      ENNReal.ofReal (C * (‖z‖ ^ (1 - ξ)) ^ ((α₁ + γ / 2 - Q γ) ^ 2 / 2)) := by
  let q := (α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ + 1
  have hq : 0 < q := (reflected_freezing_margins γ α₁ α₂ α₃ hγ hα₁ hreflect hs).2.1
  obtain ⟨C₀, ε₀, hC₀, hε₀, hb⟩ := reflected_freezing_local_input P X M γ α₁ α₂ α₃
    hγ hγ₂ hα₁ hreflect hs hX hM
  let c : ℝ := (1 / 2 : ℝ) ^ (γ ^ 2 / 2) * (2 : ℝ) ^ (-|γ * α₂|)
  have hc : 0 < c := by dsimp only [c]; positivity
  let C := c ^ (-q) * C₀
  refine ⟨C, ε₀, mul_pos (Real.rpow_pos_of_pos hc _) hC₀, hε₀, ?_⟩
  intro z ξ he he₀ hz
  have hlower (ω : Ω) := reflected_outerMass_freezing_lower γ (α₁ + γ) α₂ α₃ ξ (M ω) z he hz
  have heα : α₁ + γ - γ / 2 = α₁ + γ / 2 := by ring
  have hinv (ω : Ω) : gammaHalfOuterMass γ (α₁ + γ) α₂ α₃ (M ω) z ξ ^ (-q) ≤
      ENNReal.ofReal (c ^ (-q)) *
        freezingAnnulusMassLocal γ (α₁ + γ / 2) (M ω) 0 (‖z‖ ^ (1 - ξ)) (1 / 2) ^ (-q) := by
    have hl := hlower ω
    rw [heα] at hl
    have hh : gammaHalfOuterMass γ (α₁ + γ) α₂ α₃ (M ω) z ξ ^ (-q) ≤
        (ENNReal.ofReal c *
          freezingAnnulusMassLocal γ (α₁ + γ / 2) (M ω) 0 (‖z‖ ^ (1 - ξ)) (1 / 2)) ^ (-q) := by
      rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
      exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hl hq.le)
    rw [ENNReal.mul_rpow_eq_ite] at hh
    have hn : ENNReal.ofReal c ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hc
    simp only [hn, ENNReal.ofReal_ne_top, false_and, false_or, ite_false,
      ENNReal.ofReal_rpow_of_pos hc] at hh
    exact hh
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal (c ^ (-q)) *
        freezingAnnulusMassLocal γ (α₁ + γ / 2) (M ω) 0 (‖z‖ ^ (1 - ξ)) (1 / 2) ^ (-q) ∂P :=
      lintegral_mono hinv
    _ = ENNReal.ofReal (c ^ (-q)) * (∫⁻ ω,
        freezingAnnulusMassLocal γ (α₁ + γ / 2) (M ω) 0 (‖z‖ ^ (1 - ξ)) (1 / 2) ^ (-q) ∂P) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (c ^ (-q)) *
        ENNReal.ofReal (C₀ * (‖z‖ ^ (1 - ξ)) ^ ((α₁ + γ / 2 - Q γ) ^ 2 / 2)) :=
      mul_le_mul' le_rfl (hb _ he he₀)
    _ = _ := by
      rw [← ENNReal.ofReal_mul (Real.rpow_pos_of_pos hc _).le]
      congr 1
      dsimp only [C]
      ring

end DOZZ.Proofs

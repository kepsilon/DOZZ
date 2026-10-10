/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.FourPointT
public import DOZZ.Statements.Brownian.ReflectionR
public import DOZZ.FourPoint.Dual.Window
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic

/-! # Exact dual fusion normalizations

The literal ENNReal moment and totalized Gamma definitions are retained.
-/

public section

open MeasureTheory

namespace DOZZ.Proofs

/-- The four-point zero-mode order for the negative dual degenerate charge. -/
theorem fourPointSExp_dual (γ α₁ α₂ α₃ : ℝ) :
    fourPointSExp γ (-2 / γ) α₁ α₂ α₃ =
      (α₁ + α₂ + α₃ - 2 / γ - 2 * Q γ) / γ := by
  unfold fourPointSExp
  congr 1
  ring

/-- The independent-maximum coefficient is exactly the inner-limit coefficient. -/
theorem dual_inner_coefficient_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (B : Ω → BrownianPath × BrownianPath)
    (Z : Ω → Measure ℝ) (γ μ α₁ α₂ α₃ : ℝ) (hγ : 0 < γ) (hμ : 0 < μ)
    (hs : 2 * Q γ + 2 / γ < α₁ + α₂ + α₃) :
    let p := (α₁ + α₂ + α₃ - 2 / γ - 2 * Q γ) / γ
    let a := reflectionExponent γ α₁
    (a * Real.Gamma (-a) * Real.Gamma (p + a) / Real.Gamma p) *
      reflectionBarR P γ α₁ B Z *
      (∫⁻ ω, rho γ (M ω) (2 * Q γ - α₁ - 2 / γ) α₂ α₃ ^ (-(p + a)) ∂P).toReal =
    1 / 2 * μ ^ p * γ * (Real.Gamma p)⁻¹ * reflectionR P γ μ α₁ B Z *
      structureConstant P M γ μ (2 * Q γ - α₁ - 2 / γ) α₂ α₃ := by
  dsimp only
  let p := (α₁ + α₂ + α₃ - 2 / γ - 2 * Q γ) / γ
  let a := reflectionExponent γ α₁
  have hp : 0 < p := div_pos (by linarith only [hs]) hγ
  have horder : sExp γ (2 * Q γ - α₁ - 2 / γ) α₂ α₃ = p + a := by
    unfold sExp
    exact dual_window_zero_mode_order γ α₁ α₂ α₃
  change (a * Real.Gamma (-a) * Real.Gamma (p + a) / Real.Gamma p) *
    reflectionBarR P γ α₁ B Z *
    (∫⁻ ω, rho γ (M ω) (2 * Q γ - α₁ - 2 / γ) α₂ α₃ ^ (-(p + a)) ∂P).toReal =
    1 / 2 * μ ^ p * γ * (Real.Gamma p)⁻¹ * reflectionR P γ μ α₁ B Z *
      structureConstant P M γ μ (2 * Q γ - α₁ - 2 / γ) α₂ α₃
  unfold reflectionR structureConstant
  rw [horder]
  change (a * Real.Gamma (-a) * Real.Gamma (p + a) / Real.Gamma p) *
    reflectionBarR P γ α₁ B Z *
    (∫⁻ ω, rho γ (M ω) (2 * Q γ - α₁ - 2 / γ) α₂ α₃ ^ (-(p + a)) ∂P).toReal =
    1 / 2 * μ ^ p * γ * (Real.Gamma p)⁻¹ *
      (μ ^ a * Real.Gamma (-a) * a * reflectionBarR P γ α₁ B Z) *
      (2 * μ ^ (-(p + a)) / γ * Real.Gamma (p + a) *
        (∫⁻ ω, rho γ (M ω) (2 * Q γ - α₁ - 2 / γ) α₂ α₃ ^ (-(p + a)) ∂P).toReal)
  have hpow : μ ^ p * μ ^ a * μ ^ (-(p + a)) = 1 := by
    rw [← Real.rpow_add hμ, ← Real.rpow_add hμ, add_neg_cancel, Real.rpow_zero]
  have hΓ : Real.Gamma p ≠ 0 := (Real.Gamma_pos_of_pos hp).ne'
  have hγne : γ ≠ 0 := hγ.ne'
  field_simp
  linear_combination -(a * Real.Gamma (-a) * Real.Gamma (p + a) *
    reflectionBarR P γ α₁ B Z *
    (∫⁻ ω, rho γ (M ω) (((2 * Q γ - α₁) * γ - 2) / γ) α₂ α₃ ^
      (-(p + a)) ∂P).toReal) * hpow


end DOZZ.Proofs

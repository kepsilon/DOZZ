/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.GammaHalfReflectedOuterLittleO
public import DOZZ.Statements.FourPoint.FourPointTZeroEqStructureConstant
public import DOZZ.FourPoint.Reflected.Normalization
public import DOZZ.FourPoint.Reflected.Remainder
import Mathlib.Tactic

/-! # Reflected fusion from the inner-limit conclusion

The conditional reduction takes the literal inner-limit conclusion as an explicitly supplied
input.
-/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The real part of a complex reflected remainder has the signed little-o limit. -/
theorem reflected_real_part_remainder (κ : ℝ) (r : ℂ → ℂ)
    (hr : IsComplexLittleOAtZero κ r) :
    Tendsto (fun z => (r z).re / ‖z‖ ^ κ)
      (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}) (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have he : (fun z => ‖(r z).re / ‖z‖ ^ κ‖) =
      fun z => |(r z).re| / ‖z‖ ^ κ := by
    funext z
    rw [norm_div, Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  rw [he]
  exact squeeze_zero (fun z => div_nonneg (abs_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))
    (fun z => div_le_div_of_nonneg_right (Complex.abs_re_le_norm (r z))
      (Real.rpow_nonneg (norm_nonneg _) _)) hr

/-- Adding the outer remainder `DOZZ.gammaHalf_reflected_outer_littleO` to the exact inner
conclusion gives the full reflected fusion statement, with the same supplied-space reflection
witness. -/
theorem gammaHalf_reflected_fusion_asymptotic_of_inner_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (X : Ω → Distr)
    (γ μ α₁ α₂ α₃ ξ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hμ : 0 < μ)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃)
    (hreflect : Q γ - α₁ < γ / 2)
    (hξ : 0 < ξ) (hξ₂ : ξ < 1) (hslack : γ * (Q γ - α₁) < ξ)
    (hfreeze : γ * (Q γ - α₁) <
      (1 - ξ) * (γ * (Q γ - α₁) + (α₁ + γ / 2 - Q γ) ^ 2 / 2))
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hinner :
    ∃ B : ℝ → Ω → BrownianPath × BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
        IsReflectionData P γ α₁ (B α₁) Z ∧
        let p := (α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ
        let κ := γ * (Q γ - α₁)
        ∃ r : ℂ → ℂ,
          (∀ z,
            (((gammaHalfMoment P M γ α₁ α₂ α₃ p z -
                gammaHalfOuterMoment P M γ α₁ α₂ α₃ p z ξ) : ℝ) : ℂ) =
              ((((1 / 2 * μ ^ p * γ * (Real.Gamma p)⁻¹ *
                  reflectionR P γ μ α₁ (B α₁) Z *
                  structureConstant P M γ μ (2 * Q γ - α₁ - γ / 2) α₂ α₃ : ℝ) : ℂ) *
                ((‖z‖ ^ κ : ℝ) : ℂ)) + r z)) ∧
            IsComplexLittleOAtZero κ r) :
    ∃ B : ℝ → Ω → BrownianPath × BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
        IsReflectionData P γ α₁ (B α₁) Z ∧
        let κ := γ * (Q γ - α₁)
        ∃ r : ℂ → ℝ,
          (∀ z, fourPointT P M γ μ (-γ / 2) α₁ α₂ α₃ z =
            structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ +
              reflectionR P γ μ α₁ (B α₁) Z *
                structureConstant P M γ μ (2 * Q γ - α₁ - γ / 2) α₂ α₃ *
                  (‖z‖ ^ κ : ℝ) + r z) ∧
            Tendsto (fun z => r z / ‖z‖ ^ κ)
              (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}) (nhds 0) := by
  obtain ⟨B, Z, hZ, hB, rI, hI, hrI⟩ := hinner
  let p : ℝ := (α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ
  let κ : ℝ := γ * (Q γ - α₁)
  let N : ℝ := 2 * μ ^ (-p) / γ * Real.Gamma p
  let D : ℝ := reflectionR P γ μ α₁ (B α₁) Z *
    structureConstant P M γ μ (2 * Q γ - α₁ - γ / 2) α₂ α₃
  let C₀ : ℝ := structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃
  let r : ℂ → ℝ := fun z => fourPointT P M γ μ (-γ / 2) α₁ α₂ α₃ z - C₀ - D * ‖z‖ ^ κ
  have hp : 0 < p := div_pos (by linarith only [hs]) hγ
  have hT (z : ℂ) : fourPointT P M γ μ (-γ / 2) α₁ α₂ α₃ z =
      N * gammaHalfMoment P M γ α₁ α₂ α₃ p z := by
    simpa only [neg_div] using fourPointT_eq_gammaHalfMoment P M γ μ α₁ α₂ α₃ z
  have hzero : N * gammaHalfMoment P M γ α₁ α₂ α₃ p 0 = C₀ := by
    rw [← hT 0]
    simpa only [neg_div] using DOZZ.fourPointT_zero_eq_structureConstant P X M γ μ (γ / 2) α₁ α₂ α₃
      hγ hγ₂ hμ (by linarith only [hα₁, hγ]) hα₂ hα₃ (by linarith only [hs]) hX hM
  have hcancel := reflected_prefactor_cancel γ μ p
    (reflectionR P γ μ α₁ (B α₁) Z)
    (structureConstant P M γ μ (2 * Q γ - α₁ - γ / 2) α₂ α₃) hγ hμ hp
  have hr (z : ℂ) : r z = N *
      (gammaHalfOuterMoment P M γ α₁ α₂ α₃ p z ξ -
        gammaHalfMoment P M γ α₁ α₂ α₃ p 0 + (rI z).re) := by
    have hh := congrArg Complex.re (hI z)
    simp only [Complex.ofReal_re, Complex.add_re, Complex.mul_re,
      Complex.ofReal_im, mul_zero, sub_zero] at hh
    dsimp only [r]
    rw [hT z, ← hzero]
    linear_combination N * hh + (‖z‖ ^ κ) * hcancel
  refine ⟨B, Z, hZ, hB, r, ?_, ?_⟩
  · intro z
    dsimp only [r, C₀, D]
    ring
  · have ho := DOZZ.gammaHalf_reflected_outer_littleO P X M γ α₁ α₂ α₃ ξ
      hγ hγ₂ hξ hξ₂ hα₂ hα₃ hs hα₁ hreflect hslack hfreeze hX hM
    have hor := (isComplexLittleOAtZero_ofReal_iff κ _).mp ho
    have hir := reflected_real_part_remainder κ rI hrI
    have ht := (hor.add hir).const_mul N
    simp only [add_zero, mul_zero] at ht
    apply ht.congr'
    filter_upwards [] with z
    rw [hr z]
    ring

end DOZZ.Proofs

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.ReflectedEnd.FusionReduction
public import DOZZ.FourPoint.Dual.DiagonalReduction
import Mathlib.Tactic

/-! # Reflected formula from the fusion and classification conclusions

The coefficient is identified on the positive real ray using the existing Gauss endpoint
lemmas.
-/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The diagonal conclusion and the reflected fusion coefficient give the full
formula on the cut plane, with precisely the same reflection witness. -/
theorem gammaHalf_reflected_formula_of_fusion_and_classification {Ω : Type*} [MeasurableSpace Ω]
    {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H)
    (P : Measure Ω) (M : Ω → Measure ℂ) (X : Ω → Distr)
    (γ μ α₁ α₂ α₃ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃)
    (hnear : ∃ ξ : ℝ, 0 < ξ ∧ ξ < 1 ∧ γ * (Q γ - α₁) < ξ ∧
      γ * (Q γ - α₁) < (1 - ξ) * (γ * (Q γ - α₁) + (α₁ + γ / 2 - Q γ) ^ 2 / 2))
    (hfusion :
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
              (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}) (nhds 0))
    (hclassification :
    let a := gaussParameterA γ (γ / 2) α₁ α₂ α₃
    let b := gaussParameterB γ (γ / 2) α₁ α₂ α₃
    let c := gaussParameterC γ (γ / 2) α₁
    ∀ z ∈ gaussCutPlane,
      fourPointT P M γ μ (-(γ / 2)) α₁ α₂ α₃ z =
        structureConstant P M γ μ (α₁ - (γ / 2)) α₂ α₃ *
          (‖gaussFMinus H a b c z‖ ^ 2 +
            gaussCoefficientRatio a b c *
              ‖gaussFPlus H a b c z‖ ^ 2)) :
    ∃ B : ℝ → Ω → BrownianPath × BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
        IsReflectionData P γ α₁ (B α₁) Z ∧
        let a := gaussParameterA γ (γ / 2) α₁ α₂ α₃
        let b := gaussParameterB γ (γ / 2) α₁ α₂ α₃
        let c := gaussParameterC γ (γ / 2) α₁
        ∀ z ∈ gaussCutPlane,
          fourPointT P M γ μ (-γ / 2) α₁ α₂ α₃ z =
            structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ *
                ‖gaussFMinus H a b c z‖ ^ 2 +
              reflectionR P γ μ α₁ (B α₁) Z *
                structureConstant P M γ μ (2 * Q γ - α₁ - γ / 2) α₂ α₃ *
                  ‖gaussFPlus H a b c z‖ ^ 2 := by
  obtain ⟨B, Z, hZ, hB, r, hr, hlim⟩ := hfusion
  obtain ⟨ξ, _, hξ₂, hslack, _⟩ := hnear
  let κ : ℝ := γ * (Q γ - α₁)
  let D : ℝ := reflectionR P γ μ α₁ (B α₁) Z *
    structureConstant P M γ μ (2 * Q γ - α₁ - γ / 2) α₂ α₃
  let C₀ : ℝ := structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃
  change (∀ z, fourPointT P M γ μ (-γ / 2) α₁ α₂ α₃ z = C₀ + D * ‖z‖ ^ κ + r z) at hr
  change Tendsto (fun z => r z / ‖z‖ ^ κ)
    (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}) (nhds 0) at hlim
  have hκ : κ < 1 := hslack.trans hξ₂
  have hcast : Tendsto (fun t : ℝ => (t : ℂ))
      (nhdsWithin 0 (Ioi 0)) (nhdsWithin 0 {z : ℂ | z ≠ 0}) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_id.mono_left nhdsWithin_le_nhds), ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    simpa only [Complex.ofReal_ne_zero] using ne_of_gt ht
  have hrl : Tendsto (fun t : ℝ => r (t : ℂ) / t ^ κ)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    apply (hlim.comp hcast).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [Function.comp_def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  have hray : Tendsto (fun t : ℝ =>
      (fourPointT P M γ μ (-γ / 2) α₁ α₂ α₃ (t : ℂ) - C₀) / t ^ κ)
      (nhdsWithin 0 (Ioi 0)) (nhds D) := by
    have ht := hrl.const_add D
    simp only [add_zero] at ht
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [hr (t : ℂ)]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    have hn : t ^ κ ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
    field_simp
    ring
  dsimp only at hclassification ⊢
  obtain ⟨hA, hAB, hBC, hC, _, _, _, _⟩ := DOZZ.gauss_physical_parameter_range
    γ (γ / 2) α₁ α₂ α₃ hγ hγ₂ (Or.inl rfl) hs hα₁ hα₂ hα₃
  have hc : 0 < gaussParameterC γ (γ / 2) α₁ := hA.trans (hAB.trans hBC)
  have he : 2 * (1 - gaussParameterC γ (γ / 2) α₁) = κ := by
    unfold gaussParameterC
    dsimp only [κ]
    ring
  have hid := dual_diagonal_coefficient_identification hH
    (gaussParameterA γ (γ / 2) α₁ α₂ α₃)
    (gaussParameterB γ (γ / 2) α₁ α₂ α₃)
    (gaussParameterC γ (γ / 2) α₁) C₀
    (gaussCoefficientRatio (gaussParameterA γ (γ / 2) α₁ α₂ α₃)
      (gaussParameterB γ (γ / 2) α₁ α₂ α₃) (gaussParameterC γ (γ / 2) α₁)) D
    hc hC (he ▸ hκ) (fourPointT P M γ μ (-γ / 2) α₁ α₂ α₃)
    (by simpa only [neg_div] using hclassification) (by simpa only [he] using hray)
  refine ⟨B, Z, hZ, hB, ?_⟩
  intro z hz
  rw [show fourPointT P M γ μ (-γ / 2) α₁ α₂ α₃ z = _ from
    by simpa only [neg_div] using hclassification z hz]
  change C₀ * (_ + _ * _) = C₀ * _ + D * _
  rw [hid]
  ring

end DOZZ.Proofs

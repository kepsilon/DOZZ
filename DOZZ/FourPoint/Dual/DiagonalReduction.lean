/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Dual.BasisAsymptotic
public import DOZZ.FourPoint.Dual.Parameters
import Mathlib.Tactic

/-! # Coefficient extraction from a diagonal Gauss conclusion

This module does not import the physical classification. It extracts
its second coefficient from the positive-ray fusion limit.
-/

public section

open Filter Topology Set

namespace DOZZ.Proofs

/-- The normalized diagonal Gauss expression has positive-ray coefficient C*d. -/
theorem dual_diagonal_ray_limit {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) (a b : ℂ) (c C d : ℝ)
    (_hc : 0 < c) (hc₁ : c < 1) (hκ : 2 * (1 - c) < 1) :
    Tendsto (fun t : ℝ =>
      (C * (‖gaussFMinus H a b c (t : ℂ)‖ ^ 2 +
        d * ‖gaussFPlus H a b c (t : ℂ)‖ ^ 2) - C) /
        t ^ (2 * (1 - c))) (nhdsWithin 0 (Ioi 0)) (nhds (C * d)) := by
  have hn : ∀ n : ℕ, (c : ℂ) ≠ -(n : ℂ) := by
    intro n h
    have he := congrArg Complex.re h
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at he
    have : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith only [_hc, he, this]
  have hn₂ : ∀ n : ℕ, (2 - (c : ℂ)) ≠ -(n : ℂ) := by
    intro n h
    have he := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.neg_re,
      Complex.natCast_re] at he
    norm_num at he
    have : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hcast : Tendsto (fun t : ℝ => (t : ℂ))
      (nhdsWithin 0 (Ioi 0)) (nhdsWithin 0 {z : ℂ | z ≠ 0}) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_id.mono_left nhdsWithin_le_nhds), ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    simpa only [Complex.ofReal_ne_zero] using ne_of_gt ht
  have hm := (dual_gauss_norm_sq_littleO hH a b c hn (2 * (1 - c)) hκ).comp hcast
  have hp := dual_gauss_plus_norm_sq_ratio hH a b c hn₂
  have hsum := (hm.const_mul C).add (hp.const_mul (C * d))
  simp only [mul_zero, mul_one, zero_add] at hsum
  have ht : Tendsto (fun t : ℝ =>
      C * ((‖gaussFMinus H a b c (t : ℂ)‖ ^ 2 - 1) / t ^ (2 * (1 - c))) +
      (C * d) * (‖gaussFPlus H a b c (t : ℂ)‖ ^ 2 / t ^ (2 * (1 - c))))
      (nhdsWithin 0 (Ioi 0)) (nhds (C * d)) := by
    apply hsum.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [Function.comp_def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  apply ht.congr'
  filter_upwards [] with t
  ring

/-- Any fusion coefficient of the same diagonal observable equals its Gauss coefficient. -/
theorem dual_diagonal_coefficient_identification {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) (a b : ℂ) (c C d D : ℝ)
    (hc : 0 < c) (hc₁ : c < 1) (hκ : 2 * (1 - c) < 1)
    (T : ℂ → ℝ)
    (hdiag : ∀ z ∈ gaussCutPlane, T z =
      C * (‖gaussFMinus H a b c z‖ ^ 2 + d * ‖gaussFPlus H a b c z‖ ^ 2))
    (hfusion : Tendsto (fun t : ℝ => (T (t : ℂ) - C) / t ^ (2 * (1 - c)))
      (nhdsWithin 0 (Ioi 0)) (nhds D)) : D = C * d := by
  have hd := dual_diagonal_ray_limit hH a b c C d hc hc₁ hκ
  have he : ∀ᶠ t : ℝ in nhdsWithin 0 (Ioi 0), (t : ℂ) ∈ gaussCutPlane := by
    filter_upwards [self_mem_nhdsWithin,
      (tendsto_id.mono_left nhdsWithin_le_nhds).eventually
        (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with t ht ht₁
    exact Or.inr ⟨ht, ht₁⟩
  have hd' : Tendsto (fun t : ℝ => (T (t : ℂ) - C) / t ^ (2 * (1 - c)))
      (nhdsWithin 0 (Ioi 0)) (nhds (C * d)) := by
    apply hd.congr'
    filter_upwards [he] with t ht
    rw [hdiag (t : ℂ) ht]
  exact tendsto_nhds_unique hfusion hd'

/-- With the literal classification conclusion as a hypothesis, a dual fusion
limit identifies the reflected coefficient throughout the cut plane. The stochastic
fusion limit is a separate input to this coefficient comparison. -/
theorem dual_physical_classification_reduction {Ω : Type*} [MeasurableSpace Ω]
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (P : MeasureTheory.Measure Ω) (M : Ω → MeasureTheory.Measure ℂ)
    (γ μ α₁ α₂ α₃ D : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ + 2 / γ < α₁ + α₂ + α₃)
    (hκ : (4 / γ) * (Q γ - α₁) < 1)
    (hclassification :
      let a := gaussParameterA γ (2 / γ) α₁ α₂ α₃
      let b := gaussParameterB γ (2 / γ) α₁ α₂ α₃
      let c := gaussParameterC γ (2 / γ) α₁
      ∀ z ∈ gaussCutPlane,
        fourPointT P M γ μ (-(2 / γ)) α₁ α₂ α₃ z =
          structureConstant P M γ μ (α₁ - 2 / γ) α₂ α₃ *
            (‖gaussFMinus H a b c z‖ ^ 2 +
              gaussCoefficientRatio a b c * ‖gaussFPlus H a b c z‖ ^ 2))
    (hfusion : Tendsto (fun t : ℝ =>
      (fourPointT P M γ μ (-(2 / γ)) α₁ α₂ α₃ (t : ℂ) -
        structureConstant P M γ μ (α₁ - 2 / γ) α₂ α₃) /
          t ^ ((4 / γ) * (Q γ - α₁))) (nhdsWithin 0 (Ioi 0)) (nhds D)) :
    let a := gaussParameterA γ (2 / γ) α₁ α₂ α₃
    let b := gaussParameterB γ (2 / γ) α₁ α₂ α₃
    let c := gaussParameterC γ (2 / γ) α₁
    D = structureConstant P M γ μ (α₁ - 2 / γ) α₂ α₃ * gaussCoefficientRatio a b c ∧
    ∀ z ∈ gaussCutPlane, fourPointT P M γ μ (-(2 / γ)) α₁ α₂ α₃ z =
      structureConstant P M γ μ (α₁ - 2 / γ) α₂ α₃ * ‖gaussFMinus H a b c z‖ ^ 2 +
        D * ‖gaussFPlus H a b c z‖ ^ 2 := by
  dsimp only at hclassification ⊢
  obtain ⟨hA, hAB, hBC, hC, _, _, _, _⟩ :=
    DOZZ.gauss_physical_parameter_range γ (2 / γ) α₁ α₂ α₃
      hγ hγ₂ (Or.inr rfl) hs hα₁ hα₂ hα₃
  have hc : 0 < gaussParameterC γ (2 / γ) α₁ := hA.trans (hAB.trans hBC)
  have he : 2 * (1 - gaussParameterC γ (2 / γ) α₁) =
      (4 / γ) * (Q γ - α₁) := by unfold gaussParameterC; ring
  have hid := dual_diagonal_coefficient_identification hH
    (gaussParameterA γ (2 / γ) α₁ α₂ α₃)
    (gaussParameterB γ (2 / γ) α₁ α₂ α₃)
    (gaussParameterC γ (2 / γ) α₁)
    (structureConstant P M γ μ (α₁ - 2 / γ) α₂ α₃)
    (gaussCoefficientRatio (gaussParameterA γ (2 / γ) α₁ α₂ α₃)
      (gaussParameterB γ (2 / γ) α₁ α₂ α₃) (gaussParameterC γ (2 / γ) α₁)) D
    hc hC (he ▸ hκ) (fourPointT P M γ μ (-(2 / γ)) α₁ α₂ α₃)
    hclassification (by simpa only [he] using hfusion)
  refine ⟨hid, ?_⟩
  intro z hz
  rw [hclassification z hz, hid]
  ring

end DOZZ.Proofs

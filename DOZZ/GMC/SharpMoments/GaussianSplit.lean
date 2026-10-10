/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real

/-! # Splitting Gaussian averages of antitone functions

For an antitone function `f` with values in `[0, 1]`, a Gaussian average of `f (y + γ w)` is at
most the Gaussian lower-tail probability `P {γ w < -u}` plus `f (y - u)`: off the tail event the
shift `γ w` is at least `-u`, and antitonicity compares `f (y + γ w)` with `f (y - u)`. Applying
this twice, together with the elementary bound `(s + t)^2 ≤ (1 + 1/ε) s^2 + (1 + ε) t^2`, controls
two nested Gaussian averages of `f`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-! ### Elementary and integrability lemmas -/

/-- The elementary inequality `(s + t)^2 ≤ (1 + 1/ε) s^2 + (1 + ε) t^2` for `ε > 0`, which is
`2 s t ≤ s^2 / ε + ε t^2` in disguise. -/
theorem gaussianSplit_sq_add_le (s t ε : ℝ) (hε : 0 < ε) :
    (s + t) ^ 2 ≤ (1 + 1 / ε) * s ^ 2 + (1 + ε) * t ^ 2 := by
  have h : 0 ≤ (s - ε * t) ^ 2 / ε := by positivity
  have h' : (1 + 1 / ε) * s ^ 2 + (1 + ε) * t ^ 2 - (s + t) ^ 2 = (s - ε * t) ^ 2 / ε := by
    field_simp
    ring
  linarith

/-- A measurable function with values in `[0, 1]` is integrable for a finite measure. -/
theorem gaussianSplit_integrable_of_bounds {μ : Measure ℝ} [IsFiniteMeasure μ] {g : ℝ → ℝ}
    (hg : Measurable g) (h0 : ∀ y, 0 ≤ g y) (h1 : ∀ y, g y ≤ 1) : Integrable g μ :=
  Integrable.of_bound hg.aestronglyMeasurable 1
    (ae_of_all _ fun y => by rw [Real.norm_of_nonneg (h0 y)]; exact h1 y)

/-- The Gaussian lower-tail event `{w | γ w < -u}` is measurable. -/
theorem gaussianSplit_measurableSet_tail (γ u : ℝ) : MeasurableSet {w : ℝ | γ * w < -u} :=
  measurableSet_lt (by fun_prop) (by fun_prop)

/-! ### The inner average -/

/-- The integrand of the inner Gaussian average is integrable. -/
theorem gaussianSplit_integrable_shift (f : ℝ → ℝ) (hf : Antitone f) (hf0 : ∀ y, 0 ≤ f y)
    (hf1 : ∀ y, f y ≤ 1) (γ : ℝ) (v : ℝ≥0) (y : ℝ) :
    Integrable (fun w => f (y + γ * w)) (gaussianReal 0 v) :=
  gaussianSplit_integrable_of_bounds (hf.measurable.comp (by fun_prop)) (fun _ => hf0 _)
    (fun _ => hf1 _)

/-- Pointwise splitting: `f (y + γ w) ≤ 1_{γ w < -u} + f (y - u)`. -/
theorem gaussianSplit_pointwise (f : ℝ → ℝ) (hf : Antitone f) (hf0 : ∀ y, 0 ≤ f y)
    (hf1 : ∀ y, f y ≤ 1) (γ u y w : ℝ) :
    f (y + γ * w) ≤ {w : ℝ | γ * w < -u}.indicator 1 w + f (y - u) := by
  by_cases hw : γ * w < -u
  · have hmem : w ∈ {w : ℝ | γ * w < -u} := hw
    rw [Set.indicator_of_mem hmem]
    have h1 := hf1 (y + γ * w)
    have h2 := hf0 (y - u)
    simp only [Pi.one_apply]
    linarith
  · have hnot : w ∉ {w : ℝ | γ * w < -u} := hw
    rw [Set.indicator_of_notMem hnot]
    have hle : y - u ≤ y + γ * w := by linarith [not_lt.1 hw]
    simpa using hf hle

/-- The inner Gaussian average is nonnegative. -/
theorem gaussianSplit_inner_nonneg (f : ℝ → ℝ) (hf0 : ∀ y, 0 ≤ f y) (γ : ℝ) (v : ℝ≥0)
    (y : ℝ) : 0 ≤ ∫ w, f (y + γ * w) ∂gaussianReal 0 v :=
  integral_nonneg fun _ => hf0 _

/-- The inner Gaussian average is at most one. -/
theorem gaussianSplit_inner_le_one (f : ℝ → ℝ) (hf : Antitone f) (hf0 : ∀ y, 0 ≤ f y)
    (hf1 : ∀ y, f y ≤ 1) (γ : ℝ) (v : ℝ≥0) (y : ℝ) :
    ∫ w, f (y + γ * w) ∂gaussianReal 0 v ≤ 1 := by
  calc ∫ w, f (y + γ * w) ∂gaussianReal 0 v ≤ ∫ _w, (1 : ℝ) ∂gaussianReal 0 v :=
        integral_mono (gaussianSplit_integrable_shift f hf hf0 hf1 γ v y) (integrable_const _)
          fun _ => hf1 _
    _ = 1 := by simp

/-- The inner Gaussian average is antitone in the base point. -/
theorem gaussianSplit_inner_antitone (f : ℝ → ℝ) (hf : Antitone f) (hf0 : ∀ y, 0 ≤ f y)
    (hf1 : ∀ y, f y ≤ 1) (γ : ℝ) (v : ℝ≥0) :
    Antitone fun y => ∫ w, f (y + γ * w) ∂gaussianReal 0 v := by
  intro y₁ y₂ h
  exact integral_mono (gaussianSplit_integrable_shift f hf hf0 hf1 γ v y₂)
    (gaussianSplit_integrable_shift f hf hf0 hf1 γ v y₁) fun w => hf (by linarith)

/-- The inner Gaussian average is at most the lower-tail probability plus `f (y - u)`. -/
theorem gaussianSplit_inner_le (f : ℝ → ℝ) (hf : Antitone f) (hf0 : ∀ y, 0 ≤ f y)
    (hf1 : ∀ y, f y ≤ 1) (γ : ℝ) (v : ℝ≥0) (u y : ℝ) :
    ∫ w, f (y + γ * w) ∂gaussianReal 0 v ≤
      (gaussianReal 0 v {w | γ * w < -u}).toReal + f (y - u) := by
  have hB := gaussianSplit_measurableSet_tail γ u
  have hind : Integrable ({w : ℝ | γ * w < -u}.indicator (1 : ℝ → ℝ)) (gaussianReal 0 v) :=
    (integrable_const (1 : ℝ)).indicator hB
  calc ∫ w, f (y + γ * w) ∂gaussianReal 0 v
      ≤ ∫ w, ({w : ℝ | γ * w < -u}.indicator 1 w + f (y - u)) ∂gaussianReal 0 v :=
        integral_mono (gaussianSplit_integrable_shift f hf hf0 hf1 γ v y)
          (hind.add (integrable_const _)) fun w => gaussianSplit_pointwise f hf hf0 hf1 γ u y w
    _ = (gaussianReal 0 v {w | γ * w < -u}).toReal + f (y - u) := by
        rw [integral_add hind (integrable_const _), integral_indicator_one hB, integral_const]
        simp [Measure.real]

/-! ### The outer average -/

/-- Abstract pointwise bound for the square of an antitone `[0, 1]`-valued function `ψ` that
satisfies `ψ (c - u) ≤ P + F`: on the tail event `{γ ξ < -u}` use `ψ ≤ 1`, and off it compare
`ψ (c + γ ξ)` with `ψ (c - u)`. -/
theorem gaussianSplit_sq_pointwise (ψ : ℝ → ℝ) (hψa : Antitone ψ) (hψ0 : ∀ y, 0 ≤ ψ y)
    (hψ1 : ∀ y, ψ y ≤ 1) (γ c u ε P F : ℝ) (hε : 0 < ε) (hψ : ψ (c - u) ≤ P + F) (ξ : ℝ) :
    ψ (c + γ * ξ) ^ 2 ≤
      {ξ : ℝ | γ * ξ < -u}.indicator 1 ξ + ((1 + ε) * F ^ 2 + (1 + 1 / ε) * P ^ 2) := by
  have hnn : 0 ≤ (1 + ε) * F ^ 2 + (1 + 1 / ε) * P ^ 2 := by positivity
  by_cases hξ : γ * ξ < -u
  · have hmem : ξ ∈ {ξ : ℝ | γ * ξ < -u} := hξ
    rw [Set.indicator_of_mem hmem]
    have hsq : ψ (c + γ * ξ) ^ 2 ≤ 1 := pow_le_one₀ (hψ0 _) (hψ1 _)
    simp only [Pi.one_apply]
    linarith
  · have hnot : ξ ∉ {ξ : ℝ | γ * ξ < -u} := hξ
    rw [Set.indicator_of_notMem hnot, zero_add]
    have hle : c - u ≤ c + γ * ξ := by linarith [not_lt.1 hξ]
    calc ψ (c + γ * ξ) ^ 2 ≤ (P + F) ^ 2 :=
          pow_le_pow_left₀ (hψ0 _) ((hψa hle).trans hψ) 2
      _ ≤ (1 + 1 / ε) * P ^ 2 + (1 + ε) * F ^ 2 := gaussianSplit_sq_add_le P F ε hε
      _ = (1 + ε) * F ^ 2 + (1 + 1 / ε) * P ^ 2 := by ring

/-- Pointwise bound for the squared inner average at the base point `x + a + γ ξ`. -/
theorem gaussianSplit_outer_pointwise (f : ℝ → ℝ) (hf : Antitone f) (hf0 : ∀ y, 0 ≤ f y)
    (hf1 : ∀ y, f y ≤ 1) (γ : ℝ) (v₂ : ℝ≥0) (x a u ε : ℝ) (hε : 0 < ε) (ξ : ℝ) :
    (∫ w, f (x + a + γ * ξ + γ * w) ∂gaussianReal 0 v₂) ^ 2 ≤
      {ξ : ℝ | γ * ξ < -u}.indicator 1 ξ +
        ((1 + ε) * f (x + a - 2 * u) ^ 2 +
          (1 + 1 / ε) * ((gaussianReal 0 v₂ {w | γ * w < -u}).toReal) ^ 2) := by
  have hψ : ∫ w, f (x + a - u + γ * w) ∂gaussianReal 0 v₂ ≤
      (gaussianReal 0 v₂ {w | γ * w < -u}).toReal + f (x + a - 2 * u) := by
    have h := gaussianSplit_inner_le f hf hf0 hf1 γ v₂ u (x + a - u)
    have h2 : x + a - u - u = x + a - 2 * u := by ring
    rwa [h2] at h
  exact gaussianSplit_sq_pointwise (fun y => ∫ w, f (y + γ * w) ∂gaussianReal 0 v₂)
    (gaussianSplit_inner_antitone f hf hf0 hf1 γ v₂)
    (gaussianSplit_inner_nonneg f hf0 γ v₂) (gaussianSplit_inner_le_one f hf hf0 hf1 γ v₂)
    γ (x + a) u ε _ _ hε hψ ξ

/-- Two nested Gaussian averages of an antitone function bounded by one: away from Gaussian
lower-tail events of size `u` in each average, the shifts are at least `-u`. -/
theorem gaussianSplit_two_branch
    (f : ℝ → ℝ) (hf : Antitone f) (hf0 : ∀ y, 0 ≤ f y) (hf1 : ∀ y, f y ≤ 1)
    (γ : ℝ) (v₁ v₂ : ℝ≥0) (x a u ε : ℝ) (hε : 0 < ε) :
    (∫ ξ, (∫ w, f (x + a + γ * ξ + γ * w) ∂gaussianReal 0 v₂) ^ 2 ∂gaussianReal 0 v₁) ≤
      (gaussianReal 0 v₁ {ξ | γ * ξ < -u}).toReal +
        (1 + ε) * f (x + a - 2 * u) ^ 2 +
        (1 + 1 / ε) * ((gaussianReal 0 v₂ {w | γ * w < -u}).toReal) ^ 2 := by
  have hB := gaussianSplit_measurableSet_tail γ u
  have hmeas : Measurable fun ξ : ℝ =>
      (∫ w, f (x + a + γ * ξ + γ * w) ∂gaussianReal 0 v₂) ^ 2 :=
    ((gaussianSplit_inner_antitone f hf hf0 hf1 γ v₂).measurable.comp
      (by fun_prop : Measurable fun ξ : ℝ => x + a + γ * ξ)).pow_const 2
  have hint : Integrable (fun ξ : ℝ =>
      (∫ w, f (x + a + γ * ξ + γ * w) ∂gaussianReal 0 v₂) ^ 2) (gaussianReal 0 v₁) :=
    gaussianSplit_integrable_of_bounds hmeas (fun _ => sq_nonneg _) fun ξ =>
      pow_le_one₀ (gaussianSplit_inner_nonneg f hf0 γ v₂ (x + a + γ * ξ))
        (gaussianSplit_inner_le_one f hf hf0 hf1 γ v₂ (x + a + γ * ξ))
  have hind : Integrable ({ξ : ℝ | γ * ξ < -u}.indicator (1 : ℝ → ℝ)) (gaussianReal 0 v₁) :=
    (integrable_const (1 : ℝ)).indicator hB
  calc ∫ ξ, (∫ w, f (x + a + γ * ξ + γ * w) ∂gaussianReal 0 v₂) ^ 2 ∂gaussianReal 0 v₁
      ≤ ∫ ξ, ({ξ : ℝ | γ * ξ < -u}.indicator 1 ξ +
          ((1 + ε) * f (x + a - 2 * u) ^ 2 +
            (1 + 1 / ε) * ((gaussianReal 0 v₂ {w | γ * w < -u}).toReal) ^ 2)) ∂gaussianReal 0 v₁ :=
        integral_mono hint (hind.add (integrable_const _))
          fun ξ => gaussianSplit_outer_pointwise f hf hf0 hf1 γ v₂ x a u ε hε ξ
    _ = (gaussianReal 0 v₁ {ξ | γ * ξ < -u}).toReal +
          ((1 + ε) * f (x + a - 2 * u) ^ 2 +
            (1 + 1 / ε) * ((gaussianReal 0 v₂ {w | γ * w < -u}).toReal) ^ 2) := by
        rw [integral_add hind (integrable_const _), integral_indicator_one hB, integral_const]
        simp [Measure.real]
    _ = (gaussianReal 0 v₁ {ξ | γ * ξ < -u}).toReal +
          (1 + ε) * f (x + a - 2 * u) ^ 2 +
          (1 + 1 / ε) * ((gaussianReal 0 v₂ {w | γ * w < -u}).toReal) ^ 2 := by ring

end DOZZ.Proofs

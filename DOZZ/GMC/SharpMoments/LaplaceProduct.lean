/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Laplace transforms of independent sums on a triple product

On `Ω × Ω × ℝ` with the product law `P ⊗ (P ⊗ N)`, the Laplace transform of `m₁ q.1 + m₂ q.2.1`
at a level depending on the scalar coordinate `q.2.2` is the `N`-average of the product of the two
Laplace transforms. This is the independence step of the two-branch inequality. -/

@[expose] public section

open MeasureTheory

namespace DOZZ.Proofs

theorem laplaceProduct_integrand_bound (s m : ℝ) (hs : 0 ≤ s) (hm : 0 ≤ m) :
    ‖Real.exp (-s * m)‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (by nlinarith)

/-- Independence on a triple product factors the Laplace transform of a sum. -/
theorem integral_prod_prod_exp_mul_exp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (N : Measure ℝ) [IsProbabilityMeasure N]
    (m₁ m₂ : Ω → ℝ) (hm₁ : Measurable m₁) (hm₂ : Measurable m₂)
    (hm₁0 : ∀ ω, 0 ≤ m₁ ω) (hm₂0 : ∀ ω, 0 ≤ m₂ ω)
    (s : ℝ → ℝ) (hs : Measurable s) (hs0 : ∀ ξ, 0 ≤ s ξ) :
    ∫ q, Real.exp (-s q.2.2 * m₁ q.1) * Real.exp (-s q.2.2 * m₂ q.2.1) ∂P.prod (P.prod N) =
      ∫ ξ, (∫ ω, Real.exp (-s ξ * m₁ ω) ∂P) * (∫ ω, Real.exp (-s ξ * m₂ ω) ∂P) ∂N := by
  -- integrability of the bounded measurable integrands on the products
  have hf₁ : Measurable (fun p : Ω × ℝ => Real.exp (-s p.2 * m₁ p.1)) := by
    exact Real.measurable_exp.comp (((hs.comp measurable_snd).neg).mul (hm₁.comp measurable_fst))
  have hf₂ : Measurable (fun p : Ω × ℝ => Real.exp (-s p.2 * m₂ p.1)) := by
    exact Real.measurable_exp.comp (((hs.comp measurable_snd).neg).mul (hm₂.comp measurable_fst))
  have hb₁ : ∀ p : Ω × ℝ, ‖Real.exp (-s p.2 * m₁ p.1)‖ ≤ 1 :=
    fun p => laplaceProduct_integrand_bound _ _ (hs0 _) (hm₁0 _)
  have hb₂ : ∀ p : Ω × ℝ, ‖Real.exp (-s p.2 * m₂ p.1)‖ ≤ 1 :=
    fun p => laplaceProduct_integrand_bound _ _ (hs0 _) (hm₂0 _)
  have hF : Integrable (fun q : Ω × Ω × ℝ =>
      Real.exp (-s q.2.2 * m₁ q.1) * Real.exp (-s q.2.2 * m₂ q.2.1)) (P.prod (P.prod N)) := by
    refine Integrable.of_bound (C := 1) ?_ (Filter.Eventually.of_forall fun q => ?_)
    · exact ((hf₁.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))).mul
        (hf₂.comp ((measurable_fst.comp measurable_snd).prodMk
          (measurable_snd.comp measurable_snd)))).aestronglyMeasurable
    · rw [norm_mul]
      calc ‖Real.exp (-s q.2.2 * m₁ q.1)‖ * ‖Real.exp (-s q.2.2 * m₂ q.2.1)‖ ≤ 1 * 1 :=
            mul_le_mul (hb₁ (q.1, q.2.2)) (hb₂ (q.2.1, q.2.2)) (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
  -- first Fubini step over `q.1`
  rw [integral_prod _ hF]
  -- inner Fubini step over `(q.2.1, q.2.2)`, swapping to integrate `q.2.1` first
  have hinner : ∀ ω₁ : Ω, (∫ p : Ω × ℝ, Real.exp (-s p.2 * m₁ ω₁) * Real.exp (-s p.2 * m₂ p.1)
      ∂P.prod N) = ∫ ξ, Real.exp (-s ξ * m₁ ω₁) * ∫ ω, Real.exp (-s ξ * m₂ ω) ∂P ∂N := by
    intro ω₁
    have hG : Integrable (fun p : Ω × ℝ =>
        Real.exp (-s p.2 * m₁ ω₁) * Real.exp (-s p.2 * m₂ p.1)) (P.prod N) := by
      refine Integrable.of_bound (C := 1) ?_ (Filter.Eventually.of_forall fun p => ?_)
      · exact ((hf₁.comp (measurable_const.prodMk measurable_snd)).mul hf₂).aestronglyMeasurable
      · rw [norm_mul]
        calc ‖Real.exp (-s p.2 * m₁ ω₁)‖ * ‖Real.exp (-s p.2 * m₂ p.1)‖ ≤ 1 * 1 :=
              mul_le_mul (hb₁ (ω₁, p.2)) (hb₂ p) (norm_nonneg _) zero_le_one
          _ = 1 := one_mul 1
    rw [integral_prod_symm _ hG]
    apply integral_congr_ae
    filter_upwards [] with ξ
    exact integral_const_mul _ _
  simp_rw [hinner]
  -- swap the remaining two integrals
  have hH : Integrable (fun p : Ω × ℝ =>
      Real.exp (-s p.2 * m₁ p.1) * ∫ ω, Real.exp (-s p.2 * m₂ ω) ∂P) (P.prod N) := by
    have hL : Measurable (fun ξ : ℝ => ∫ ω, Real.exp (-s ξ * m₂ ω) ∂P) := by
      have := hf₂.stronglyMeasurable.integral_prod_left' (μ := P)
      exact this.measurable
    refine Integrable.of_bound (C := 1) ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact (hf₁.mul (hL.comp measurable_snd)).aestronglyMeasurable
    · rw [norm_mul]
      have hint : ‖∫ ω, Real.exp (-s p.2 * m₂ ω) ∂P‖ ≤ 1 := by
        calc ‖∫ ω, Real.exp (-s p.2 * m₂ ω) ∂P‖ ≤ ∫ _ω, (1 : ℝ) ∂P :=
              norm_integral_le_of_norm_le (integrable_const 1)
                (Filter.Eventually.of_forall fun ω => hb₂ (ω, p.2))
          _ = 1 := by simp
      calc ‖Real.exp (-s p.2 * m₁ p.1)‖ * ‖∫ ω, Real.exp (-s p.2 * m₂ ω) ∂P‖ ≤ 1 * 1 :=
            mul_le_mul (hb₁ p) hint (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
  rw [integral_integral_swap hH]
  apply integral_congr_ae
  filter_upwards [] with ξ
  exact integral_mul_const _ _

end DOZZ.Proofs

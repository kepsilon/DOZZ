/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteChaosScaledLaplaceIBP
public import Mathlib.MeasureTheory.Integral.Prod

/-! Product-space forms of the conditional Laplace-score Gaussian IBP. -/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace DOZZ.Proofs

/-- The standard Gaussian law on a finite real coordinate space. -/
noncomputable def standardGaussianFinMeasure (n : ℕ) : Measure (Fin (n + 1) → ℝ) :=
  Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1

instance standardGaussianFinMeasure_isProbability (n : ℕ) :
    IsProbabilityMeasure (standardGaussianFinMeasure n) := by
  dsimp [standardGaussianFinMeasure]
  infer_instance

/-- The linearly interpolated field with a deterministic shift supplied by the other block. -/
noncomputable def finiteChaosTwoBlockField
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (c : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ) (t : ℝ)
    (x y : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun j => Real.sqrt t * (∑ k, A j k * x k) + c y j

/-- One coordinate of the finite-chaos Laplace score along a two-block field. -/
noncomputable def finiteChaosTwoBlockLaplaceScore
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (c : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (a v : Fin (n + 1) → ℝ) (γ s t : ℝ) (i : Fin (n + 1))
    (x y : Fin (n + 1) → ℝ) : ℝ :=
  finiteChaosVectorWeight a v γ (finiteChaosTwoBlockField A c t x y) i *
    (-s * Real.exp (-s * finiteChaosVectorMass a v γ
      (finiteChaosTwoBlockField A c t x y)))

/-- The field-coordinate derivative of the Laplace score, including the diagonal Wick term. -/
noncomputable def finiteChaosTwoBlockLaplaceScoreDerivative
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (c : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (a v : Fin (n + 1) → ℝ) (γ s t : ℝ) (i j : Fin (n + 1))
    (x y : Fin (n + 1) → ℝ) : ℝ :=
  γ * (if i = j then
      finiteChaosVectorWeight a v γ (finiteChaosTwoBlockField A c t x y) i *
        (-s * Real.exp (-s * finiteChaosVectorMass a v γ
          (finiteChaosTwoBlockField A c t x y))) else 0) +
    γ * finiteChaosVectorWeight a v γ (finiteChaosTwoBlockField A c t x y) i *
      finiteChaosVectorWeight a v γ (finiteChaosTwoBlockField A c t x y) j *
        (s ^ 2 * Real.exp (-s * finiteChaosVectorMass a v γ
          (finiteChaosTwoBlockField A c t x y)))

/-- Integrating the conditional `X`-block Laplace-score IBP over an independent standard Gaussian
block gives the covariance identity on the product Gaussian space. The integrability premises are
exactly those needed for Fubini; the uniform Laplace-score bounds supply them in applications. -/
theorem finiteChaos_laplace_X_block_ibp_on_product
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (a v : Fin (n + 1) → ℝ)
    (c : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (γ s t : ℝ) (ha : ∀ j, 0 ≤ a j) (hs : 0 ≤ s) (ht : 0 < t)
    (i : Fin (n + 1))
    (hleft : Integrable
      (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) =>
        (∑ k, A i k * z.2 k) *
          finiteChaosTwoBlockLaplaceScore A c a v γ s t i z.2 z.1)
      ((standardGaussianFinMeasure n).prod (standardGaussianFinMeasure n)))
    (hderiv : ∀ (j : Fin (n + 1)), Integrable
      (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) =>
        finiteChaosTwoBlockLaplaceScoreDerivative A c a v γ s t i j z.2 z.1)
      ((standardGaussianFinMeasure n).prod (standardGaussianFinMeasure n))) :
    ∫ z, (∑ k, A i k * z.2 k) *
        finiteChaosTwoBlockLaplaceScore A c a v γ s t i z.2 z.1
      ∂((standardGaussianFinMeasure n).prod (standardGaussianFinMeasure n)) =
      Real.sqrt t * ∑ j, (∑ k, A i k * A j k) *
        ∫ z, finiteChaosTwoBlockLaplaceScoreDerivative A c a v γ s t i j z.2 z.1
          ∂((standardGaussianFinMeasure n).prod (standardGaussianFinMeasure n)) := by
  classical
  let μ := standardGaussianFinMeasure n
  let V := finiteChaosTwoBlockField A c t
  let W := finiteChaosTwoBlockLaplaceScore A c a v γ s t i
  let D := finiteChaosTwoBlockLaplaceScoreDerivative A c a v γ s t i
  have hconditional (y : Fin (n + 1) → ℝ) :
      ∫ x, (∑ k, A i k * x k) * W x y ∂μ =
        Real.sqrt t * ∑ j, (∑ k, A i k * A j k) *
          ∫ x, D j x y ∂μ := by
    exact finiteChaos_laplace_score_scaled_shifted_standardGaussian_ibp
      A a v (c y) γ s (Real.sqrt t) ha hs (Real.sqrt_pos.2 ht) i
  have hiter :
      ∫ y, ∫ x, (∑ k, A i k * x k) * W x y ∂μ ∂μ =
        Real.sqrt t * ∑ j, (∑ k, A i k * A j k) *
          ∫ y, ∫ x, D j x y ∂μ ∂μ := by
    calc
      ∫ y, ∫ x, (∑ k, A i k * x k) * W x y ∂μ ∂μ =
          ∫ y, Real.sqrt t * ∑ j, (∑ k, A i k * A j k) *
          ∫ x, D j x y ∂μ ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with y
              exact hconditional y
      _ = Real.sqrt t * ∑ j, (∑ k, A i k * A j k) *
            ∫ y, ∫ x, D j x y ∂μ ∂μ := by
              rw [integral_const_mul, integral_finsetSum]
              · apply congrArg (fun q : ℝ => Real.sqrt t * q)
                apply Finset.sum_congr rfl
                intro j hj
                rw [integral_const_mul]
              · intro j hj
                exact (hderiv j).integral_prod_left.const_mul _
  calc
    ∫ z, (∑ k, A i k * z.2 k) * W z.2 z.1 ∂(μ.prod μ) =
        ∫ y, ∫ x, (∑ k, A i k * x k) * W x y ∂μ ∂μ :=
          integral_prod _ hleft
    _ = Real.sqrt t * ∑ j, (∑ k, A i k * A j k) *
        ∫ y, ∫ x, D j x y ∂μ ∂μ := hiter
    _ = Real.sqrt t * ∑ j, (∑ k, A i k * A j k) *
        ∫ z, D j z.2 z.1 ∂(μ.prod μ) := by
          congr 1
          apply Finset.sum_congr rfl
          intro j hj
          congr 1
          exact (integral_prod _ (hderiv j)).symm

/-- The product-integrability conditions for the `X`-block identity follow from the uniform
Laplace-score bounds whenever the deterministic shift is measurable. -/
theorem finiteChaos_laplace_X_block_ibp_on_product_of_measurable_shift
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (a v : Fin (n + 1) → ℝ)
    (c : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ) (hc : Measurable c)
    (γ s t : ℝ) (ha : ∀ j, 0 ≤ a j) (hs : 0 ≤ s) (ht : 0 < t)
    (i : Fin (n + 1)) :
    ∫ z, (∑ k, A i k * z.2 k) *
        finiteChaosTwoBlockLaplaceScore A c a v γ s t i z.2 z.1
      ∂((standardGaussianFinMeasure n).prod (standardGaussianFinMeasure n)) =
      Real.sqrt t * ∑ j, (∑ k, A i k * A j k) *
        ∫ z, finiteChaosTwoBlockLaplaceScoreDerivative A c a v γ s t i j z.2 z.1
          ∂((standardGaussianFinMeasure n).prod (standardGaussianFinMeasure n)) := by
  classical
  let μ := standardGaussianFinMeasure n
  let V := finiteChaosTwoBlockField A c t
  let scoreField : (Fin (n + 1) → ℝ) → ℝ := fun x =>
    finiteChaosVectorWeight a v γ x i *
      (-s * Real.exp (-s * finiteChaosVectorMass a v γ x))
  let derivField : Fin (n + 1) → (Fin (n + 1) → ℝ) → ℝ := fun j x =>
    γ * (if i = j then
        finiteChaosVectorWeight a v γ x i *
          (-s * Real.exp (-s * finiteChaosVectorMass a v γ x)) else 0) +
      γ * finiteChaosVectorWeight a v γ x i * finiteChaosVectorWeight a v γ x j *
        (s ^ 2 * Real.exp (-s * finiteChaosVectorMass a v γ x))
  let score := fun x y => scoreField (V x y)
  let deriv := fun j x y => derivField j (V x y)
  have hcoord (k : Fin (n + 1)) : Integrable (fun x : Fin (n + 1) → ℝ => x k) μ := by
    simpa [μ, standardGaussianFinMeasure] using
      (integrable_eval IsGaussian.integrable_id :
        Integrable (fun x : Fin (n + 1) → ℝ => x k)
          (Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1))
  have hterm (k : Fin (n + 1)) :
      Integrable (fun x : Fin (n + 1) → ℝ => A i k * x k) μ :=
    (hcoord k).const_mul _
  have hlinear : Integrable
      (fun x : Fin (n + 1) → ℝ => ∑ k, A i k * x k) μ := by
    exact integrable_finsetSum Finset.univ (fun k hk => hterm k)
  have hlinearProd : Integrable
      (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) =>
        ∑ k, A i k * z.2 k) (μ.prod μ) := by
    have hsnd : MeasurePreserving Prod.snd (μ.prod μ) μ := measurePreserving_snd
    simpa only [Function.comp_def] using
      hsnd.integrable_comp_of_integrable hlinear
  have hVmeas : Measurable
      (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) =>
        V z.2 z.1) := by
    change Measurable (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) =>
      fun j => Real.sqrt t * (∑ k, A j k * z.2 k) + c z.1 j)
    have hc' : Measurable (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) => c z.1) :=
      hc.comp measurable_fst
    have hlin : Measurable
        (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) =>
          fun j => Real.sqrt t * (∑ k, A j k * z.2 k)) := by
      apply Measurable.of_eval
      intro j
      fun_prop
    exact hlin.add hc'
  have hscoreMeas : Measurable
      (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) => score z.2 z.1) := by
    have hweight (j : Fin (n + 1)) :
        Continuous (fun x : Fin (n + 1) → ℝ => finiteChaosVectorWeight a v γ x j) := by
      fun_prop [finiteChaosVectorWeight]
    have hmass : Continuous (fun x : Fin (n + 1) → ℝ =>
        finiteChaosVectorMass a v γ x) := by
      simp only [finiteChaosVectorMass]
      exact continuous_finsetSum Finset.univ (fun j hj => hweight j)
    have hcont : Continuous scoreField := by
      dsimp [scoreField]
      fun_prop
    change Measurable (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) =>
      scoreField (V z.2 z.1))
    exact hcont.measurable.comp hVmeas
  have hderivMeas : ∀ j : Fin (n + 1), Measurable
      (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) => deriv j z.2 z.1) := by
    intro j
    have hweight (k : Fin (n + 1)) :
        Continuous (fun x : Fin (n + 1) → ℝ => finiteChaosVectorWeight a v γ x k) := by
      fun_prop [finiteChaosVectorWeight]
    have hmass : Continuous (fun x : Fin (n + 1) → ℝ =>
        finiteChaosVectorMass a v γ x) := by
      simp only [finiteChaosVectorMass]
      exact continuous_finsetSum Finset.univ (fun k hk => hweight k)
    have hcont : Continuous (derivField j) := by
      by_cases hij : i = j
      · simp only [derivField, ite_eq_left hij]
        fun_prop
      · simp only [derivField, ite_eq_right hij]
        fun_prop
    change Measurable (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) =>
      derivField j (V z.2 z.1))
    exact hcont.measurable.comp hVmeas
  have hscoreBound (z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) :
      ‖score z.2 z.1‖ ≤ 1 := by
    simpa [score, finiteChaosTwoBlockLaplaceScore,
      scoreField, V, finiteChaosTwoBlockField] using
      finiteChaos_laplace_first_weight_bound a v γ s ha hs
        (finiteChaosTwoBlockField A c t z.2 z.1) i
  have hleft : Integrable
      (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) =>
        (∑ k, A i k * z.2 k) * score z.2 z.1) (μ.prod μ) := by
    apply hlinearProd.norm.mono'
    · exact hlinearProd.aestronglyMeasurable.mul hscoreMeas.aestronglyMeasurable
    · filter_upwards [] with z
      rw [norm_mul]
      calc
        ‖∑ k, A i k * z.2 k‖ * ‖score z.2 z.1‖ ≤
            ‖∑ k, A i k * z.2 k‖ * 1 :=
              mul_le_mul_of_nonneg_left (hscoreBound z) (norm_nonneg _)
        _ = ‖∑ k, A i k * z.2 k‖ := by ring
  have hderiv : ∀ j : Fin (n + 1), Integrable
      (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) => deriv j z.2 z.1)
      (μ.prod μ) := by
    intro j
    refine Integrable.of_bound (hderivMeas j).aestronglyMeasurable
      (5 * |γ|) (ae_of_all _ fun z => ?_)
    simpa [deriv, derivField, V, finiteChaosTwoBlockLaplaceScoreDerivative,
      finiteChaosTwoBlockField] using
      finiteChaos_laplace_score_derivative_norm_le a v γ s ha hs
        (finiteChaosTwoBlockField A c t z.2 z.1) i j
  simpa [μ, score, deriv, standardGaussianFinMeasure,
    V, scoreField, derivField, finiteChaosTwoBlockField,
    finiteChaosTwoBlockLaplaceScore,
    finiteChaosTwoBlockLaplaceScoreDerivative] using
    finiteChaos_laplace_X_block_ibp_on_product
      A a v c γ s t ha hs ht i hleft hderiv

/-- The same product-space identity with the differentiated Gaussian block in the first product
coordinate. This form lets the `Y` block of the interpolation use the same conditional lemma. -/
theorem finiteChaos_laplace_X_block_ibp_on_product_first_of_measurable_shift
    {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (a v : Fin (n + 1) → ℝ)
    (c : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ) (hc : Measurable c)
    (γ s t : ℝ) (ha : ∀ j, 0 ≤ a j) (hs : 0 ≤ s) (ht : 0 < t)
    (i : Fin (n + 1)) :
    ∫ z, (∑ k, A i k * z.1 k) *
        finiteChaosTwoBlockLaplaceScore A c a v γ s t i z.1 z.2
      ∂((standardGaussianFinMeasure n).prod (standardGaussianFinMeasure n)) =
      Real.sqrt t * ∑ j, (∑ k, A i k * A j k) *
        ∫ z, finiteChaosTwoBlockLaplaceScoreDerivative A c a v γ s t i j z.1 z.2
          ∂((standardGaussianFinMeasure n).prod (standardGaussianFinMeasure n)) := by
  classical
  let μ := standardGaussianFinMeasure n
  have hsecond := finiteChaos_laplace_X_block_ibp_on_product_of_measurable_shift
    A a v c hc γ s t ha hs ht i
  have hleft :
      ∫ z, (∑ k, A i k * z.1 k) *
        finiteChaosTwoBlockLaplaceScore A c a v γ s t i z.1 z.2 ∂(μ.prod μ) =
      ∫ z, (∑ k, A i k * z.2 k) *
        finiteChaosTwoBlockLaplaceScore A c a v γ s t i z.2 z.1 ∂(μ.prod μ) := by
    simpa only [Prod.swap] using
      (integral_prod_swap (μ := μ) (ν := μ)
        (f := fun z => (∑ k, A i k * z.2 k) *
          finiteChaosTwoBlockLaplaceScore A c a v γ s t i z.2 z.1))
  have hright (j : Fin (n + 1)) :
      ∫ z, finiteChaosTwoBlockLaplaceScoreDerivative A c a v γ s t i j z.1 z.2
          ∂(μ.prod μ) =
      ∫ z, finiteChaosTwoBlockLaplaceScoreDerivative A c a v γ s t i j z.2 z.1
          ∂(μ.prod μ) := by
    simpa only [Prod.swap] using
      (integral_prod_swap (μ := μ) (ν := μ)
        (f := fun z => finiteChaosTwoBlockLaplaceScoreDerivative A c a v γ s t i j z.2 z.1))
  calc
    _ = ∫ z, (∑ k, A i k * z.2 k) *
        finiteChaosTwoBlockLaplaceScore A c a v γ s t i z.2 z.1 ∂(μ.prod μ) := hleft
    _ = Real.sqrt t * ∑ j, (∑ k, A i k * A j k) *
        ∫ z, finiteChaosTwoBlockLaplaceScoreDerivative A c a v γ s t i j z.2 z.1
          ∂(μ.prod μ) := hsecond
    _ = Real.sqrt t * ∑ j, (∑ k, A i k * A j k) *
        ∫ z, finiteChaosTwoBlockLaplaceScoreDerivative A c a v γ s t i j z.1 z.2
          ∂(μ.prod μ) := by
            congr 1
            apply Finset.sum_congr rfl
            intro j hj
            rw [hright j]

end DOZZ.Proofs

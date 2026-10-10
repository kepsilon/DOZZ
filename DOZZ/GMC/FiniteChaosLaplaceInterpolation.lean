/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteChaosTwoBlockIBP
public import DOZZ.GMC.FiniteChaosInterpolationExpectation
public import DOZZ.GMC.FiniteGaussianInterpolationIdentity
public import DOZZ.GMC.FiniteChaosLaplaceLinearChain

/-! Laplace-test interpolation for finite Gaussian vectors represented on standard coordinates. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace DOZZ.Proofs

/-- The row Gram covariance of a square standard-Gaussian linear image. -/
noncomputable def finiteChaosMatrixRowCovariance {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (i j : Fin (n + 1)) : ℝ := ∑ k, A i k * A j k

/-- The diagonal variance vector of a standard-Gaussian linear image. -/
noncomputable def finiteChaosMatrixRowVariance {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : Fin (n + 1) → ℝ :=
  fun i => finiteChaosMatrixRowCovariance A i i

/-- The field along the independent two-block Gaussian interpolation. -/
noncomputable def finiteChaosMatrixTwoBlockField {n : ℕ}
    (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (t : ℝ)
    (x y : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun i => Real.sqrt t * finiteChaosLinearImageVector A x i +
    Real.sqrt (1 - t) * finiteChaosLinearImageVector B y i

/-- The linearly interpolated Wick variance vector. -/
noncomputable def finiteChaosMatrixTwoBlockVariance {n : ℕ}
    (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (t : ℝ) : Fin (n + 1) → ℝ :=
  fun i => t * finiteChaosMatrixRowVariance A i +
    (1 - t) * finiteChaosMatrixRowVariance B i

/-- One Laplace-score coordinate on the matrix two-block interpolation. -/
noncomputable def finiteChaosMatrixLaplaceScore {n : ℕ}
    (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (a : Fin (n + 1) → ℝ) (γ s t : ℝ) (i : Fin (n + 1))
    (z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) : ℝ :=
  finiteChaosVectorWeight a (finiteChaosMatrixTwoBlockVariance A B t) γ
      (finiteChaosMatrixTwoBlockField A B t z.1 z.2) i *
    (-s * Real.exp (-s * finiteChaosVectorMass a
      (finiteChaosMatrixTwoBlockVariance A B t) γ
      (finiteChaosMatrixTwoBlockField A B t z.1 z.2)))

/-- The mixed second-derivative factor in the Laplace-test interpolation. -/
noncomputable def finiteChaosMatrixLaplaceHessianFactor {n : ℕ}
    (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (a : Fin (n + 1) → ℝ) (γ s t : ℝ) (i j : Fin (n + 1))
    (z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) : ℝ :=
  finiteChaosVectorWeight a (finiteChaosMatrixTwoBlockVariance A B t) γ
      (finiteChaosMatrixTwoBlockField A B t z.1 z.2) i *
    finiteChaosVectorWeight a (finiteChaosMatrixTwoBlockVariance A B t) γ
      (finiteChaosMatrixTwoBlockField A B t z.1 z.2) j *
    (s ^ 2 * Real.exp (-s * finiteChaosVectorMass a
      (finiteChaosMatrixTwoBlockVariance A B t) γ
      (finiteChaosMatrixTwoBlockField A B t z.1 z.2)) )

/-- The Laplace score's derivative with respect to a field coordinate. -/
noncomputable def finiteChaosMatrixLaplaceScoreDerivative {n : ℕ}
    (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (a : Fin (n + 1) → ℝ) (γ s t : ℝ) (i j : Fin (n + 1))
    (z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) : ℝ :=
  γ * (if i = j then finiteChaosMatrixLaplaceScore A B a γ s t i z else 0) +
    γ * finiteChaosMatrixLaplaceHessianFactor A B a γ s t i j z

/-- The pointwise derivative of the Laplace interpolation test expressed as its two Gaussian
linear coordinates and the changing Wick variance. -/
theorem kahaneInterpolatedLaplaceTestDerivative_eq_score_sum
    {n : ℕ} (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (a : Fin (n + 1) → ℝ) (γ s t : ℝ)
    (z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) :
    kahaneInterpolatedTestDerivative
        (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B)
        (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ
        (fun x => -s * Real.exp (-s * x)) t z =
    ∑ i, finiteChaosMatrixLaplaceScore A B a γ s t i z *
        (γ * (finiteChaosLinearImageVector A z.1 i / (2 * Real.sqrt t) -
          finiteChaosLinearImageVector B z.2 i / (2 * Real.sqrt (1 - t))) -
          γ ^ 2 / 2 * (finiteChaosMatrixRowVariance A i -
            finiteChaosMatrixRowVariance B i)) := by
  classical
  let V := finiteChaosMatrixTwoBlockField A B t
  let v := finiteChaosMatrixTwoBlockVariance A B t
  have hmass : kahaneInterpolatedMass
      (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B)
      (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ t z =
      finiteChaosVectorMass a v γ (V z.1 z.2) := by
    simp only [kahaneInterpolatedMass, finiteChaosVectorMass, finiteChaosVectorWeight,
      V, v, finiteChaosMatrixTwoBlockField, finiteChaosMatrixTwoBlockVariance,
      finiteChaosMatrixRowVariance, finiteChaosMatrixRowCovariance,
      finiteChaosLinearImageVector]
  rw [kahaneInterpolatedTestDerivative, hmass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [finiteChaosMatrixLaplaceScore, V, v, finiteChaosMatrixTwoBlockField,
    finiteChaosMatrixTwoBlockVariance, finiteChaosMatrixRowVariance,
    finiteChaosMatrixRowCovariance, finiteChaosLinearImageVector, finiteChaosVectorWeight]
  ring

/-- The finite Laplace expectation along two standard-Gaussian linear images. -/
noncomputable def finiteChaosMatrixLaplaceInterpolationExpectation {n : ℕ}
    (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (a : Fin (n + 1) → ℝ) (γ s : ℝ) : ℝ → ℝ := fun t =>
  ∫ z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ),
    Real.exp (-s * kahaneInterpolatedMass
      (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B)
      (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ t z)
    ∂((standardGaussianFinMeasure n).prod (standardGaussianFinMeasure n))

/-- The abstract dominated-differentiation contract specialized to a finite Gaussian Laplace
interpolation. The domination hypotheses are the local hypotheses required by
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`. -/
theorem finiteChaosMatrixLaplaceInterpolationExpectation_hasDerivAt
    {n : ℕ} (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (a : Fin (n + 1) → ℝ) (γ s t ε : ℝ)
    (hε : 0 < ε) (hεleft : ε ≤ t) (hεright : ε ≤ 1 - t)
    (hMeas : ∀ᶠ r in 𝓝 t, AEStronglyMeasurable
      (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) =>
        Real.exp (-s * kahaneInterpolatedMass
          (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B)
          (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ r z))
      ((standardGaussianFinMeasure n).prod (standardGaussianFinMeasure n)))
    (hInt : Integrable
      (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) =>
        Real.exp (-s * kahaneInterpolatedMass
          (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B)
          (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ t z))
      ((standardGaussianFinMeasure n).prod (standardGaussianFinMeasure n)))
    (hDMeas : AEStronglyMeasurable
      (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) =>
        kahaneInterpolatedTestDerivative
          (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B)
          (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ
          (fun x => -s * Real.exp (-s * x)) t z)
      ((standardGaussianFinMeasure n).prod (standardGaussianFinMeasure n)))
    (b : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) → ℝ)
    (hb : Integrable b
      ((standardGaussianFinMeasure n).prod (standardGaussianFinMeasure n)))
    (hbound : ∀ᵐ z ∂((standardGaussianFinMeasure n).prod (standardGaussianFinMeasure n)),
      ∀ r ∈ Metric.ball t ε,
        ‖kahaneInterpolatedTestDerivative
          (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B)
          (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ
          (fun x => -s * Real.exp (-s * x)) r z‖ ≤ b z) :
    HasDerivAt (finiteChaosMatrixLaplaceInterpolationExpectation A B a γ s)
      (∫ z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ),
        kahaneInterpolatedTestDerivative
          (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B)
          (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ
          (fun x => -s * Real.exp (-s * x)) t z
        ∂((standardGaussianFinMeasure n).prod (standardGaussianFinMeasure n))) t := by
  let X := finiteChaosLinearImageVector A
  let Y := finiteChaosLinearImageVector B
  let vX := finiteChaosMatrixRowVariance A
  let vY := finiteChaosMatrixRowVariance B
  let F : ℝ → ℝ := fun x => Real.exp (-s * x)
  let F' : ℝ → ℝ := fun x => -s * Real.exp (-s * x)
  have hF (x : ℝ) : HasDerivAt F (F' x) x := by
    change HasDerivAt (fun u => Real.exp (-s * u))
      (-s * Real.exp (-s * x)) x
    have hlin : HasDerivAt (fun u : ℝ => -s * u) (-s) x := by
      simpa using (hasDerivAt_id x).const_mul (-s)
    have hexp := (Real.hasDerivAt_exp (-s * x)).comp x hlin
    convert hexp using 1
    · rfl
    · ring
  have h := kahaneInterpolatedExpectation_hasDerivAt
    (standardGaussianFinMeasure n) (standardGaussianFinMeasure n)
    X Y vX vY a γ t ε F F' hF hε hεleft hεright
    (by simpa [X, Y, vX, vY, F] using hMeas)
    (by simpa [X, Y, vX, vY, F] using hInt)
    (by simpa [X, Y, vX, vY, F'] using hDMeas)
    b hb (by simpa [X, Y, vX, vY, F'] using hbound)
  change HasDerivAt
    (fun r => ∫ z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ),
      Real.exp (-s * kahaneInterpolatedMass
        (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B)
        (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ r z)
      ∂((standardGaussianFinMeasure n).prod (standardGaussianFinMeasure n)))
    (∫ z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ),
      kahaneInterpolatedTestDerivative
        (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B)
        (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ
        (fun x => -s * Real.exp (-s * x)) t z
      ∂((standardGaussianFinMeasure n).prod (standardGaussianFinMeasure n))) t
  exact h

/-- The product-space Laplace derivative after both block IBP substitutions. Entrywise covariance
order makes it nonpositive; the diagonal score term cancels the derivative of the Wick variance. -/
theorem finiteChaosMatrixLaplaceInterpolation_derivative_integral_nonpos
    {n : ℕ} (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (a : Fin (n + 1) → ℝ) (γ s t : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hs : 0 ≤ s) (ht : 0 < t) (ht1 : t < 1)
    (hcov : ∀ i j, finiteChaosMatrixRowCovariance A i j ≤
      finiteChaosMatrixRowCovariance B i j) :
    ∫ z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ),
      kahaneInterpolatedTestDerivative
        (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B)
        (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ
        (fun x => -s * Real.exp (-s * x)) t z
      ∂((standardGaussianFinMeasure n).prod (standardGaussianFinMeasure n)) ≤ 0 := by
  classical
  let μ := standardGaussianFinMeasure n
  let ν := μ.prod μ
  let v := finiteChaosMatrixTwoBlockVariance A B t
  let V := finiteChaosMatrixTwoBlockField A B t
  let cY : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ := fun y i =>
    Real.sqrt (1 - t) * finiteChaosLinearImageVector B y i
  let cX : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ := fun x i =>
    Real.sqrt t * finiteChaosLinearImageVector A x i
  let S (i : Fin (n + 1))
      (z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) :=
    finiteChaosMatrixLaplaceScore A B a γ s t i z
  let K (i j : Fin (n + 1))
      (z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) :=
    finiteChaosMatrixLaplaceHessianFactor A B a γ s t i j z
  let G (i j : Fin (n + 1))
      (z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) :=
    finiteChaosMatrixLaplaceScoreDerivative A B a γ s t i j z
  have hfieldX (z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) :
      finiteChaosTwoBlockField A cY t z.1 z.2 = V z.1 z.2 := by
    funext i
    simp [finiteChaosTwoBlockField, V, cY, finiteChaosMatrixTwoBlockField,
      finiteChaosLinearImageVector]
  have hfieldY (z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) :
      finiteChaosTwoBlockField B cX (1 - t) z.2 z.1 = V z.1 z.2 := by
    funext i
    simp [finiteChaosTwoBlockField, V, cX, finiteChaosMatrixTwoBlockField,
      finiteChaosLinearImageVector]
    ring
  have hfieldX' (z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) :
      finiteChaosTwoBlockField A cY t z.1 z.2 =
        finiteChaosMatrixTwoBlockField A B t z.1 z.2 := by
    simpa [V] using hfieldX z
  have hfieldY' (z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) :
      finiteChaosTwoBlockField B cX (1 - t) z.2 z.1 =
        finiteChaosMatrixTwoBlockField A B t z.1 z.2 := by
    simpa [V] using hfieldY z
  have hcY : Measurable cY := by
    dsimp [cY]
    fun_prop [finiteChaosLinearImageVector]
  have hcX : Measurable cX := by
    dsimp [cX]
    fun_prop [finiteChaosLinearImageVector]
  have hscoreX (i : Fin (n + 1)) (z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) :
      finiteChaosTwoBlockLaplaceScore A cY a v γ s t i z.1 z.2 = S i z := by
    dsimp [finiteChaosTwoBlockLaplaceScore, finiteChaosMatrixLaplaceScore,
      S, v]
    rw [hfieldX' z]
  have hscoreY (i : Fin (n + 1)) (z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) :
      finiteChaosTwoBlockLaplaceScore B cX a v γ s (1 - t) i z.2 z.1 = S i z := by
    dsimp [finiteChaosTwoBlockLaplaceScore, finiteChaosMatrixLaplaceScore,
      S, v]
    rw [hfieldY' z]
  have hderivX (i j : Fin (n + 1))
      (z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) :
      finiteChaosTwoBlockLaplaceScoreDerivative A cY a v γ s t i j z.1 z.2 =
        G i j z := by
    dsimp [finiteChaosTwoBlockLaplaceScoreDerivative,
      finiteChaosMatrixLaplaceScoreDerivative, finiteChaosTwoBlockLaplaceScore,
      finiteChaosMatrixLaplaceScore, finiteChaosMatrixLaplaceHessianFactor,
      S, K, G, v]
    rw [hfieldX' z]
    ring
  have hderivY (i j : Fin (n + 1))
      (z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) :
      finiteChaosTwoBlockLaplaceScoreDerivative B cX a v γ s (1 - t) i j z.2 z.1 =
        G i j z := by
    dsimp [finiteChaosTwoBlockLaplaceScoreDerivative,
      finiteChaosMatrixLaplaceScoreDerivative, finiteChaosTwoBlockLaplaceScore,
      finiteChaosMatrixLaplaceScore, finiteChaosMatrixLaplaceHessianFactor,
      S, K, G, v]
    rw [hfieldY' z]
    ring
  have hX (i : Fin (n + 1)) :
      ∫ z, (∑ k, A i k * z.1 k) * S i z ∂ν =
        Real.sqrt t * ∑ j, finiteChaosMatrixRowCovariance A i j *
          ∫ z, G i j z ∂ν := by
    simpa only [hscoreX, hderivX, finiteChaosMatrixRowCovariance, μ, ν] using
      (finiteChaos_laplace_X_block_ibp_on_product_first_of_measurable_shift
        A a v cY hcY γ s t ha hs ht i)
  have hY (i : Fin (n + 1)) :
      ∫ z, (∑ k, B i k * z.2 k) * S i z ∂ν =
        Real.sqrt (1 - t) * ∑ j, finiteChaosMatrixRowCovariance B i j *
          ∫ z, G i j z ∂ν := by
    simpa only [hscoreY, hderivY, finiteChaosMatrixRowCovariance, μ, ν] using
      (finiteChaos_laplace_X_block_ibp_on_product_of_measurable_shift
        B a v cX hcX γ s (1 - t) ha hs (by linarith) i)
  have hSmeas (i : Fin (n + 1)) : Measurable (S i) := by
    dsimp [S, finiteChaosMatrixLaplaceScore]
    fun_prop [finiteChaosMatrixTwoBlockField, finiteChaosMatrixTwoBlockVariance,
      finiteChaosMatrixRowVariance, finiteChaosMatrixRowCovariance,
      finiteChaosLinearImageVector, finiteChaosVectorWeight, finiteChaosVectorMass]
  have hKmeas (i j : Fin (n + 1)) : Measurable (K i j) := by
    dsimp [K, finiteChaosMatrixLaplaceHessianFactor]
    fun_prop [finiteChaosMatrixTwoBlockField, finiteChaosMatrixTwoBlockVariance,
      finiteChaosMatrixRowVariance, finiteChaosMatrixRowCovariance,
      finiteChaosLinearImageVector, finiteChaosVectorWeight, finiteChaosVectorMass]
  have hGmeas (i j : Fin (n + 1)) : Measurable (G i j) := by
    change Measurable (fun z => γ * (if i = j then S i z else 0) + γ * K i j z)
    by_cases hij : i = j
    · simp [hij]
      fun_prop
    · simp [hij]
      fun_prop
  have hSbound (i : Fin (n + 1)) (z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) :
      ‖S i z‖ ≤ 1 := by
    simpa [S, finiteChaosMatrixLaplaceScore] using
      finiteChaos_laplace_first_weight_bound a v γ s ha hs (V z.1 z.2) i
  have hKbound (i j : Fin (n + 1))
      (z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) : ‖K i j z‖ ≤ 4 := by
    simpa [K, finiteChaosMatrixLaplaceHessianFactor] using
      finiteChaos_laplace_second_weight_bound a v γ s ha hs (V z.1 z.2) i j
  have hGbound (i j : Fin (n + 1))
      (z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) : ‖G i j z‖ ≤ 5 * |γ| := by
    have h := finiteChaos_laplace_score_derivative_norm_le a
      (finiteChaosMatrixTwoBlockVariance A B t) γ s ha hs
      (finiteChaosMatrixTwoBlockField A B t z.1 z.2) i j
    convert h using 1
    dsimp [G, finiteChaosMatrixLaplaceScoreDerivative,
      finiteChaosMatrixLaplaceScore, finiteChaosMatrixLaplaceHessianFactor,
      finiteChaosMatrixTwoBlockVariance, finiteChaosMatrixTwoBlockField]
    ring_nf
  have hSInt (i : Fin (n + 1)) : Integrable (S i) ν :=
    Integrable.of_bound (hSmeas i).aestronglyMeasurable 1
      (ae_of_all ν (hSbound i))
  have hKInt (i j : Fin (n + 1)) : Integrable (K i j) ν :=
    Integrable.of_bound (hKmeas i j).aestronglyMeasurable 4
      (ae_of_all ν (hKbound i j))
  have hGInt (i j : Fin (n + 1)) : Integrable (G i j) ν :=
    Integrable.of_bound (hGmeas i j).aestronglyMeasurable (5 * |γ|)
      (ae_of_all ν (hGbound i j))
  have hcoord (k : Fin (n + 1)) : Integrable (fun x : Fin (n + 1) → ℝ => x k) μ := by
    simpa [μ, standardGaussianFinMeasure] using
      (integrable_eval IsGaussian.integrable_id :
        Integrable (fun x : Fin (n + 1) → ℝ => x k)
          (Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1))
  have hArow (i : Fin (n + 1)) : Integrable
      (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) =>
        ∑ k, A i k * z.1 k) ν := by
    have hcoord' (k : Fin (n + 1)) : Integrable
        (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) => z.1 k) ν := by
      exact measurePreserving_fst.integrable_comp_of_integrable (hcoord k)
    exact integrable_finsetSum Finset.univ (fun k hk => (hcoord' k).const_mul _)
  have hBrow (i : Fin (n + 1)) : Integrable
      (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) =>
        ∑ k, B i k * z.2 k) ν := by
    have hcoord' (k : Fin (n + 1)) : Integrable
        (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) => z.2 k) ν := by
      exact measurePreserving_snd.integrable_comp_of_integrable (hcoord k)
    exact integrable_finsetSum Finset.univ (fun k hk => (hcoord' k).const_mul _)
  have hAScore (i : Fin (n + 1)) : Integrable
      (fun z => (∑ k, A i k * z.1 k) * S i z) ν := by
    apply (hArow i).norm.mono'
    · exact (hArow i).aestronglyMeasurable.mul (hSmeas i).aestronglyMeasurable
    · filter_upwards [] with z
      rw [norm_mul]
      calc
        ‖∑ k, A i k * z.1 k‖ * ‖S i z‖ ≤ ‖∑ k, A i k * z.1 k‖ * 1 :=
          mul_le_mul_of_nonneg_left (hSbound i z) (norm_nonneg _)
        _ = ‖∑ k, A i k * z.1 k‖ := by ring
  have hBScore (i : Fin (n + 1)) : Integrable
      (fun z => (∑ k, B i k * z.2 k) * S i z) ν := by
    apply (hBrow i).norm.mono'
    · exact (hBrow i).aestronglyMeasurable.mul (hSmeas i).aestronglyMeasurable
    · filter_upwards [] with z
      rw [norm_mul]
      calc
        ‖∑ k, B i k * z.2 k‖ * ‖S i z‖ ≤ ‖∑ k, B i k * z.2 k‖ * 1 :=
          mul_le_mul_of_nonneg_left (hSbound i z) (norm_nonneg _)
        _ = ‖∑ k, B i k * z.2 k‖ := by ring
  let AX (i : Fin (n + 1)) : ℝ := γ * ∫ z, (∑ k, A i k * z.1 k) * S i z ∂ν
  let BY (i : Fin (n + 1)) : ℝ := γ * ∫ z, (∑ k, B i k * z.2 k) * S i z ∂ν
  let H (i j : Fin (n + 1)) : ℝ := γ * ∫ z, G i j z ∂ν
  let Kbar (i j : Fin (n + 1)) : ℝ := ∫ z, K i j z ∂ν
  let Dbar (i : Fin (n + 1)) : ℝ := ∫ z, S i z ∂ν
  have hXibp : ∀ i, AX i = Real.sqrt t * ∑ j,
      finiteChaosMatrixRowCovariance A i j * H i j := by
    intro i
    dsimp [AX, H]
    rw [hX i]
    calc
      γ * (Real.sqrt t * ∑ j, finiteChaosMatrixRowCovariance A i j *
          ∫ z, G i j z ∂ν) =
          ∑ j, γ * (Real.sqrt t * (finiteChaosMatrixRowCovariance A i j *
            ∫ z, G i j z ∂ν)) := by
              rw [show γ * (Real.sqrt t * ∑ j, finiteChaosMatrixRowCovariance A i j *
                ∫ z, G i j z ∂ν) = (γ * Real.sqrt t) *
                ∑ j, finiteChaosMatrixRowCovariance A i j * ∫ z, G i j z ∂ν by ring,
                Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j hj
              ring
      _ = ∑ j, Real.sqrt t * (finiteChaosMatrixRowCovariance A i j *
            (γ * ∫ z, G i j z ∂ν)) := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
      _ = Real.sqrt t * ∑ j, finiteChaosMatrixRowCovariance A i j *
            (γ * ∫ z, G i j z ∂ν) := by rw [Finset.mul_sum]
  have hYibp : ∀ i, BY i = Real.sqrt (1 - t) * ∑ j,
      finiteChaosMatrixRowCovariance B i j * H i j := by
    intro i
    dsimp [BY, H]
    rw [hY i]
    calc
      γ * (Real.sqrt (1 - t) * ∑ j, finiteChaosMatrixRowCovariance B i j *
          ∫ z, G i j z ∂ν) =
          ∑ j, γ * (Real.sqrt (1 - t) * (finiteChaosMatrixRowCovariance B i j *
            ∫ z, G i j z ∂ν)) := by
              rw [show γ * (Real.sqrt (1 - t) * ∑ j, finiteChaosMatrixRowCovariance B i j *
                ∫ z, G i j z ∂ν) = (γ * Real.sqrt (1 - t)) *
                ∑ j, finiteChaosMatrixRowCovariance B i j * ∫ z, G i j z ∂ν by ring,
                Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j hj
              ring
      _ = ∑ j, Real.sqrt (1 - t) * (finiteChaosMatrixRowCovariance B i j *
            (γ * ∫ z, G i j z ∂ν)) := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
      _ = Real.sqrt (1 - t) * ∑ j, finiteChaosMatrixRowCovariance B i j *
            (γ * ∫ z, G i j z ∂ν) := by rw [Finset.mul_sum]
  have hHessian : ∀ i j, H i j = γ ^ 2 * Kbar i j +
      if i = j then γ ^ 2 * Dbar i else 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      have hpoint (z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) :
          γ * G i i z = γ ^ 2 * S i z + γ ^ 2 * K i i z := by
        simp [G, finiteChaosMatrixLaplaceScoreDerivative, K, S,
          finiteChaosMatrixLaplaceScore]
        ring
      dsimp [H, Kbar, Dbar]
      calc
        γ * ∫ z, G i i z ∂ν = ∫ z, γ * G i i z ∂ν := by
          rw [integral_const_mul]
        _ = ∫ z, (γ ^ 2 * S i z + γ ^ 2 * K i i z) ∂ν := by
          apply integral_congr_ae
          exact ae_of_all ν hpoint
        _ = γ ^ 2 * ∫ z, S i z ∂ν + γ ^ 2 * ∫ z, K i i z ∂ν := by
          rw [integral_add (hSInt i |>.const_mul _) (hKInt i i |>.const_mul _),
            integral_const_mul, integral_const_mul]
      simp
      ring_nf
    · have hpoint (z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) :
          γ * G i j z = γ ^ 2 * K i j z := by
        simp [G, finiteChaosMatrixLaplaceScoreDerivative, K,
          finiteChaosMatrixLaplaceHessianFactor, finiteChaosMatrixLaplaceScore, hij]
        ring
      dsimp [H, Kbar]
      calc
        γ * ∫ z, G i j z ∂ν = ∫ z, γ * G i j z ∂ν := by
          rw [integral_const_mul]
        _ = ∫ z, γ ^ 2 * K i j z ∂ν := by
          apply integral_congr_ae
          exact ae_of_all ν hpoint
        _ = γ ^ 2 * ∫ z, K i j z ∂ν := integral_const_mul _ _
      simp [hij]
  have hKnonneg : ∀ i j, 0 ≤ Kbar i j := by
    intro i j
    apply integral_nonneg
    intro z
    dsimp [K, finiteChaosMatrixLaplaceHessianFactor]
    have hwi : 0 ≤ finiteChaosVectorWeight a
        (finiteChaosMatrixTwoBlockVariance A B t) γ
        (finiteChaosMatrixTwoBlockField A B t z.1 z.2) i := by
      unfold finiteChaosVectorWeight
      exact mul_nonneg (ha i) (Real.exp_nonneg _)
    have hwj : 0 ≤ finiteChaosVectorWeight a
        (finiteChaosMatrixTwoBlockVariance A B t) γ
        (finiteChaosMatrixTwoBlockField A B t z.1 z.2) j := by
      unfold finiteChaosVectorWeight
      exact mul_nonneg (ha j) (Real.exp_nonneg _)
    exact mul_nonneg (mul_nonneg hwi hwj)
      (mul_nonneg (sq_nonneg s) (Real.exp_nonneg _))
  have hderivIntegral :
      ∫ z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ),
        kahaneInterpolatedTestDerivative
          (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B)
          (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ
          (fun x => -s * Real.exp (-s * x)) t z ∂ν =
        (∑ i, AX i) / (2 * Real.sqrt t) -
          (∑ i, BY i) / (2 * Real.sqrt (1 - t)) -
          γ ^ 2 / 2 * ∑ i, (finiteChaosMatrixRowVariance A i -
            finiteChaosMatrixRowVariance B i) * Dbar i := by
    let T (i : Fin (n + 1)) (z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) :=
      γ / (2 * Real.sqrt t) * ((∑ k, A i k * z.1 k) * S i z) -
        γ / (2 * Real.sqrt (1 - t)) * ((∑ k, B i k * z.2 k) * S i z) -
        γ ^ 2 / 2 * (finiteChaosMatrixRowVariance A i -
          finiteChaosMatrixRowVariance B i) * S i z
    have hpoint (z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ)) :
        kahaneInterpolatedTestDerivative
          (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B)
          (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ
          (fun x => -s * Real.exp (-s * x)) t z = ∑ i, T i z := by
      rw [kahaneInterpolatedLaplaceTestDerivative_eq_score_sum]
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [T, S, finiteChaosLinearImageVector]
      ring_nf
    have hTint (i : Fin (n + 1)) : Integrable (T i) ν := by
      dsimp [T]
      exact (((hAScore i).const_mul _).sub ((hBScore i).const_mul _)).sub
        ((hSInt i).const_mul _)
    calc
      _ = ∫ z, ∑ i, T i z ∂ν := by
        apply integral_congr_ae
        exact ae_of_all ν hpoint
      _ = ∑ i, ∫ z, T i z ∂ν := by
        simpa using
          (integral_finsetSum Finset.univ (fun i hi => hTint i))
      _ = ∑ i, (AX i / (2 * Real.sqrt t) - BY i / (2 * Real.sqrt (1 - t)) -
          γ ^ 2 / 2 * (finiteChaosMatrixRowVariance A i -
            finiteChaosMatrixRowVariance B i) * Dbar i) := by
        apply Finset.sum_congr rfl
        intro i hi
        have h1 := (hAScore i).const_mul (γ / (2 * Real.sqrt t))
        have h2 := (hBScore i).const_mul (γ / (2 * Real.sqrt (1 - t)))
        have h3 := (hSInt i).const_mul
          (γ ^ 2 / 2 * (finiteChaosMatrixRowVariance A i -
            finiteChaosMatrixRowVariance B i))
        have h12 := h1.sub h2
        dsimp [T, AX, BY, Dbar]
        calc
          ∫ z, ((γ / (2 * Real.sqrt t) *
              ((∑ k, A i k * z.1 k) * S i z)) -
            (γ / (2 * Real.sqrt (1 - t)) *
              ((∑ k, B i k * z.2 k) * S i z))) -
              (γ ^ 2 / 2 * (finiteChaosMatrixRowVariance A i -
                finiteChaosMatrixRowVariance B i) * S i z) ∂ν =
            (∫ z, γ / (2 * Real.sqrt t) *
                ((∑ k, A i k * z.1 k) * S i z) ∂ν) -
              (∫ z, γ / (2 * Real.sqrt (1 - t)) *
                ((∑ k, B i k * z.2 k) * S i z) ∂ν) -
              ∫ z, γ ^ 2 / 2 * (finiteChaosMatrixRowVariance A i -
                finiteChaosMatrixRowVariance B i) * S i z ∂ν := by
                  calc
                    ∫ z, (((γ / (2 * Real.sqrt t) *
                        ((∑ k, A i k * z.1 k) * S i z)) -
                      (γ / (2 * Real.sqrt (1 - t)) *
                        ((∑ k, B i k * z.2 k) * S i z))) -
                      (γ ^ 2 / 2 * (finiteChaosMatrixRowVariance A i -
                        finiteChaosMatrixRowVariance B i) * S i z)) ∂ν =
                        (∫ z, (γ / (2 * Real.sqrt t) *
                          ((∑ k, A i k * z.1 k) * S i z)) -
                          (γ / (2 * Real.sqrt (1 - t)) *
                            ((∑ k, B i k * z.2 k) * S i z)) ∂ν) -
                          ∫ z, γ ^ 2 / 2 * (finiteChaosMatrixRowVariance A i -
                            finiteChaosMatrixRowVariance B i) * S i z ∂ν := by
                              exact integral_sub (h1.sub h2) h3
                    _ = _ := by rw [integral_sub h1 h2]
          _ = (γ * ∫ z, (∑ k, A i k * z.1 k) * S i z ∂ν) /
                (2 * Real.sqrt t) -
              (γ * ∫ z, (∑ k, B i k * z.2 k) * S i z ∂ν) /
                (2 * Real.sqrt (1 - t)) -
              γ ^ 2 / 2 * (finiteChaosMatrixRowVariance A i -
                finiteChaosMatrixRowVariance B i) * ∫ z, S i z ∂ν := by
                  rw [integral_const_mul, integral_const_mul, integral_const_mul]
                  ring
      _ = (∑ i, AX i) / (2 * Real.sqrt t) -
          (∑ i, BY i) / (2 * Real.sqrt (1 - t)) -
          γ ^ 2 / 2 * (∑ i, (finiteChaosMatrixRowVariance A i -
            finiteChaosMatrixRowVariance B i) * Dbar i) := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          ← Finset.sum_div, ← Finset.sum_div]
        congr 1
        calc
          ∑ i, γ ^ 2 / 2 * (finiteChaosMatrixRowVariance A i -
              finiteChaosMatrixRowVariance B i) * Dbar i =
            ∑ i, (γ ^ 2 / 2) * ((finiteChaosMatrixRowVariance A i -
              finiteChaosMatrixRowVariance B i) * Dbar i) := by
                apply Finset.sum_congr rfl
                intro i hi
                ring
          _ = γ ^ 2 / 2 * ∑ i, (finiteChaosMatrixRowVariance A i -
              finiteChaosMatrixRowVariance B i) * Dbar i := by
                exact (Finset.mul_sum Finset.univ _ _).symm
  have hsign := kahaneInterpolation_derivative_nonpos_of_covariance_order
    γ t (finiteChaosMatrixRowCovariance A) (finiteChaosMatrixRowCovariance B)
    AX BY H Kbar Dbar ht ht1 hcov (fun i j => hKnonneg i j)
    hXibp hYibp hHessian
  rw [hderivIntegral]
  exact hsign

/-- Under the local dominated-differentiation contract, the finite Laplace expectation has a
nonpositive derivative whenever the two covariance matrices are entrywise ordered. -/
theorem finiteChaosMatrixLaplaceInterpolationExpectation_deriv_nonpos
    {n : ℕ} (A B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (a : Fin (n + 1) → ℝ) (γ s t ε : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hs : 0 ≤ s) (ht : 0 < t) (ht1 : t < 1)
    (hcov : ∀ i j, finiteChaosMatrixRowCovariance A i j ≤
      finiteChaosMatrixRowCovariance B i j)
    (hε : 0 < ε) (hεleft : ε ≤ t) (hεright : ε ≤ 1 - t)
    (hMeas : ∀ᶠ r in 𝓝 t, AEStronglyMeasurable
      (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) =>
        Real.exp (-s * kahaneInterpolatedMass
          (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B)
          (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ r z))
      ((standardGaussianFinMeasure n).prod (standardGaussianFinMeasure n)))
    (hInt : Integrable
      (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) =>
        Real.exp (-s * kahaneInterpolatedMass
          (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B)
          (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ t z))
      ((standardGaussianFinMeasure n).prod (standardGaussianFinMeasure n)))
    (hDMeas : AEStronglyMeasurable
      (fun z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) =>
        kahaneInterpolatedTestDerivative
          (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B)
          (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ
          (fun x => -s * Real.exp (-s * x)) t z)
      ((standardGaussianFinMeasure n).prod (standardGaussianFinMeasure n)))
    (b : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ) → ℝ)
    (hb : Integrable b
      ((standardGaussianFinMeasure n).prod (standardGaussianFinMeasure n)))
    (hbound : ∀ᵐ z ∂((standardGaussianFinMeasure n).prod (standardGaussianFinMeasure n)),
      ∀ r ∈ Metric.ball t ε,
        ‖kahaneInterpolatedTestDerivative
          (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B)
          (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ
          (fun x => -s * Real.exp (-s * x)) r z‖ ≤ b z) :
    HasDerivAt (finiteChaosMatrixLaplaceInterpolationExpectation A B a γ s)
      (∫ z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ),
        kahaneInterpolatedTestDerivative
          (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B)
          (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ
          (fun x => -s * Real.exp (-s * x)) t z
        ∂((standardGaussianFinMeasure n).prod (standardGaussianFinMeasure n))) t ∧
      (∫ z : (Fin (n + 1) → ℝ) × (Fin (n + 1) → ℝ),
        kahaneInterpolatedTestDerivative
          (finiteChaosLinearImageVector A) (finiteChaosLinearImageVector B)
          (finiteChaosMatrixRowVariance A) (finiteChaosMatrixRowVariance B) a γ
          (fun x => -s * Real.exp (-s * x)) t z
        ∂((standardGaussianFinMeasure n).prod (standardGaussianFinMeasure n))) ≤ 0 := by
  constructor
  · exact finiteChaosMatrixLaplaceInterpolationExpectation_hasDerivAt A B a γ s t ε
      hε hεleft hεright hMeas hInt hDMeas b hb hbound
  · exact finiteChaosMatrixLaplaceInterpolation_derivative_integral_nonpos
      A B a γ s t ha hs ht ht1 hcov


end DOZZ.Proofs

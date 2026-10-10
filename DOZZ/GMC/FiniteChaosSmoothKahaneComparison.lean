/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteChaosTestGrowth
public import DOZZ.GMC.FiniteChaosLaplaceBounds
public import DOZZ.GMC.FiniteChaosSmoothKahane
public import DOZZ.GMC.FiniteChaosInterpolationExpectation
public import DOZZ.GMC.FiniteGaussianInterpolationIdentity
public import DOZZ.GMC.FiniteGaussianProduct
public import DOZZ.GMC.FiniteGaussianIntegrationByPartsGrowth
public import DOZZ.GMC.FiniteGaussianTilt

/-! Smooth-test Kahane interpolation for finite Gaussian chaos sums. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions Topology

namespace DOZZ.Proofs

/-- Covariance of two coordinates pulled back from the first factor of a product measure. -/
theorem gaussianCovariance_product_fst
    {ΩX ΩY ι : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [Fintype ι]
    (PX : Measure ΩX) (PY : Measure ΩY) (X : ΩX → ι → ℝ)
    (hX : IsCenteredJointlyGaussian PX X) (hPY : IsProbabilityMeasure PY)
    (i j : ι) :
    DOZZ.gaussianCovariance (PX.prod PY)
        (fun ω => X ω.1 i) (fun ω => X ω.1 j) =
      DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) := by
  classical
  let : IsProbabilityMeasure PX := hX.1
  let : IsProbabilityMeasure PY := hPY
  let μ : Measure (ΩX × ΩY) := PX.prod PY
  let hfst : MeasurePreserving Prod.fst μ PX := measurePreserving_fst
  have hiMem : MemLp (fun ω => X ω i) 2 PX := by
    obtain ⟨hm, _⟩ := hX.2.2 (Pi.single i 1)
    simpa [Pi.single_apply] using hm
  have hjMem : MemLp (fun ω => X ω j) 2 PX := by
    obtain ⟨hm, _⟩ := hX.2.2 (Pi.single j 1)
    simpa [Pi.single_apply] using hm
  have hHolder : ENNReal.HolderTriple 2 2 1 := ⟨by
    simpa using ENNReal.inv_two_add_inv_two⟩
  have hprodMem := hiMem.mul hjMem (hpqr := hHolder)
  have hprodInt : Integrable (fun ω => X ω i * X ω j) PX :=
    memLp_one_iff_integrable.mp (by convert hprodMem using 1)
  have hprodMap : Integrable (fun x => X x i * X x j) (μ.map Prod.fst) := by
    rw [hfst.map_eq]
    exact hprodInt
  have hmap := integral_map hfst.aemeasurable hprodMap.aestronglyMeasurable
  rw [hfst.map_eq] at hmap
  simpa [DOZZ.gaussianCovariance] using hmap.symm

/-- Covariance of two coordinates pulled back from the second factor of a product measure. -/
theorem gaussianCovariance_product_snd
    {ΩX ΩY ι : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [Fintype ι]
    (PX : Measure ΩX) (PY : Measure ΩY) (Y : ΩY → ι → ℝ)
    (hPX : IsProbabilityMeasure PX) (hY : IsCenteredJointlyGaussian PY Y)
    (i j : ι) :
    DOZZ.gaussianCovariance (PX.prod PY)
        (fun ω => Y ω.2 i) (fun ω => Y ω.2 j) =
      DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j) := by
  classical
  let : IsProbabilityMeasure PX := hPX
  let : IsProbabilityMeasure PY := hY.1
  let μ : Measure (ΩX × ΩY) := PX.prod PY
  let hsnd : MeasurePreserving Prod.snd μ PY := measurePreserving_snd
  have hiMem : MemLp (fun ω => Y ω i) 2 PY := by
    obtain ⟨hm, _⟩ := hY.2.2 (Pi.single i 1)
    simpa [Pi.single_apply] using hm
  have hjMem : MemLp (fun ω => Y ω j) 2 PY := by
    obtain ⟨hm, _⟩ := hY.2.2 (Pi.single j 1)
    simpa [Pi.single_apply] using hm
  have hHolder : ENNReal.HolderTriple 2 2 1 := ⟨by
    simpa using ENNReal.inv_two_add_inv_two⟩
  have hprodMem := hiMem.mul hjMem (hpqr := hHolder)
  have hprodInt : Integrable (fun ω => Y ω i * Y ω j) PY :=
    memLp_one_iff_integrable.mp (by convert hprodMem using 1)
  have hprodMap : Integrable (fun y => Y y i * Y y j) (μ.map Prod.snd) := by
    rw [hsnd.map_eq]
    exact hprodInt
  have hmap := integral_map hsnd.aemeasurable hprodMap.aestronglyMeasurable
  rw [hsnd.map_eq] at hmap
  simpa [DOZZ.gaussianCovariance] using hmap.symm

/-- Cross covariance of independent coordinates on a product space is zero for centered
Gaussian families. -/
theorem gaussianCovariance_product_cross_eq_zero
    {ΩX ΩY ι : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    [Fintype ι] [DecidableEq ι]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (hX : IsCenteredJointlyGaussian PX X) (hY : IsCenteredJointlyGaussian PY Y)
    (i j : ι) :
    DOZZ.gaussianCovariance (PX.prod PY)
        (fun ω => X ω.1 i) (fun ω => Y ω.2 j) = 0 := by
  let : IsProbabilityMeasure PX := hX.1
  let : IsProbabilityMeasure PY := hY.1
  rw [DOZZ.gaussianCovariance]
  have hprod : (∫ ω : ΩX × ΩY, X ω.1 i * Y ω.2 j ∂PX.prod PY) =
      (∫ x, X x i ∂PX) * ∫ y, Y y j ∂PY := by
    exact integral_prod_mul (fun x => X x i) (fun y => Y y j)
  rw [hprod, coord_mean PX X hX i, coord_mean PY Y hY j]
  simp

/-- The covariance of the concatenation of independent centered Gaussian vectors on a product
space is block diagonal. -/
theorem gaussianCovariance_product_concat
    {ΩX ΩY ι : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    [Fintype ι] [DecidableEq ι]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (hX : IsCenteredJointlyGaussian PX X) (hY : IsCenteredJointlyGaussian PY Y)
    (i j : Sum ι ι) :
    DOZZ.gaussianCovariance (PX.prod PY)
        (fun ω => match i with | Sum.inl k => X ω.1 k | Sum.inr k => Y ω.2 k)
        (fun ω => match j with | Sum.inl k => X ω.1 k | Sum.inr k => Y ω.2 k) =
      match i, j with
      | Sum.inl k, Sum.inl l =>
          DOZZ.gaussianCovariance PX (fun ω => X ω k) (fun ω => X ω l)
      | Sum.inr k, Sum.inr l =>
          DOZZ.gaussianCovariance PY (fun ω => Y ω k) (fun ω => Y ω l)
      | _, _ => 0 := by
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          exact gaussianCovariance_product_fst PX PY X hX hY.1 i j
      | inr j =>
          exact gaussianCovariance_product_cross_eq_zero PX PY X Y hX hY i j
  | inr i =>
      cases j with
      | inl j =>
          simpa [DOZZ.gaussianCovariance, mul_comm] using
          (gaussianCovariance_product_cross_eq_zero PX PY X Y hX hY j i)
      | inr j =>
          exact gaussianCovariance_product_snd PX PY Y hX.1 hY i j

/-- Gaussian integration by parts for a smooth Kahane score on the concatenated independent
blocks. This is the reusable Stein step in the finite interpolation argument. -/
theorem kahaneSumVectorScore_gaussian_integration_by_parts
    {ΩX ΩY ι : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    [Fintype ι] [DecidableEq ι]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (hX : IsCenteredJointlyGaussian PX X) (hY : IsCenteredJointlyGaussian PY Y)
    (a v : ι → ℝ) (γ t : ℝ) (F' F'' : ℝ → ℝ)
    (hF'meas : Measurable F') (hF''meas : Measurable F'')
    (hF' : ∀ x, HasDerivAt F' (F'' x) x)
    (c : Sum ι ι → ℝ) (hc : ∀ k, 0 ≤ c k) (M : ℝ) (hM : 0 ≤ M)
    (hGbound : ∀ z i,
      ‖kahaneSumVectorScore a v γ t F' z i‖ ≤
        M * Real.exp (∑ k, c k * |z k|))
    (hDbound : ∀ z i k,
      ‖kahaneSumVectorScoreDerivative a v γ t F' F'' z i k‖ ≤
        M * Real.exp (∑ k, c k * |z k|))
    (i : ι) (k : Sum ι ι) :
    ∫ ω, (fun ω : ΩX × ΩY =>
        match k with
        | Sum.inl j => X ω.1 j
        | Sum.inr j => Y ω.2 j) ω *
        kahaneSumVectorScore a v γ t F'
          (fun j => match j with
            | Sum.inl l => X ω.1 l
            | Sum.inr l => Y ω.2 l) i ∂(PX.prod PY) =
      ∑ j, DOZZ.gaussianCovariance (PX.prod PY)
          (fun ω => match k with
            | Sum.inl l => X ω.1 l
            | Sum.inr l => Y ω.2 l)
          (fun ω => match j with
            | Sum.inl l => X ω.1 l
            | Sum.inr l => Y ω.2 l) *
        ∫ ω, kahaneSumVectorScoreDerivative a v γ t F' F''
          (fun j => match j with
            | Sum.inl l => X ω.1 l
            | Sum.inr l => Y ω.2 l) i j ∂(PX.prod PY) := by
  classical
  let Z : ΩX × ΩY → Sum ι ι → ℝ := fun ω j => match j with
    | Sum.inl l => X ω.1 l
    | Sum.inr l => Y ω.2 l
  have hZ : IsCenteredJointlyGaussian (PX.prod PY) Z := by
    exact independent_product_concat_isCenteredJointlyGaussian PX PY X Y hX hY
  let G : (Sum ι ι → ℝ) → ℝ := fun z => kahaneSumVectorScore a v γ t F' z i
  let D : (Sum ι ι → ℝ) → Sum ι ι → ℝ := fun z j =>
    kahaneSumVectorScoreDerivative a v γ t F' F'' z i j
  have hGmeas : Measurable G := by
    dsimp [G, kahaneSumVectorScore, finiteChaosVectorTestScore]
    fun_prop [kahaneSumVectorField, finiteChaosVectorMass, finiteChaosVectorWeight]
  have hDmeas : ∀ j, Measurable (fun z => D z j) := by
    intro j
    cases j with
    | inl j =>
        by_cases hij : i = j
        · simp [D, kahaneSumVectorScoreDerivative,
            kahaneSumVectorFieldScoreDerivative, finiteChaosVectorTestScoreDerivative,
            hij]
          fun_prop [kahaneSumVectorField, finiteChaosVectorMass, finiteChaosVectorWeight]
        · simp [D, kahaneSumVectorScoreDerivative,
            kahaneSumVectorFieldScoreDerivative, finiteChaosVectorTestScoreDerivative,
            hij]
          fun_prop [kahaneSumVectorField, finiteChaosVectorMass, finiteChaosVectorWeight]
    | inr j =>
        by_cases hij : i = j
        · simp [D, kahaneSumVectorScoreDerivative,
            kahaneSumVectorFieldScoreDerivative, finiteChaosVectorTestScoreDerivative,
            hij]
          fun_prop [kahaneSumVectorField, finiteChaosVectorMass, finiteChaosVectorWeight]
        · simp [D, kahaneSumVectorScoreDerivative,
            kahaneSumVectorFieldScoreDerivative, finiteChaosVectorTestScoreDerivative,
            hij]
          fun_prop [kahaneSumVectorField, finiteChaosVectorMass, finiteChaosVectorWeight]
  have hGdir : ∀ (x d : Sum ι ι → ℝ) s,
      HasDerivAt (fun r => G (fun j => x j + r * d j))
        (∑ j, d j * D (fun j => x j + s * d j) j) s := by
    intro x d s
    simpa [G, D] using
      kahaneSumVectorScore_directional_hasDerivAt a v γ t F' F'' hF' x d i s
  have hGbound' : ∀ z, ‖G z‖ ≤ M * Real.exp (∑ j, c j * |z j|) := by
    intro z
    exact hGbound z i
  have hDbound' : ∀ z j, ‖D z j‖ ≤ M * Real.exp (∑ l, c l * |z l|) := by
    intro z j
    exact hDbound z i j
  have hresult := finite_gaussian_integration_by_parts_of_absExp_bound
    (PX.prod PY) Z hZ k G D hGmeas hDmeas c hc M hM hGbound' hDbound' hGdir
  simpa [Z, G, D] using hresult


/-- The smooth Kahane interpolation derivative has nonpositive expectation. The stated
integrability conditions are the finite exponential-envelope consequences needed by Gaussian IBP
and by rearranging the finite sums. -/
theorem kahaneSmoothInterpolation_integrand_nonpos_of_gaussian_ibp
    {ΩX ΩY ι : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    [Fintype ι] [DecidableEq ι]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (hX : IsCenteredJointlyGaussian PX X) (hY : IsCenteredJointlyGaussian PY Y)
    (a vX vY : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (γ t : ℝ)
    (F' F'' : ℝ → ℝ)
    (hF'meas : Measurable F') (hF''meas : Measurable F'')
    (hF' : ∀ x, HasDerivAt F' (F'' x) x)
    (hF''nonneg : ∀ x, 0 ≤ x → 0 ≤ F'' x)
    (ht : 0 < t) (ht1 : t < 1)
    (hvX : ∀ i, vX i = DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω i))
    (hvY : ∀ i, vY i = DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω i))
    (hcov : ∀ i j,
      DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) ≤
        DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j))
    (c : Sum ι ι → ℝ) (hc : ∀ k, 0 ≤ c k) (M : ℝ) (hM : 0 ≤ M)
    (hGbound : ∀ z i,
      ‖kahaneSumVectorScore a (fun i => t * vX i + (1 - t) * vY i)
          γ t F' z i‖ ≤ M * Real.exp (∑ k, c k * |z k|))
    (hDbound : ∀ z i k,
      ‖kahaneSumVectorScoreDerivative a (fun i => t * vX i + (1 - t) * vY i)
          γ t F' F'' z i k‖ ≤ M * Real.exp (∑ k, c k * |z k|))
    (hScoreInt : ∀ i, Integrable
      (fun ω : ΩX × ΩY => kahaneSumVectorScore a (fun i => t * vX i + (1 - t) * vY i)
        γ t F' (fun k => match k with
          | Sum.inl j => X ω.1 j
          | Sum.inr j => Y ω.2 j) i) (PX.prod PY))
    (hXScoreInt : ∀ i, Integrable
      (fun ω : ΩX × ΩY => X ω.1 i * kahaneSumVectorScore a
        (fun i => t * vX i + (1 - t) * vY i) γ t F'
        (fun k => match k with
          | Sum.inl j => X ω.1 j
          | Sum.inr j => Y ω.2 j) i) (PX.prod PY))
    (hYScoreInt : ∀ i, Integrable
      (fun ω : ΩX × ΩY => Y ω.2 i * kahaneSumVectorScore a
        (fun i => t * vX i + (1 - t) * vY i) γ t F'
        (fun k => match k with
          | Sum.inl j => X ω.1 j
          | Sum.inr j => Y ω.2 j) i) (PX.prod PY))
    (hFieldDInt : ∀ i j, Integrable
      (fun ω : ΩX × ΩY => kahaneSumVectorFieldScoreDerivative a
        (fun i => t * vX i + (1 - t) * vY i) γ t F' F''
        (fun k => match k with
          | Sum.inl l => X ω.1 l
          | Sum.inr l => Y ω.2 l) i j) (PX.prod PY))
    (hKInt : ∀ i j, Integrable
      (fun ω : ΩX × ΩY => finiteChaosVectorWeight a (fun i => t * vX i + (1 - t) * vY i)
        γ (kahaneSumVectorField t (fun k => match k with
          | Sum.inl l => X ω.1 l
          | Sum.inr l => Y ω.2 l)) i *
        finiteChaosVectorWeight a (fun i => t * vX i + (1 - t) * vY i)
          γ (kahaneSumVectorField t (fun k => match k with
            | Sum.inl l => X ω.1 l
            | Sum.inr l => Y ω.2 l)) j *
        F'' (finiteChaosVectorMass a (fun i => t * vX i + (1 - t) * vY i) γ
          (kahaneSumVectorField t (fun k => match k with
            | Sum.inl l => X ω.1 l
            | Sum.inr l => Y ω.2 l)))) (PX.prod PY)) :
    ∫ ω, kahaneInterpolatedTestDerivative X Y vX vY a γ F' t ω ∂(PX.prod PY) ≤ 0 := by
  classical
  let : IsProbabilityMeasure PX := hX.1
  let : IsProbabilityMeasure PY := hY.1
  let μ : Measure (ΩX × ΩY) := PX.prod PY
  let : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  let v : ι → ℝ := fun i => t * vX i + (1 - t) * vY i
  let Z : ΩX × ΩY → Sum ι ι → ℝ := fun ω k => match k with
    | Sum.inl i => X ω.1 i
    | Sum.inr i => Y ω.2 i
  let score (ω : ΩX × ΩY) (i : ι) : ℝ :=
    kahaneSumVectorScore a v γ t F' (Z ω) i
  let fieldD (ω : ΩX × ΩY) (i j : ι) : ℝ :=
    kahaneSumVectorFieldScoreDerivative a v γ t F' F'' (Z ω) i j
  let K (ω : ΩX × ΩY) (i j : ι) : ℝ :=
    finiteChaosVectorWeight a v γ (kahaneSumVectorField t (Z ω)) i *
      finiteChaosVectorWeight a v γ (kahaneSumVectorField t (Z ω)) j *
        F'' (finiteChaosVectorMass a v γ (kahaneSumVectorField t (Z ω)))
  let Hbar : ι → ι → ℝ := fun i j => γ * ∫ ω, fieldD ω i j ∂μ
  let Kbar : ι → ι → ℝ := fun i j => ∫ ω, K ω i j ∂μ
  let Dbar : ι → ℝ := fun i => ∫ ω, score ω i ∂μ
  let A : ι → ℝ := fun i => γ * ∫ ω, X ω.1 i * score ω i ∂μ
  let B : ι → ℝ := fun i => γ * ∫ ω, Y ω.2 i * score ω i ∂μ
  have hXibp : ∀ i, A i = Real.sqrt t * ∑ j,
      DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) * Hbar i j := by
    intro i
    have hIBP := kahaneSumVectorScore_gaussian_integration_by_parts PX PY X Y hX hY
      a v γ t F' F'' hF'meas hF''meas hF' c hc M hM hGbound hDbound i (Sum.inl i)
    have hsum : (∑ k, DOZZ.gaussianCovariance μ
        (fun ω => Z ω (Sum.inl i)) (fun ω => Z ω k) *
          ∫ ω, kahaneSumVectorScoreDerivative a v γ t F' F'' (Z ω) i k ∂μ) =
        Real.sqrt t * ∑ j,
          DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) *
            ∫ ω, fieldD ω i j ∂μ := by
      rw [Fintype.sum_sum_type]
      have hleft : (∑ j, DOZZ.gaussianCovariance μ
          (fun ω => Z ω (Sum.inl i)) (fun ω => Z ω (Sum.inl j)) *
            ∫ ω, kahaneSumVectorScoreDerivative a v γ t F' F'' (Z ω) i
              (Sum.inl j) ∂μ) =
          Real.sqrt t * ∑ j,
            DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) *
              ∫ ω, fieldD ω i j ∂μ := by
        calc
          _ = ∑ j, DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) *
              (Real.sqrt t * ∫ ω, fieldD ω i j ∂μ) := by
                apply Finset.sum_congr rfl
                intro j hj
                rw [gaussianCovariance_product_concat PX PY X Y hX hY
                  (Sum.inl i) (Sum.inl j)]
                simp [fieldD, kahaneSumVectorScoreDerivative,
                  kahaneSumVectorFieldScoreDerivative, integral_const_mul]
          _ = Real.sqrt t * ∑ j,
              DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) *
                ∫ ω, fieldD ω i j ∂μ := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro j hj
                  ring
      have hright : (∑ j, DOZZ.gaussianCovariance μ
          (fun ω => Z ω (Sum.inl i)) (fun ω => Z ω (Sum.inr j)) *
            ∫ ω, kahaneSumVectorScoreDerivative a v γ t F' F'' (Z ω) i
              (Sum.inr j) ∂μ) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [gaussianCovariance_product_concat PX PY X Y hX hY (Sum.inl i) (Sum.inr j)]
        simp
      rw [hleft, hright, add_zero]
    calc
      A i = γ * ∫ ω, X ω.1 i * score ω i ∂μ := rfl
      _ = γ * (∑ k, DOZZ.gaussianCovariance μ
          (fun ω => Z ω (Sum.inl i)) (fun ω => Z ω k) *
          ∫ ω, kahaneSumVectorScoreDerivative a v γ t F' F'' (Z ω) i k ∂μ) := by
            rw [← hIBP]
      _ = Real.sqrt t * ∑ j,
          DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) * Hbar i j := by
            rw [hsum]
            simp only [Hbar]
            calc
              γ * (Real.sqrt t * ∑ j,
                  DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) *
                    ∫ ω, fieldD ω i j ∂μ) =
                  ∑ j, (γ * Real.sqrt t) *
                    (DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) *
                      ∫ ω, fieldD ω i j ∂μ) := by
                        rw [← mul_assoc, Finset.mul_sum]
              _ = Real.sqrt t * ∑ j,
                  DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) *
                    (γ * ∫ ω, fieldD ω i j ∂μ) := by
                        rw [Finset.mul_sum]
                        apply Finset.sum_congr rfl
                        intro j hj
                        ring
  have hYibp : ∀ i, B i = Real.sqrt (1 - t) * ∑ j,
      DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j) * Hbar i j := by
    intro i
    have hIBP := kahaneSumVectorScore_gaussian_integration_by_parts PX PY X Y hX hY
      a v γ t F' F'' hF'meas hF''meas hF' c hc M hM hGbound hDbound i (Sum.inr i)
    have hsum : (∑ k, DOZZ.gaussianCovariance μ
        (fun ω => Z ω (Sum.inr i)) (fun ω => Z ω k) *
          ∫ ω, kahaneSumVectorScoreDerivative a v γ t F' F'' (Z ω) i k ∂μ) =
        Real.sqrt (1 - t) * ∑ j,
          DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j) *
            ∫ ω, fieldD ω i j ∂μ := by
      rw [Fintype.sum_sum_type]
      have hleft : (∑ j, DOZZ.gaussianCovariance μ
          (fun ω => Z ω (Sum.inr i)) (fun ω => Z ω (Sum.inl j)) *
            ∫ ω, kahaneSumVectorScoreDerivative a v γ t F' F'' (Z ω) i
              (Sum.inl j) ∂μ) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        rw [gaussianCovariance_product_concat PX PY X Y hX hY (Sum.inr i) (Sum.inl j)]
        simp
      have hright : (∑ j, DOZZ.gaussianCovariance μ
          (fun ω => Z ω (Sum.inr i)) (fun ω => Z ω (Sum.inr j)) *
            ∫ ω, kahaneSumVectorScoreDerivative a v γ t F' F'' (Z ω) i
              (Sum.inr j) ∂μ) =
          Real.sqrt (1 - t) * ∑ j,
            DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j) *
              ∫ ω, fieldD ω i j ∂μ := by
        calc
          _ = ∑ j, DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j) *
              (Real.sqrt (1 - t) * ∫ ω, fieldD ω i j ∂μ) := by
                apply Finset.sum_congr rfl
                intro j hj
                rw [gaussianCovariance_product_concat PX PY X Y hX hY
                  (Sum.inr i) (Sum.inr j)]
                simp [fieldD, kahaneSumVectorScoreDerivative,
                  kahaneSumVectorFieldScoreDerivative, integral_const_mul]
          _ = Real.sqrt (1 - t) * ∑ j,
              DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j) *
                ∫ ω, fieldD ω i j ∂μ := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro j hj
                  ring
      rw [hleft, zero_add, hright]
    calc
      B i = γ * ∫ ω, Y ω.2 i * score ω i ∂μ := rfl
      _ = γ * (∑ k, DOZZ.gaussianCovariance μ
          (fun ω => Z ω (Sum.inr i)) (fun ω => Z ω k) *
          ∫ ω, kahaneSumVectorScoreDerivative a v γ t F' F'' (Z ω) i k ∂μ) := by
            rw [← hIBP]
      _ = Real.sqrt (1 - t) * ∑ j,
          DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j) * Hbar i j := by
            rw [hsum]
            simp only [Hbar]
            calc
              γ * (Real.sqrt (1 - t) * ∑ j,
                  DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j) *
                    ∫ ω, fieldD ω i j ∂μ) =
                  ∑ j, (γ * Real.sqrt (1 - t)) *
                    (DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j) *
                      ∫ ω, fieldD ω i j ∂μ) := by
                        rw [← mul_assoc, Finset.mul_sum]
              _ = Real.sqrt (1 - t) * ∑ j,
                  DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j) *
                    (γ * ∫ ω, fieldD ω i j ∂μ) := by
                        rw [Finset.mul_sum]
                        apply Finset.sum_congr rfl
                        intro j hj
                        ring
  have hHessian : ∀ i j, Hbar i j = γ ^ 2 * Kbar i j +
      if i = j then γ ^ 2 * Dbar i else 0 := by
    intro i j
    have hintD := hScoreInt i
    have hintK := hKInt i j
    have hintField := hFieldDInt i j
    have hpoint (ω : ΩX × ΩY) : γ * fieldD ω i j =
        γ ^ 2 * K ω i j + if i = j then γ ^ 2 * score ω i else 0 := by
      simp only [fieldD, kahaneSumVectorFieldScoreDerivative,
        finiteChaosVectorTestScoreDerivative]
      by_cases hij : i = j
      · subst j
        dsimp [score, K, kahaneSumVectorScore, finiteChaosVectorTestScore]
        simp_all
        ring_nf
      · simp only [ite_eq_right hij]
        dsimp [score, K, kahaneSumVectorScore, finiteChaosVectorTestScore]
        ring
    have hintRhs : Integrable (fun ω => γ ^ 2 * K ω i j +
        if i = j then γ ^ 2 * score ω i else 0) μ := by
      by_cases hij : i = j
      · subst j
        have hfun : (fun ω : ΩX × ΩY => γ ^ 2 * K ω i i +
            if i = i then γ ^ 2 * score ω i else 0) =
            fun ω => γ ^ 2 * K ω i i + γ ^ 2 * score ω i := by
          funext ω
          simp
        rw [hfun]
        exact (hintK.const_mul (γ ^ 2)).add (hintD.const_mul (γ ^ 2))
      · simpa [hij] using hintK.const_mul (γ ^ 2)
    calc
      Hbar i j = ∫ ω, γ * fieldD ω i j ∂μ := by
        dsimp [Hbar]
        exact (integral_const_mul γ (fun ω => fieldD ω i j)).symm
      _ = ∫ ω, γ ^ 2 * K ω i j + if i = j then γ ^ 2 * score ω i else 0 ∂μ := by
        apply integral_congr_ae
        exact ae_of_all μ hpoint
      _ = γ ^ 2 * Kbar i j + if i = j then γ ^ 2 * Dbar i else 0 := by
        by_cases hij : i = j
        · subst j
          have hfun : (fun ω : ΩX × ΩY => γ ^ 2 * K ω i i +
              if i = i then γ ^ 2 * score ω i else 0) =
              fun ω => γ ^ 2 * K ω i i + γ ^ 2 * score ω i := by
            funext ω
            simp
          rw [hfun]
          rw [integral_add (hintK.const_mul _) (hintD.const_mul _), integral_const_mul,
            integral_const_mul]
          simp [Kbar, Dbar, K, score, v, Z]
          dsimp [μ]
        · have hfun : (fun ω : ΩX × ΩY => γ ^ 2 * K ω i j +
              if i = j then γ ^ 2 * score ω i else 0) =
              fun ω => γ ^ 2 * K ω i j := by
            funext ω
            simp [hij]
          rw [hfun]
          rw [integral_const_mul]
          change γ ^ 2 * (∫ ω, K ω i j ∂μ) =
            γ ^ 2 * Kbar i j + if i = j then γ ^ 2 * Dbar i else 0
          simp [hij, Kbar]
  have hKnonneg : ∀ i j, 0 ≤ Kbar i j := by
    intro i j
    apply integral_nonneg
    intro ω
    have hwi : 0 ≤ finiteChaosVectorWeight a v γ (kahaneSumVectorField t (Z ω)) i :=
      mul_nonneg (ha i) (Real.exp_nonneg _)
    have hwj : 0 ≤ finiteChaosVectorWeight a v γ (kahaneSumVectorField t (Z ω)) j :=
      mul_nonneg (ha j) (Real.exp_nonneg _)
    change 0 ≤ finiteChaosVectorWeight a v γ (kahaneSumVectorField t (Z ω)) i *
      finiteChaosVectorWeight a v γ (kahaneSumVectorField t (Z ω)) j *
        F'' (finiteChaosVectorMass a v γ (kahaneSumVectorField t (Z ω)))
    exact mul_nonneg (mul_nonneg hwi hwj)
      (hF''nonneg _ (finiteChaosVectorMass_nonneg a v γ ha
        (kahaneSumVectorField t (Z ω))) )
  have hderivIdentity :
      ∫ ω, kahaneInterpolatedTestDerivative X Y vX vY a γ F' t ω ∂μ =
        (∑ i, A i) / (2 * Real.sqrt t) -
        (∑ i, B i) / (2 * Real.sqrt (1 - t)) -
        γ ^ 2 / 2 * ∑ i, (vX i - vY i) * Dbar i := by
    have hpoint (ω : ΩX × ΩY) :
        kahaneInterpolatedTestDerivative X Y vX vY a γ F' t ω =
          ∑ i, score ω i * (γ * (X ω.1 i / (2 * Real.sqrt t) -
            Y ω.2 i / (2 * Real.sqrt (1 - t))) -
            γ ^ 2 / 2 * (vX i - vY i)) := by
      rw [kahaneInterpolatedTestDerivative]
      have hmass : kahaneInterpolatedMass X Y vX vY a γ t ω =
          finiteChaosVectorMass a v γ (kahaneSumVectorField t (Z ω)) := by
        simp [kahaneInterpolatedMass, finiteChaosVectorMass, finiteChaosVectorWeight,
          kahaneSumVectorField, Z, v, mul_comm]
      have hweight (i : ι) :
          a i * Real.exp (γ * (Real.sqrt t * X ω.1 i +
            Real.sqrt (1 - t) * Y ω.2 i) -
            γ ^ 2 / 2 * (t * vX i + (1 - t) * vY i)) =
          finiteChaosVectorWeight a v γ (kahaneSumVectorField t (Z ω)) i := by
        simp [finiteChaosVectorWeight, kahaneSumVectorField, Z, v]
      rw [hmass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [score, kahaneSumVectorScore, finiteChaosVectorTestScore]
      rw [hweight i]
      ring
    have htermInt (i : ι) : Integrable (fun ω : ΩX × ΩY =>
        score ω i * (γ * (X ω.1 i / (2 * Real.sqrt t) -
          Y ω.2 i / (2 * Real.sqrt (1 - t))) -
          γ ^ 2 / 2 * (vX i - vY i))) μ := by
      have hX := (hXScoreInt i).const_mul (γ / (2 * Real.sqrt t))
      have hY := (hYScoreInt i).const_mul (γ / (2 * Real.sqrt (1 - t)))
      have hD := (hScoreInt i).const_mul (γ ^ 2 / 2 * (vX i - vY i))
      have hxy := hX.sub hY
      convert hxy.sub hD using 1; ext ω; simp [score]; ring
    have htermEval (i : ι) :
        (∫ ω, score ω i * (γ * (X ω.1 i / (2 * Real.sqrt t) -
          Y ω.2 i / (2 * Real.sqrt (1 - t))) -
          γ ^ 2 / 2 * (vX i - vY i)) ∂μ) =
        A i / (2 * Real.sqrt t) - B i / (2 * Real.sqrt (1 - t)) -
          γ ^ 2 / 2 * (vX i - vY i) * Dbar i := by
      have hpoint' (ω : ΩX × ΩY) :
          score ω i * (γ * (X ω.1 i / (2 * Real.sqrt t) -
            Y ω.2 i / (2 * Real.sqrt (1 - t))) -
            γ ^ 2 / 2 * (vX i - vY i)) =
          (γ / (2 * Real.sqrt t)) * (X ω.1 i * score ω i) -
            (γ / (2 * Real.sqrt (1 - t)) * (Y ω.2 i * score ω i)) -
            (γ ^ 2 / 2 * (vX i - vY i)) * score ω i := by
        ring
      calc
        _ = ∫ ω, (γ / (2 * Real.sqrt t)) * (X ω.1 i * score ω i) -
            (γ / (2 * Real.sqrt (1 - t)) * (Y ω.2 i * score ω i)) -
            (γ ^ 2 / 2 * (vX i - vY i)) * score ω i ∂μ := by
              apply integral_congr_ae
              exact ae_of_all μ hpoint'
        _ = (γ / (2 * Real.sqrt t)) * ∫ ω, X ω.1 i * score ω i ∂μ -
            (γ / (2 * Real.sqrt (1 - t)) * ∫ ω, Y ω.2 i * score ω i ∂μ) -
            (γ ^ 2 / 2 * (vX i - vY i)) * ∫ ω, score ω i ∂μ := by
              let hXi : Integrable (fun ω : ΩX × ΩY =>
                  (γ / (2 * Real.sqrt t)) * (X ω.1 i * score ω i)) μ := by
                convert (hXScoreInt i).const_mul (γ / (2 * Real.sqrt t)) using 1
              let hYi : Integrable (fun ω : ΩX × ΩY =>
                  (γ / (2 * Real.sqrt (1 - t))) * (Y ω.2 i * score ω i)) μ := by
                convert (hYScoreInt i).const_mul (γ / (2 * Real.sqrt (1 - t))) using 1
              let hDi : Integrable (fun ω : ΩX × ΩY =>
                  (γ ^ 2 / 2 * (vX i - vY i)) * score ω i) μ := by
                convert (hScoreInt i).const_mul (γ ^ 2 / 2 * (vX i - vY i)) using 1
              calc
                _ = (∫ ω, (γ / (2 * Real.sqrt t) * (X ω.1 i * score ω i) -
                      γ / (2 * Real.sqrt (1 - t)) * (Y ω.2 i * score ω i)) ∂μ) -
                    ∫ ω, (γ ^ 2 / 2 * (vX i - vY i)) * score ω i ∂μ := by
                      exact integral_sub (hXi.sub hYi) hDi
                _ = _ := by
                  rw [integral_sub hXi hYi, integral_const_mul, integral_const_mul,
                    integral_const_mul]
        _ = _ := by simp [A, B, Dbar]; ring
    calc
      _ = ∫ ω, ∑ i, score ω i * (γ * (X ω.1 i / (2 * Real.sqrt t) -
            Y ω.2 i / (2 * Real.sqrt (1 - t))) -
            γ ^ 2 / 2 * (vX i - vY i)) ∂μ := by
              apply integral_congr_ae
              exact ae_of_all μ hpoint
      _ = ∑ i, ∫ ω, score ω i * (γ * (X ω.1 i / (2 * Real.sqrt t) -
            Y ω.2 i / (2 * Real.sqrt (1 - t))) -
            γ ^ 2 / 2 * (vX i - vY i)) ∂μ := by
              exact integral_finsetSum Finset.univ (fun i hi => htermInt i)
      _ = _ := by
        calc
          _ = ∑ i, (A i / (2 * Real.sqrt t) - B i / (2 * Real.sqrt (1 - t)) -
              γ ^ 2 / 2 * (vX i - vY i) * Dbar i) := by
                apply Finset.sum_congr rfl
                intro i hi
                exact htermEval i
          _ = (∑ i, A i) / (2 * Real.sqrt t) -
              (∑ i, B i) / (2 * Real.sqrt (1 - t)) -
              γ ^ 2 / 2 * ∑ i, (vX i - vY i) * Dbar i := by
                rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib,
                  ← Finset.sum_div, ← Finset.sum_div]
                congr 1
                calc
                  ∑ i, (γ ^ 2 / 2) * (vX i - vY i) * Dbar i =
                      (γ ^ 2 / 2) * ∑ i, (vX i - vY i) * Dbar i := by
                        rw [Finset.mul_sum]
                        apply Finset.sum_congr rfl
                        intro i hi
                        ring
                  _ = _ := rfl
  rw [hderivIdentity]
  have hsign := kahaneInterpolation_derivative_nonpos_of_covariance_order γ t
    (fun i j => DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j))
    (fun i j => DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j))
    A B Hbar Kbar Dbar ht ht1 hcov hKnonneg hXibp hYibp hHessian
  have hdiag : (∑ i, (vX i - vY i) * Dbar i) =
      ∑ i, (DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω i) -
        DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω i)) * Dbar i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hvX i, hvY i]
  simpa only [hdiag] using hsign

end DOZZ.Proofs

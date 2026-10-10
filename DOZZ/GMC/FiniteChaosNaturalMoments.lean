/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteChaosMean
public import Mathlib.Probability.Moments.Variance

/-! Integer finite-chaos moments from the Gaussian law of a sum of Wick factors. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal

namespace DOZZ.Proofs

/-- A finite linear image of a centered jointly Gaussian family is still centered jointly
Gaussian. The coefficient type may repeat or mix coordinates arbitrarily. -/
private theorem centeredJointlyGaussian_linearMap
    {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype κ]
    (P : Measure Ω) (Z : Ω → ι → ℝ) (hZ : DOZZ.IsCenteredJointlyGaussian P Z)
    (B : κ → ι → ℝ) :
    DOZZ.IsCenteredJointlyGaussian P (fun ω k => ∑ i, B k i * Z ω i) := by
  classical
  refine ⟨hZ.1, ?_, ?_⟩
  · intro k
    exact Finset.aemeasurable_fun_sum Finset.univ fun i hi =>
      (hZ.2.1 i).const_mul (B k i)
  · intro c
    let d : ι → ℝ := fun i => ∑ k, c k * B k i
    have hsum (ω : Ω) :
        ∑ k, c k * (∑ i, B k i * Z ω i) = ∑ i, d i * Z ω i := by
      dsimp [d]
      calc
        ∑ k, c k * (∑ i, B k i * Z ω i) =
            ∑ k, ∑ i, c k * (B k i * Z ω i) := by simp_rw [Finset.mul_sum]
        _ = ∑ i, ∑ k, (c k * B k i) * Z ω i := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro k hk
              ring
        _ = ∑ i, (∑ k, c k * B k i) * Z ω i := by
              simp_rw [← Finset.sum_mul]
    obtain ⟨hmem, v, hmap⟩ := hZ.2.2 d
    refine ⟨?_, ⟨v, ?_⟩⟩
    · simpa only [hsum] using hmem
    · simpa only [hsum] using hmap

noncomputable def tupleOffDiagonalCovariance
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {n : ℕ}
    (P : Measure Ω) (Z : Ω → ι → ℝ) (s : Fin n → ι) : ℝ :=
  ∑ a, ∑ b, if a = b then 0 else
    DOZZ.gaussianCovariance P (fun ω => Z ω (s a)) (fun ω => Z ω (s b))

/-- The product of any finite tuple of Wick exponentials has expectation equal to the exponential
of half the off-diagonal covariance sum. The proof combines the tuple into one Gaussian linear
combination, so no covariance nonsingularity is needed. -/
theorem finite_wick_tuple_moment
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (n : ℕ) (P : Measure Ω) (Z : Ω → ι → ℝ)
    (hZ : DOZZ.IsCenteredJointlyGaussian P Z) (s : Fin n → ι) (γ : ℝ) :
    ∫⁻ ω, ∏ a, ENNReal.ofReal (Real.exp
      (γ * Z ω (s a) - γ ^ 2 / 2 *
        DOZZ.gaussianVariance P (fun ω => Z ω (s a)))) ∂P =
      ENNReal.ofReal (Real.exp
        (γ ^ 2 / 2 * tupleOffDiagonalCovariance P Z s)) := by
  classical
  have _ : IsProbabilityMeasure P := hZ.1
  let U : Ω → Fin n → ℝ := fun ω a => Z ω (s a)
  let B : (Fin n) → ι → ℝ := fun a i => if s a = i then 1 else 0
  have hU : DOZZ.IsCenteredJointlyGaussian P U := by
    have h := centeredJointlyGaussian_linearMap P Z hZ B
    refine ⟨h.1, ?_, ?_⟩
    · intro a
      simpa [U, B, eq_comm] using h.2.1 a
    · intro c
      have hcoordinate (ω : Ω) (a : Fin n) :
          U ω a = ∑ i, B a i * Z ω i := by
        simp [U, B, eq_comm]
      have hsum (ω : Ω) :
          ∑ a, c a * U ω a = ∑ a, c a * (∑ i, B a i * Z ω i) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [hcoordinate]
      obtain ⟨hm, ⟨v, hmap⟩⟩ := h.2.2 c
      refine ⟨?_, v, ?_⟩
      · simpa only [hsum] using hm
      · rw [show (fun ω => ∑ a, c a * U ω a) =
          fun ω => ∑ a, c a * (∑ i, B a i * Z ω i) from funext hsum]
        exact hmap
  let C : Unit → Fin n → ℝ := fun _ _ => 1
  let S : Ω → ℝ := fun ω => ∑ a, U ω a
  have hS : DOZZ.IsCenteredJointlyGaussian P (fun ω (_ : Unit) => S ω) := by
    simpa [S, C] using centeredJointlyGaussian_linearMap P U hU C
  let W (a : Fin n) (ω : Ω) := Real.exp
    (γ * U ω a - γ ^ 2 / 2 * DOZZ.gaussianVariance P (fun ω => U ω a))
  let D : ℝ := ∑ a, DOZZ.gaussianVariance P (fun ω => U ω a)
  have hmean (a : Fin n) : (∫ ω, U ω a ∂P) = 0 := by
    obtain ⟨_, _, hmean, _⟩ := coordinate_mean_variance P U hU a
    exact hmean
  have hUmem (a : Fin n) : MemLp (fun ω => U ω a) 2 P := by
    obtain ⟨hm, _⟩ := hU.2.2 (Pi.single a 1)
    simpa [Pi.single_apply] using hm
  have hSmean : (∫ ω, S ω ∂P) = 0 := by
    dsimp [S]
    rw [integral_finsetSum]
    · simp [hmean]
    · intro a ha
      exact (hUmem a).integrable (by norm_num)
  have hSvariance : DOZZ.gaussianVariance P S = D +
      tupleOffDiagonalCovariance P Z s := by
    let μ : Measure Ω := P
    have hcov (a b : Fin n) :
        ProbabilityTheory.covariance (fun ω => U ω a) (fun ω => U ω b) μ =
          DOZZ.gaussianCovariance P (fun ω => U ω a) (fun ω => U ω b) := by
      rw [ProbabilityTheory.covariance_eq_sub (hUmem a) (hUmem b), hmean a, hmean b]
      simp [DOZZ.gaussianCovariance]
    have hvar := ProbabilityTheory.variance_fun_sum
      (μ := μ) (X := fun a ω => U ω a) hUmem
    have hvarMean : Var[S; P] = DOZZ.gaussianVariance P S := by
      rw [variance_eq_integral (hS.2.1 ()), hSmean]
      simp [DOZZ.gaussianVariance, DOZZ.gaussianCovariance, S, pow_two]
    have hsplit :
        (∑ a, ∑ b,
          DOZZ.gaussianCovariance P (fun ω => U ω a) (fun ω => U ω b)) =
          D + ∑ a, ∑ b, if a = b then 0 else
            DOZZ.gaussianCovariance P (fun ω => U ω a) (fun ω => U ω b) := by
      rw [show (∑ a, ∑ b,
          DOZZ.gaussianCovariance P (fun ω => U ω a) (fun ω => U ω b)) =
          ∑ a, ∑ b,
            ((if a = b then DOZZ.gaussianCovariance P
                (fun ω => U ω a) (fun ω => U ω b) else 0) +
              (if a = b then 0 else DOZZ.gaussianCovariance P
                (fun ω => U ω a) (fun ω => U ω b))) by
            apply Finset.sum_congr rfl
            intro a ha
            apply Finset.sum_congr rfl
            intro b hb
            by_cases hab : a = b <;> simp [hab]]
      simp only [Finset.sum_add_distrib]
      congr 1
      · apply Finset.sum_congr rfl
        intro a ha
        rw [Finset.sum_eq_single a]
        · simp [DOZZ.gaussianVariance, DOZZ.gaussianCovariance]
        · intro b hb hba
          simp [Ne.symm hba]
        · intro hnot
          exact (hnot (Finset.mem_univ a)).elim
    calc
      DOZZ.gaussianVariance P S = Var[S; P] := hvarMean.symm
      _ = ∑ a, ∑ b,
          ProbabilityTheory.covariance (fun ω => U ω a) (fun ω => U ω b) μ := by
            simpa [S, μ] using hvar
      _ = D + ∑ a, ∑ b, if a = b then 0 else
            DOZZ.gaussianCovariance P (fun ω => U ω a) (fun ω => U ω b) := by
            simp_rw [hcov]
            exact hsplit
      _ = D + tupleOffDiagonalCovariance P Z s := by
            congr 1
  have hsumExponent (ω : Ω) :
      (∑ a, (γ * U ω a - γ ^ 2 / 2 *
        DOZZ.gaussianVariance P (fun ω => U ω a))) =
        (γ * S ω - γ ^ 2 / 2 * DOZZ.gaussianVariance P S) +
          γ ^ 2 / 2 * tupleOffDiagonalCovariance P Z s := by
    rw [hSvariance]
    simp only [Finset.sum_sub_distrib]
    dsimp [D, S]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    ring_nf
  have hpoint (ω : Ω) :
      (∏ a, ENNReal.ofReal (W a ω)) =
        ENNReal.ofReal (Real.exp (γ ^ 2 / 2 * tupleOffDiagonalCovariance P Z s)) *
          ENNReal.ofReal (Real.exp
            (γ * S ω - γ ^ 2 / 2 * DOZZ.gaussianVariance P S)) := by
    calc
      _ = ENNReal.ofReal (∏ a, Real.exp
          (γ * U ω a - γ ^ 2 / 2 *
            DOZZ.gaussianVariance P (fun ω => U ω a))) := by
              rw [← ENNReal.ofReal_prod_of_nonneg (s := Finset.univ)
                (fun a ha => Real.exp_nonneg _)]
      _ = ENNReal.ofReal (Real.exp (∑ a,
          (γ * U ω a - γ ^ 2 / 2 *
            DOZZ.gaussianVariance P (fun ω => U ω a)))) := by
              rw [← Real.exp_sum]
      _ = _ := by
              rw [hsumExponent ω, Real.exp_add,
                ENNReal.ofReal_mul (Real.exp_nonneg _)]
              exact mul_comm _ _
  have hWickIntegral :
      ∫⁻ ω, ENNReal.ofReal (Real.exp
        (γ * S ω - γ ^ 2 / 2 * DOZZ.gaussianVariance P S)) ∂P = 1 := by
    simpa [S] using wick_exponential_lintegral_expectation P
      (fun ω (_ : Unit) => ∑ a, U ω a) hS () γ
  calc
    _ = ∫⁻ ω, ENNReal.ofReal (Real.exp (γ ^ 2 / 2 *
          tupleOffDiagonalCovariance P Z s)) *
          ENNReal.ofReal (Real.exp
            (γ * S ω - γ ^ 2 / 2 * DOZZ.gaussianVariance P S)) ∂P := by
          apply lintegral_congr_ae
          exact ae_of_all P hpoint
    _ = ENNReal.ofReal (Real.exp
          (γ ^ 2 / 2 * tupleOffDiagonalCovariance P Z s)) := by
          rw [lintegral_const_mul'' _
            (wick_exponential_integrable_expectation P
              (fun ω (_ : Unit) => ∑ a, U ω a) hS () γ).1.aemeasurable.ennreal_ofReal,
            hWickIntegral, mul_one]

/-- Every natural finite-chaos moment expands into a sum over coordinate tuples. -/
theorem finiteChaosMoment_nat_formula
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ) (hZ : DOZZ.IsCenteredJointlyGaussian P Z)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (γ : ℝ) (n : ℕ) :
    DOZZ.finiteChaosMoment P Z a γ (n : ℝ) =
      ∑ s : Fin n → ι, ENNReal.ofReal
        ((∏ j, a (s j)) * Real.exp
          (γ ^ 2 / 2 * tupleOffDiagonalCovariance P Z s)) := by
  classical
  let W (i : ι) (ω : Ω) := Real.exp
    (γ * Z ω i - γ ^ 2 / 2 * DOZZ.gaussianVariance P (fun ω => Z ω i))
  let u (i : ι) (ω : Ω) := ENNReal.ofReal (a i * W i ω)
  let term (s : Fin n → ι) (ω : Ω) := ∏ j, u (s j) ω
  have hWick (i : ι) : Integrable (W i) P :=
    (wick_exponential_integrable_expectation P Z hZ i γ).1
  have huMeas (i : ι) : AEMeasurable (u i ·) P := by
    dsimp [u, W]
    exact ((hWick i).aemeasurable.const_mul (a i)).ennreal_ofReal
  have htermMeas (s : Fin n → ι) : AEMeasurable (term s) P := by
    dsimp [term]
    exact Finset.aemeasurable_fun_prod Finset.univ fun j hj => huMeas (s j)
  have htermFactor (s : Fin n → ι) (ω : Ω) :
      term s ω = ENNReal.ofReal (∏ j, a (s j)) *
        (∏ j, ENNReal.ofReal (W (s j) ω)) := by
    dsimp [term, u, W]
    calc
      _ = ENNReal.ofReal (∏ j, a (s j) * W (s j) ω) := by
            rw [← ENNReal.ofReal_prod_of_nonneg (s := Finset.univ)
              (fun j hj => mul_nonneg (ha (s j)) (Real.exp_nonneg _))]
      _ = ENNReal.ofReal (∏ j, a (s j)) *
          ENNReal.ofReal (∏ j, W (s j) ω) := by
            rw [Finset.prod_mul_distrib,
              ENNReal.ofReal_mul (Finset.prod_nonneg fun j hj => ha (s j))]
      _ = _ := by
            rw [ENNReal.ofReal_prod_of_nonneg (s := Finset.univ)
              (fun j hj => Real.exp_nonneg _)]
  have htermIntegral (s : Fin n → ι) :
      ∫⁻ ω, term s ω ∂P = ENNReal.ofReal
        ((∏ j, a (s j)) * Real.exp
          (γ ^ 2 / 2 * tupleOffDiagonalCovariance P Z s)) := by
    calc
      _ = ENNReal.ofReal (∏ j, a (s j)) *
          (∫⁻ ω, ∏ j, ENNReal.ofReal (W (s j) ω) ∂P) := by
            rw [show (fun ω => term s ω) = fun ω =>
                ENNReal.ofReal (∏ j, a (s j)) *
                  (∏ j, ENNReal.ofReal (W (s j) ω)) by
                  funext ω
                  exact htermFactor s ω]
            exact lintegral_const_mul'' _
              (Finset.aemeasurable_fun_prod Finset.univ fun j hj =>
                (hWick (s j)).aemeasurable.ennreal_ofReal)
      _ = ENNReal.ofReal (∏ j, a (s j)) *
          ENNReal.ofReal (Real.exp
            (γ ^ 2 / 2 * tupleOffDiagonalCovariance P Z s)) := by
              rw [finite_wick_tuple_moment n P Z hZ s γ]
      _ = _ := by
              rw [← ENNReal.ofReal_mul (Finset.prod_nonneg fun j hj => ha (s j))]
  have hmass (ω : Ω) : DOZZ.finiteChaosMass P Z a γ ω = ∑ i, a i * W i ω := by
    simp [DOZZ.finiteChaosMass, W]
  have hsum (ω : Ω) :
      ENNReal.ofReal (DOZZ.finiteChaosMass P Z a γ ω) = ∑ i, u i ω := by
    rw [hmass ω, ENNReal.ofReal_sum_of_nonneg]
    intro i hi
    exact mul_nonneg (ha i) (Real.exp_nonneg _)
  have hpoint (ω : Ω) :
      ENNReal.rpow (ENNReal.ofReal (DOZZ.finiteChaosMass P Z a γ ω)) n =
        ∑ s : Fin n → ι, term s ω := by
    calc
      _ = (ENNReal.ofReal (DOZZ.finiteChaosMass P Z a γ ω)) ^ n :=
        ENNReal.rpow_natCast _ n
      _ = ∑ s : Fin n → ι, term s ω := by
        rw [hsum, Fintype.sum_pow]
  rw [DOZZ.finiteChaosMoment]
  calc
    ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (DOZZ.finiteChaosMass P Z a γ ω)) n ∂P =
        ∫⁻ ω, ∑ s : Fin n → ι, term s ω ∂P := by
          apply lintegral_congr_ae
          exact ae_of_all P hpoint
    _ = ∑ s : Fin n → ι, ∫⁻ ω, term s ω ∂P :=
          lintegral_finsetSum' Finset.univ (fun s hs => htermMeas s)
    _ = _ := by
          apply Finset.sum_congr rfl
          intro s hs
          exact htermIntegral s

/-- Entrywise covariance order compares all natural finite-chaos moments. -/
theorem kahane_finite_power_nat
    {ΩX ΩY ι : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [Fintype ι]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (hX : DOZZ.IsCenteredJointlyGaussian PX X) (hY : DOZZ.IsCenteredJointlyGaussian PY Y)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (γ : ℝ) (n : ℕ)
    (hcov : ∀ i j, DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) ≤
      DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j)) :
    DOZZ.finiteChaosMoment PX X a γ (n : ℝ) ≤
      DOZZ.finiteChaosMoment PY Y a γ (n : ℝ) := by
  rw [finiteChaosMoment_nat_formula PX X hX a ha γ n,
    finiteChaosMoment_nat_formula PY Y hY a ha γ n]
  apply Finset.sum_le_sum
  intro s hs
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _
    (Finset.prod_nonneg fun j hj => ha (s j))
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ γ ^ 2 / 2)
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  by_cases hij : i = j
  · simp [hij]
  · simp [hij]
    exact hcov (s i) (s j)


end DOZZ.Proofs

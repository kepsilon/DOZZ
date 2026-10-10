/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteChaosMean
public import DOZZ.GMC.FiniteGaussianTilt

/-! Pairwise Wick moments and the second moment of finite Gaussian chaos. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- The mixed second moment of two Wick exponentials is the exponential of their covariance.
The identity follows from the finite tilt formula, including for singular joint Gaussian laws. -/
theorem finite_wick_pair_second_moment
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ)
    (hZ : IsCenteredJointlyGaussian P Z) (i j : ι) (γ : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp
      (γ * Z ω i - γ ^ 2 / 2 * gaussianVariance P (fun ω => Z ω i))) *
      ENNReal.ofReal (Real.exp
      (γ * Z ω j - γ ^ 2 / 2 * gaussianVariance P (fun ω => Z ω j))) ∂P =
      ENNReal.ofReal (Real.exp
        (γ ^ 2 * gaussianCovariance P (fun ω => Z ω j) (fun ω => Z ω i))) := by
  classical
  let tilt : ι → ℝ := fun k => if k = i then γ else 0
  let F : (ι → ℝ) → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp
    (γ * z j - γ ^ 2 / 2 * gaussianVariance P (fun ω => Z ω j)))
  have hF : Measurable F := by
    dsimp [F]
    fun_prop
  have hlin (ω : Ω) : ∑ k, tilt k * Z ω k = γ * Z ω i := by
    simp [tilt]
  have hquad : (∑ k, ∑ l, tilt k * gaussianCovariance P
      (fun ω => Z ω k) (fun ω => Z ω l) * tilt l) =
      γ ^ 2 * gaussianVariance P (fun ω => Z ω i) := by
    simp [tilt, gaussianVariance]
    ring
  have hshift (k : ι) : ∑ l, gaussianCovariance P
      (fun ω => Z ω k) (fun ω => Z ω l) * tilt l =
        γ * gaussianCovariance P (fun ω => Z ω k) (fun ω => Z ω i) := by
    simp [tilt]
    ring
  have hTilt := finite_gaussian_tilt P Z hZ tilt F hF
  have hTilt' :
      (∫⁻ ω, ENNReal.ofReal (Real.exp
        (γ * Z ω i - γ ^ 2 / 2 * gaussianVariance P (fun ω => Z ω i))) * F (Z ω) ∂P) =
        ∫⁻ ω, F (fun k => Z ω k +
          γ * gaussianCovariance P (fun ω => Z ω k) (fun ω => Z ω i)) ∂P := by
    calc
      _ = ∫⁻ ω, ENNReal.ofReal (Real.exp
          ((∑ k, tilt k * Z ω k) -
            (∑ k, ∑ l, tilt k * gaussianCovariance P
              (fun ω => Z ω k) (fun ω => Z ω l) * tilt l) / 2)) *
            F (Z ω) ∂P := by
              apply lintegral_congr_ae
              exact ae_of_all _ (fun ω => by
                change ENNReal.ofReal (Real.exp
                    (γ * Z ω i - γ ^ 2 / 2 * gaussianVariance P
                      (fun ω' => Z ω' i))) * F (Z ω) = _
                have hweight : Real.exp
                    (γ * Z ω i - γ ^ 2 / 2 * gaussianVariance P
                      (fun ω' => Z ω' i)) = Real.exp
                    ((∑ k, tilt k * Z ω k) -
                      (∑ k, ∑ l, tilt k * gaussianCovariance P
                        (fun ω' => Z ω' k) (fun ω' => Z ω' l) * tilt l) / 2) := by
                  congr 1
                  rw [← hlin ω, hquad]
                  ring
                rw [hweight])
      _ = ∫⁻ ω, F (fun k => Z ω k +
            ∑ l, gaussianCovariance P (fun ω => Z ω k) (fun ω => Z ω l) * tilt l) ∂P := hTilt
      _ = ∫⁻ ω, F (fun k => Z ω k +
            γ * gaussianCovariance P (fun ω => Z ω k) (fun ω => Z ω i)) ∂P := by
              apply lintegral_congr_ae
              exact ae_of_all _ (fun ω => by
                apply congrArg F
                funext k
                rw [hshift k])
  obtain ⟨v, hmap, _, hvar⟩ := coordinate_mean_variance P Z hZ j
  have hWick := wick_exponential_integrable_expectation P Z hZ j γ
  have hWickNN : 0 ≤ᵐ[P] fun ω => Real.exp
      (γ * Z ω j - γ ^ 2 / 2 * gaussianVariance P (fun ω => Z ω j)) :=
    ae_of_all _ (fun ω => (Real.exp_pos _).le)
  have hWickLin : ∫⁻ ω, ENNReal.ofReal (Real.exp
      (γ * Z ω j - γ ^ 2 / 2 * gaussianVariance P (fun ω => Z ω j))) ∂P = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hWick.1 hWickNN, hWick.2]
    norm_num
  have hShiftPoint (ω : Ω) : F (fun k => Z ω k +
      γ * gaussianCovariance P (fun ω' => Z ω' k) (fun ω' => Z ω' i)) =
      ENNReal.ofReal (Real.exp (γ ^ 2 * gaussianCovariance P
        (fun ω' => Z ω' j) (fun ω' => Z ω' i))) *
        ENNReal.ofReal (Real.exp
          (γ * Z ω j - γ ^ 2 / 2 * gaussianVariance P (fun ω => Z ω j))) := by
    dsimp [F]
    rw [show γ * (Z ω j + γ * gaussianCovariance P
          (fun ω' => Z ω' j) (fun ω' => Z ω' i)) -
          γ ^ 2 / 2 * gaussianVariance P (fun ω' => Z ω' j) =
        γ ^ 2 * gaussianCovariance P (fun ω' => Z ω' j)
          (fun ω' => Z ω' i) +
          (γ * Z ω j - γ ^ 2 / 2 * gaussianVariance P (fun ω' => Z ω' j)) by
            rw [hvar]
            ring]
    rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_nonneg _)]
  calc
    _ = ∫⁻ ω, ENNReal.ofReal (Real.exp
          (γ * Z ω i - γ ^ 2 / 2 * gaussianVariance P (fun ω => Z ω i))) * F (Z ω) ∂P := by
            apply lintegral_congr_ae
            exact ae_of_all _ (fun ω => rfl)
    _ = ∫⁻ ω, F (fun k => Z ω k +
          γ * gaussianCovariance P (fun ω => Z ω k) (fun ω => Z ω i)) ∂P := hTilt'
    _ = ENNReal.ofReal (Real.exp (γ ^ 2 * gaussianCovariance P
          (fun ω => Z ω j) (fun ω => Z ω i))) := by
          calc
            _ = ∫⁻ ω, ENNReal.ofReal (Real.exp (γ ^ 2 * gaussianCovariance P
                  (fun ω' => Z ω' j) (fun ω' => Z ω' i))) *
                  ENNReal.ofReal (Real.exp
                    (γ * Z ω j - γ ^ 2 / 2 * gaussianVariance P
                      (fun ω' => Z ω' j))) ∂P := by
                    apply lintegral_congr_ae
                    exact ae_of_all _ hShiftPoint
            _ = ENNReal.ofReal (Real.exp (γ ^ 2 * gaussianCovariance P
                  (fun ω => Z ω j) (fun ω => Z ω i))) *
                  ∫⁻ ω, ENNReal.ofReal (Real.exp
                    (γ * Z ω j - γ ^ 2 / 2 * gaussianVariance P
                      (fun ω => Z ω j))) ∂P := by
                    rw [lintegral_const_mul'' _ hWick.1.aemeasurable.ennreal_ofReal]
            _ = _ := by rw [hWickLin, mul_one]

/-- The finite chaos second moment is the double sum of pairwise covariance weights. -/
theorem finiteChaosMoment_two_formula
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ) (hZ : IsCenteredJointlyGaussian P Z)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (γ : ℝ) :
    finiteChaosMoment P Z a γ 2 =
      ∑ i, ∑ j, ENNReal.ofReal (a i * a j * Real.exp
        (γ ^ 2 * gaussianCovariance P (fun ω => Z ω j) (fun ω => Z ω i))) := by
  classical
  let W : ι → Ω → ℝ := fun i ω => Real.exp
    (γ * Z ω i - γ ^ 2 / 2 * gaussianVariance P (fun ω => Z ω i))
  let w : ι → Ω → ℝ≥0∞ := fun i ω => ENNReal.ofReal (W i ω)
  let term : ι → ι → Ω → ℝ≥0∞ := fun i j ω =>
    ENNReal.ofReal (a i * W i ω) * ENNReal.ofReal (a j * W j ω)
  have hWick (i : ι) : Integrable (W i) P := by
    exact (wick_exponential_integrable_expectation P Z hZ i γ).1
  have hwMeas (i : ι) : AEMeasurable (w i) P :=
    (hWick i).aemeasurable.ennreal_ofReal
  have htermMeas (i j : ι) : AEMeasurable (term i j) P := by
    dsimp [term]
    exact ((hWick i).aemeasurable.const_mul (a i)).ennreal_ofReal.mul
      ((hWick j).aemeasurable.const_mul (a j)).ennreal_ofReal
  have htermPoint (i j : ι) (ω : Ω) :
      term i j ω = ENNReal.ofReal (a i * a j) * (w i ω * w j ω) := by
    dsimp [term, w, W]
    calc
      _ = ENNReal.ofReal (a i) * ENNReal.ofReal (W i ω) *
          (ENNReal.ofReal (a j) * ENNReal.ofReal (W j ω)) := by
            rw [ENNReal.ofReal_mul (ha i), ENNReal.ofReal_mul (ha j)]
      _ = ENNReal.ofReal (a i * a j) *
          (ENNReal.ofReal (W i ω) * ENNReal.ofReal (W j ω)) := by
            rw [ENNReal.ofReal_mul (ha i)]
            ac_rfl
  have htermIntegral (i j : ι) :
      (∫⁻ ω, term i j ω ∂P) = ENNReal.ofReal (a i * a j * Real.exp
        (γ ^ 2 * gaussianCovariance P (fun ω => Z ω j) (fun ω => Z ω i))) := by
    calc
      ∫⁻ ω, term i j ω ∂P =
          ENNReal.ofReal (a i * a j) * ∫⁻ ω, w i ω * w j ω ∂P := by
            rw [show (fun ω => term i j ω) = fun ω =>
              ENNReal.ofReal (a i * a j) * (w i ω * w j ω) by
                funext ω
                exact htermPoint i j ω]
            exact lintegral_const_mul'' _ ((hwMeas i).mul (hwMeas j))
      _ = ENNReal.ofReal (a i * a j) * ENNReal.ofReal (Real.exp
          (γ ^ 2 * gaussianCovariance P (fun ω => Z ω j) (fun ω => Z ω i))) := by
            rw [finite_wick_pair_second_moment P Z hZ i j γ]
      _ = ENNReal.ofReal (a i * a j * Real.exp
          (γ ^ 2 * gaussianCovariance P (fun ω => Z ω j) (fun ω => Z ω i))) := by
            rw [← ENNReal.ofReal_mul (mul_nonneg (ha i) (ha j))]
  have hpoint (ω : Ω) :
      ENNReal.rpow (ENNReal.ofReal (finiteChaosMass P Z a γ ω)) 2 =
        ∑ i, ∑ j, term i j ω := by
    calc
      _ = (ENNReal.ofReal (finiteChaosMass P Z a γ ω)) ^ (2 : ℕ) := by
        exact ENNReal.rpow_natCast (ENNReal.ofReal (finiteChaosMass P Z a γ ω)) 2
      _ = ∑ i, ∑ j, term i j ω := by
        have hmass : finiteChaosMass P Z a γ ω = ∑ i, a i * W i ω := by
          simp [finiteChaosMass, W]
        have hsum : ENNReal.ofReal (finiteChaosMass P Z a γ ω) =
            ∑ i, ENNReal.ofReal (a i * W i ω) := by
          rw [hmass, ENNReal.ofReal_sum_of_nonneg]
          intro i hi
          exact mul_nonneg (ha i) (Real.exp_nonneg _)
        rw [hsum, pow_two, Finset.sum_mul_sum]
  have hinnerMeas (i : ι) :
      AEMeasurable (fun ω => ∑ j, term i j ω) P :=
    Finset.aemeasurable_fun_sum Finset.univ (fun j hj => htermMeas i j)
  rw [finiteChaosMoment]
  calc
    ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (finiteChaosMass P Z a γ ω)) 2 ∂P =
        ∫⁻ ω, ∑ i, ∑ j, term i j ω ∂P := by
          apply lintegral_congr_ae
          exact ae_of_all _ hpoint
    _ = ∑ i, ∫⁻ ω, ∑ j, term i j ω ∂P := by
          exact lintegral_finsetSum' Finset.univ (fun i hi => hinnerMeas i)
    _ = ∑ i, ∑ j, ∫⁻ ω, term i j ω ∂P := by
          apply Finset.sum_congr rfl
          intro i hi
          exact lintegral_finsetSum' Finset.univ (fun j hj => htermMeas i j)
    _ = ∑ i, ∑ j, ENNReal.ofReal (a i * a j * Real.exp
          (γ ^ 2 * gaussianCovariance P (fun ω => Z ω j) (fun ω => Z ω i))) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          exact htermIntegral i j

/-- The finite Kahane power comparison at `p = 2` follows termwise from the pair moment formula. -/
theorem kahane_finite_power_two
    {ΩX ΩY ι : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [Fintype ι]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (hX : IsCenteredJointlyGaussian PX X) (hY : IsCenteredJointlyGaussian PY Y)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (γ : ℝ)
    (hcov : ∀ i j, gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) ≤
      gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j)) :
    finiteChaosMoment PX X a γ 2 ≤ finiteChaosMoment PY Y a γ 2 := by
  rw [finiteChaosMoment_two_formula PX X hX a ha γ,
    finiteChaosMoment_two_formula PY Y hY a ha γ]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (ha i) (ha j))
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (hcov j i) (sq_nonneg γ)

end DOZZ.Proofs

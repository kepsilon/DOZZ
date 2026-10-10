/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteGaussianTilt
public import DOZZ.Statements.GMC.FiniteChaosMoment
public import DOZZ.GMC.FiniteChaosNegativePower
public import DOZZ.GMC.FiniteChaosPowerUnitInterval
public import DOZZ.GMC.FiniteChaosSecondMoment

/-! A size-bias recursion for positive finite-chaos powers, using finite Gaussian tilting. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Distributions NNReal

namespace DOZZ.Proofs

private theorem gaussianCovariance_comm_local
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X Y : Ω → ℝ) :
    DOZZ.gaussianCovariance P X Y = DOZZ.gaussianCovariance P Y X := by
  unfold DOZZ.gaussianCovariance
  apply integral_congr_ae
  exact ae_of_all P (fun ω => by ring)

/-- Multiplication by the chaos mass raises the exponent by one. Each summand is then removed
from the Wick exponential by a Cameron--Martin shift, leaving a deterministic change of weights. -/
theorem finiteChaosMoment_succ_tilt_formula
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ)
    (hZ : DOZZ.IsCenteredJointlyGaussian P Z)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (γ q : ℝ) (hq : 0 ≤ q) :
    DOZZ.finiteChaosMoment P Z a γ (q + 1) =
      ∑ i, ENNReal.ofReal (a i) *
        DOZZ.finiteChaosMoment P Z
          (fun j => a j * Real.exp (γ ^ 2 *
            DOZZ.gaussianCovariance P (fun ω => Z ω j) (fun ω => Z ω i))) γ q := by
  classical
  let mass (b : ι → ℝ) (z : ι → ℝ) : ℝ :=
    ∑ j, b j * Real.exp (γ * z j - γ ^ 2 / 2 *
      DOZZ.gaussianVariance P (fun ω => Z ω j))
  let wt (i : ι) (ω : Ω) : ℝ := a i * Real.exp
    (γ * Z ω i - γ ^ 2 / 2 * DOZZ.gaussianVariance P (fun ω => Z ω i))
  let tilt (i : ι) : ι → ℝ := Pi.single i γ
  let shiftedWeight (i : ι) (j : ι) : ℝ := a j * Real.exp
    (γ ^ 2 * DOZZ.gaussianCovariance P (fun ω => Z ω j) (fun ω => Z ω i))
  let G (b : ι → ℝ) : (ι → ℝ) → ℝ≥0∞ := fun z =>
    ENNReal.rpow (ENNReal.ofReal (mass b z)) q
  have hmass_nonneg (b : ι → ℝ) (hb : ∀ j, 0 ≤ b j) (z : ι → ℝ) :
      0 ≤ mass b z := by
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (hb j) (Real.exp_nonneg _)
  have hMassMeas (b : ι → ℝ) : Measurable (mass b) := by
    dsimp [mass]
    fun_prop
  have hGMeas (b : ι → ℝ) : Measurable (G b) := by
    exact ENNReal.continuous_rpow_const.measurable.comp
      (ENNReal.measurable_ofReal.comp (hMassMeas b))
  have hwtMeas (i : ι) : AEMeasurable (fun ω => ENNReal.ofReal (wt i ω)) P := by
    have harg : AEMeasurable (fun ω => γ * Z ω i - γ ^ 2 / 2 *
        DOZZ.gaussianVariance P (fun ω => Z ω i)) P :=
      (hZ.2.1 i).const_mul γ |>.sub_const _
    exact (Real.measurable_exp.comp_aemeasurable harg).const_mul (a i) |>.ennreal_ofReal
  have hmassAEMeas : AEMeasurable
      (fun ω => ENNReal.ofReal (DOZZ.finiteChaosMass P Z a γ ω)) P := by
    have hterm (i : ι) : AEMeasurable
        (fun ω => ENNReal.ofReal (wt i ω)) P := by
      exact hwtMeas i
    have hpoint (ω : Ω) :
        ENNReal.ofReal (DOZZ.finiteChaosMass P Z a γ ω) =
          ∑ i, ENNReal.ofReal (wt i ω) := by
      rw [DOZZ.finiteChaosMass,
        ENNReal.ofReal_sum_of_nonneg (fun i hi => mul_nonneg (ha i) (Real.exp_nonneg _))]
    have hfun : (fun ω => ENNReal.ofReal (DOZZ.finiteChaosMass P Z a γ ω)) =
        fun ω => ∑ i, ENNReal.ofReal (wt i ω) := by
      funext ω
      exact hpoint ω
    rw [hfun]
    exact Finset.aemeasurable_fun_sum Finset.univ (fun i hi => hterm i)
  have hpowMeas : AEMeasurable
      (fun ω => ENNReal.rpow
        (ENNReal.ofReal (DOZZ.finiteChaosMass P Z a γ ω)) q) P :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hmassAEMeas
  have htermMeas (i : ι) : AEMeasurable
      (fun ω => ENNReal.ofReal (wt i ω) *
        ENNReal.rpow (ENNReal.ofReal (DOZZ.finiteChaosMass P Z a γ ω)) q) P :=
    hwtMeas i |>.mul hpowMeas
  have hmomentPoint (ω : Ω) :
      ENNReal.rpow (ENNReal.ofReal (DOZZ.finiteChaosMass P Z a γ ω)) (q + 1) =
        ∑ i, ENNReal.ofReal (wt i ω) *
          ENNReal.rpow (ENNReal.ofReal (DOZZ.finiteChaosMass P Z a γ ω)) q := by
    have hmass : DOZZ.finiteChaosMass P Z a γ ω = ∑ i, wt i ω := by
      simp [DOZZ.finiteChaosMass, wt]
    have hterms : ∀ i ∈ Finset.univ, 0 ≤ wt i ω := by
      intro i hi
      exact mul_nonneg (ha i) (Real.exp_nonneg _)
    have hpowone : ENNReal.rpow
        (ENNReal.ofReal (DOZZ.finiteChaosMass P Z a γ ω)) 1 =
          ENNReal.ofReal (DOZZ.finiteChaosMass P Z a γ ω) :=
      ENNReal.rpow_one _
    calc
      ENNReal.rpow (ENNReal.ofReal (DOZZ.finiteChaosMass P Z a γ ω)) (q + 1) =
          ENNReal.rpow (ENNReal.ofReal (DOZZ.finiteChaosMass P Z a γ ω)) q *
            ENNReal.rpow (ENNReal.ofReal (DOZZ.finiteChaosMass P Z a γ ω)) 1 :=
        ENNReal.rpow_add_of_nonneg q 1 hq (by norm_num)
      _ = _ := by
        rw [hpowone, hmass, ENNReal.ofReal_sum_of_nonneg hterms,
          mul_comm, Finset.sum_mul]
  have hsum :
      DOZZ.finiteChaosMoment P Z a γ (q + 1) =
        ∑ i, ∫⁻ ω, ENNReal.ofReal (wt i ω) *
          ENNReal.rpow (ENNReal.ofReal (DOZZ.finiteChaosMass P Z a γ ω)) q ∂P := by
    rw [DOZZ.finiteChaosMoment]
    calc
      _ = ∫⁻ ω, ∑ i, ENNReal.ofReal (wt i ω) *
            ENNReal.rpow (ENNReal.ofReal (DOZZ.finiteChaosMass P Z a γ ω)) q ∂P := by
              apply lintegral_congr_ae
              exact ae_of_all P hmomentPoint
      _ = ∑ i, ∫⁻ ω, ENNReal.ofReal (wt i ω) *
            ENNReal.rpow (ENNReal.ofReal (DOZZ.finiteChaosMass P Z a γ ω)) q ∂P :=
              lintegral_finsetSum' Finset.univ (fun i hi => htermMeas i)
  have hterm (i : ι) :
      ∫⁻ ω, ENNReal.ofReal (wt i ω) *
        ENNReal.rpow (ENNReal.ofReal (DOZZ.finiteChaosMass P Z a γ ω)) q ∂P =
      ENNReal.ofReal (a i) *
        DOZZ.finiteChaosMoment P Z (shiftedWeight i) γ q := by
    let F : (ι → ℝ) → ℝ≥0∞ := G a
    have hF : Measurable F := hGMeas a
    have htilt := finite_gaussian_tilt P Z hZ (tilt i) F hF
    have hlog (ω : Ω) :
        (∑ j, tilt i j * Z ω j) -
          (∑ j, ∑ k, tilt i j *
            DOZZ.gaussianCovariance P (fun ω => Z ω j) (fun ω => Z ω k) * tilt i k) / 2 =
        γ * Z ω i - γ ^ 2 / 2 *
          DOZZ.gaussianVariance P (fun ω => Z ω i) := by
      simp [tilt, DOZZ.gaussianVariance, DOZZ.gaussianCovariance, Pi.single_apply]
      ring
    have hshift (ω : Ω) :
        mass a (fun j => Z ω j +
          ∑ k, DOZZ.gaussianCovariance P (fun ω => Z ω j) (fun ω => Z ω k) * tilt i k) =
        mass (shiftedWeight i) (fun j => Z ω j) := by
      simp only [mass, shiftedWeight, tilt]
      apply Finset.sum_congr rfl
      intro j hj
      simp [Pi.single_apply]
      rw [show γ * (Z ω j +
          DOZZ.gaussianCovariance P (fun ω => Z ω j) (fun ω => Z ω i) * γ) -
          γ ^ 2 / 2 * DOZZ.gaussianVariance P (fun ω => Z ω j) =
        γ ^ 2 * DOZZ.gaussianCovariance P (fun ω => Z ω j) (fun ω => Z ω i) +
          (γ * Z ω j - γ ^ 2 / 2 *
            DOZZ.gaussianVariance P (fun ω => Z ω j)) by ring,
        Real.exp_add]
      ring
    have htiltApplied :
        (∫⁻ ω, ENNReal.ofReal (Real.exp
          (γ * Z ω i - γ ^ 2 / 2 *
            DOZZ.gaussianVariance P (fun ω => Z ω i))) * F (Z ω) ∂P) =
        DOZZ.finiteChaosMoment P Z (shiftedWeight i) γ q := by
      calc
        _ = ∫⁻ ω, ENNReal.ofReal (Real.exp
              ((∑ j, tilt i j * Z ω j) -
                (∑ j, ∑ k, tilt i j *
                  DOZZ.gaussianCovariance P (fun ω => Z ω j)
              (fun ω => Z ω k) * tilt i k) / 2)) * F (Z ω) ∂P := by
              apply lintegral_congr_ae
              exact ae_of_all P fun ω => by
                change ENNReal.ofReal (Real.exp
                  (γ * Z ω i - γ ^ 2 / 2 *
                    DOZZ.gaussianVariance P (fun ω => Z ω i))) * F (Z ω) =
                  ENNReal.ofReal (Real.exp
                    ((∑ j, tilt i j * Z ω j) -
                      (∑ j, ∑ k, tilt i j *
                        DOZZ.gaussianCovariance P (fun ω => Z ω j)
                          (fun ω => Z ω k) * tilt i k) / 2)) * F (Z ω)
                rw [← hlog ω]
        _ = ∫⁻ ω, F (fun j => Z ω j +
              ∑ k, DOZZ.gaussianCovariance P (fun ω => Z ω j)
                (fun ω => Z ω k) * tilt i k) ∂P := htilt
        _ = DOZZ.finiteChaosMoment P Z (shiftedWeight i) γ q := by
              rw [DOZZ.finiteChaosMoment]
              apply lintegral_congr_ae
              filter_upwards [] with ω
              change G a (fun j => Z ω j +
                ∑ k, DOZZ.gaussianCovariance P (fun ω => Z ω j)
                  (fun ω => Z ω k) * tilt i k) = _
              simp [G, mass, hshift ω, DOZZ.finiteChaosMass]
    have hfactor (ω : Ω) : ENNReal.ofReal (wt i ω) =
        ENNReal.ofReal (a i) * ENNReal.ofReal (Real.exp
          (γ * Z ω i - γ ^ 2 / 2 *
            DOZZ.gaussianVariance P (fun ω => Z ω i))) := by
      dsimp [wt]
      rw [ENNReal.ofReal_mul (ha i)]
    have hExpMeas : AEMeasurable (fun ω => ENNReal.ofReal (Real.exp
        (γ * Z ω i - γ ^ 2 / 2 *
          DOZZ.gaussianVariance P (fun ω => Z ω i)))) P := by
      have harg : AEMeasurable (fun ω => γ * Z ω i - γ ^ 2 / 2 *
          DOZZ.gaussianVariance P (fun ω => Z ω i)) P :=
        (hZ.2.1 i).const_mul γ |>.sub_const _
      exact (Real.measurable_exp.comp_aemeasurable harg).ennreal_ofReal
    calc
      _ = ∫⁻ ω, ENNReal.ofReal (a i) *
          (ENNReal.ofReal (Real.exp
            (γ * Z ω i - γ ^ 2 / 2 *
              DOZZ.gaussianVariance P (fun ω => Z ω i))) *
            ENNReal.rpow (ENNReal.ofReal (DOZZ.finiteChaosMass P Z a γ ω)) q) ∂P := by
          apply lintegral_congr_ae
          exact ae_of_all P fun ω => by
            simp only [hfactor]
            ac_rfl
      _ = ENNReal.ofReal (a i) *
          ∫⁻ ω, ENNReal.ofReal (Real.exp
            (γ * Z ω i - γ ^ 2 / 2 *
              DOZZ.gaussianVariance P (fun ω => Z ω i))) *
            ENNReal.rpow (ENNReal.ofReal (DOZZ.finiteChaosMass P Z a γ ω)) q ∂P := by
          exact lintegral_const_mul'' (ENNReal.ofReal (a i))
            (hExpMeas.mul hpowMeas)
      _ = ENNReal.ofReal (a i) * DOZZ.finiteChaosMoment P Z (shiftedWeight i) γ q := by
          rw [← htiltApplied]
          rfl

  rw [hsum]
  apply Finset.sum_congr rfl
  intro i hi
  exact hterm i

/-- Increasing the nonnegative coefficient vector can only increase a nonnegative chaos moment. -/
theorem finiteChaosMoment_mono_weights
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ) (a b : ι → ℝ)
    (hab : ∀ i, a i ≤ b i) (γ p : ℝ) (hp : 0 ≤ p) :
    DOZZ.finiteChaosMoment P Z a γ p ≤ DOZZ.finiteChaosMoment P Z b γ p := by
  apply lintegral_mono
  intro ω
  apply ENNReal.rpow_le_rpow
  · apply ENNReal.ofReal_le_ofReal
    apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_right (hab i) (Real.exp_nonneg _)
  · exact hp

/-- Every real power at least one satisfies the finite Kahane comparison. The interval `1 ≤ p ≤ 2`
is the resolvent base case; each size-bias step lowers the exponent by one and changes the
coefficients by the covariance tilt, whose order follows directly from covariance domination. -/
theorem kahane_finite_power_ge_one_intervals
    {ΩX ΩY ι : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [Fintype ι]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (hX : DOZZ.IsCenteredJointlyGaussian PX X)
    (hY : DOZZ.IsCenteredJointlyGaussian PY Y)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (γ : ℝ)
    (hcov : ∀ i j,
      DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) ≤
        DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j)) :
    ∀ n : ℕ, ∀ p : ℝ, (n : ℝ) + 1 ≤ p → p ≤ (n : ℝ) + 2 →
      DOZZ.finiteChaosMoment PX X a γ p ≤ DOZZ.finiteChaosMoment PY Y a γ p := by
  classical
  intro n
  revert a ha
  induction n with
  | zero =>
      intro a ha p hpLo hpHi
      have hpLo0 : (1 : ℝ) ≤ p := by simpa using hpLo
      have hpHi0 : p ≤ (2 : ℝ) := by simpa using hpHi
      by_cases hp1 : p = 1
      · rw [hp1]
        exact le_of_eq (finiteChaosMoment_one_eq PX PY X Y hX hY a ha γ)
      by_cases hp2 : p = 2
      · rw [hp2]
        exact kahane_finite_power_two PX PY X Y hX hY a ha γ hcov
      have hpLo' : 1 < p := lt_of_le_of_ne hpLo0 (Ne.symm hp1)
      have hpHi' : p < 2 := lt_of_le_of_ne hpHi0 hp2
      exact kahane_finite_power_convex_one_two PX PY X Y hX hY a ha γ p
        ⟨hpLo', hpHi'⟩ hcov
  | succ n ih =>
      intro a ha p hpLo hpHi
      let q : ℝ := p - 1
      have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by simp
      rw [hcast] at hpLo hpHi
      have hpLo' : (n : ℝ) + 2 ≤ p := by linarith [hpLo]
      have hpHi' : p ≤ (n : ℝ) + 3 := by linarith [hpHi]
      have hqLo : (n : ℝ) + 1 ≤ q := by dsimp [q]; linarith
      have hqHi : q ≤ (n : ℝ) + 2 := by dsimp [q]; linarith
      have hqNonneg : 0 ≤ q := by linarith [hqLo]
      let bX : ι → ι → ℝ := fun i j => a j * Real.exp
        (γ ^ 2 * DOZZ.gaussianCovariance PX (fun ω => X ω j) (fun ω => X ω i))
      let bY : ι → ι → ℝ := fun i j => a j * Real.exp
        (γ ^ 2 * DOZZ.gaussianCovariance PY (fun ω => Y ω j) (fun ω => Y ω i))
      have hbX : ∀ i j, 0 ≤ bX i j := by
        intro i j
        exact mul_nonneg (ha j) (Real.exp_nonneg _)
      have hbY : ∀ i j, 0 ≤ bY i j := by
        intro i j
        exact mul_nonneg (ha j) (Real.exp_nonneg _)
      have hweight : ∀ i j, bX i j ≤ bY i j := by
        intro i j
        dsimp [bX, bY]
        apply mul_le_mul_of_nonneg_left _ (ha j)
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left (hcov j i) (sq_nonneg γ)
      have hpEq : q + 1 = p := by dsimp [q]; ring
      have hrecX := finiteChaosMoment_succ_tilt_formula PX X hX a ha γ q hqNonneg
      have hrecY := finiteChaosMoment_succ_tilt_formula PY Y hY a ha γ q hqNonneg
      have hih (i : ι) :
          DOZZ.finiteChaosMoment PX X (bY i) γ q ≤
            DOZZ.finiteChaosMoment PY Y (bY i) γ q := by
        exact ih (bY i) (hbY i) q hqLo hqHi
      rw [← hpEq, hrecX, hrecY]
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ ENNReal.ofReal (a i))
      calc
          DOZZ.finiteChaosMoment PX X (bX i) γ q ≤
            DOZZ.finiteChaosMoment PX X (bY i) γ q :=
          finiteChaosMoment_mono_weights PX X (bX i) (bY i)
            (hweight i) γ q hqNonneg
        _ ≤ DOZZ.finiteChaosMoment PY Y (bY i) γ q := hih i

/-- Full finite convex-power comparison, including negative real powers and every power at least
one. Positive powers are covered by the unit interval base and covariance size-bias recursion. -/
theorem kahane_finite_power_convex
    {ΩX ΩY ι : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY] [Fintype ι]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (hX : DOZZ.IsCenteredJointlyGaussian PX X)
    (hY : DOZZ.IsCenteredJointlyGaussian PY Y)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (γ p : ℝ)
    (hp : p ≤ 0 ∨ 1 ≤ p)
    (hcov : ∀ i j,
      DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) ≤
        DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j)) :
    DOZZ.finiteChaosMoment PX X a γ p ≤ DOZZ.finiteChaosMoment PY Y a γ p := by
  rcases hp with hp | hp
  · exact kahane_finite_power_nonpos PX PY X Y hX hY a ha γ p hp hcov
  · let N : ℕ := Nat.floor p
    have hfloor : (N : ℝ) ≤ p := by
      dsimp [N]
      exact Nat.floor_le (by linarith)
    have hfloor_lt : p < (N : ℝ) + 1 := by
      dsimp [N]
      exact Nat.lt_floor_add_one p
    have hNpos : 1 ≤ N := by
      by_contra hN
      have hNzero : N = 0 := by omega
      have hNzeroR : (N : ℝ) = 0 := by exact_mod_cast hNzero
      rw [hNzeroR] at hfloor_lt
      linarith
    let n : ℕ := N - 1
    have hncast : (n : ℝ) + 1 = (N : ℝ) := by
      dsimp [n]
      rw [Nat.cast_sub hNpos]
      push_cast
      ring
    have hnlo : (n : ℝ) + 1 ≤ p := by rw [hncast]; exact hfloor
    have hnhi : p ≤ (n : ℝ) + 2 := by
      have htop : (N : ℝ) + 1 = (n : ℝ) + 2 := by rw [← hncast]; ring
      rw [← htop]
      exact hfloor_lt.le
    exact kahane_finite_power_ge_one_intervals PX PY X Y hX hY a ha γ hcov
      n p hnlo hnhi


end DOZZ.Proofs

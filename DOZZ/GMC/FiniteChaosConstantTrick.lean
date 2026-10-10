/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteGaussianCommonScalar
public import DOZZ.GMC.FiniteChaosNegativePower
public import DOZZ.GMC.FiniteChaosPowerUnitInterval
public import DOZZ.GMC.FiniteChaosNaturalMoments
public import DOZZ.GMC.FiniteChaosSecondMoment

/-! Bounded covariance-discrepancy comparisons from the common-scalar moment identity. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- The two-sided finite constant trick for nonpositive powers. The comparison is valid for
extended moments, including divergent negative moments and zero weights. -/
theorem kahane_finite_constant_trick_nonpos
    {ΩX ΩY : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    {ι : Type*} [Fintype ι]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (hX : DOZZ.IsCenteredJointlyGaussian PX X)
    (hY : DOZZ.IsCenteredJointlyGaussian PY Y)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (γ C p : ℝ)
    (hC : 0 ≤ C) (hp : p ≤ 0)
    (hcov : ∀ i j,
      |DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) -
        DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j)| ≤ C) :
    ENNReal.ofReal (Real.exp (-(γ ^ 2 * C / 2 * (p ^ 2 - p)))) *
        DOZZ.finiteChaosMoment PY Y a γ p ≤ DOZZ.finiteChaosMoment PX X a γ p ∧
      DOZZ.finiteChaosMoment PX X a γ p ≤
        ENNReal.ofReal (Real.exp (γ ^ 2 * C / 2 * (p ^ 2 - p))) *
          DOZZ.finiteChaosMoment PY Y a γ p := by
  classical
  let c : ℝ := Real.sqrt C
  let A : ℝ := γ ^ 2 * C / 2 * (p ^ 2 - p)
  let Yc : ΩY × ℝ → ι → ℝ := fun ω i => Y ω.1 i + c * ω.2
  let Xc : ΩX × ℝ → ι → ℝ := fun ω i => X ω.1 i + c * ω.2
  have hcSq : c ^ 2 = C := by
    dsimp [c]
    exact Real.sq_sqrt hC
  have hYc : DOZZ.IsCenteredJointlyGaussian (PY.prod (gaussianReal 0 1)) Yc := by
    simpa [Yc] using independent_common_scalar_add_isCenteredJointlyGaussian PY Y hY c
  have hXc : DOZZ.IsCenteredJointlyGaussian (PX.prod (gaussianReal 0 1)) Xc := by
    simpa [Xc] using independent_common_scalar_add_isCenteredJointlyGaussian PX X hX c
  have hcovXleYc (i j : ι) :
      DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) ≤
        DOZZ.gaussianCovariance (PY.prod (gaussianReal 0 1))
          (fun ω => Yc ω i) (fun ω => Yc ω j) := by
    have hupper := (abs_le.mp (hcov i j)).2
    calc
      DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) ≤
          DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j) + C := by linarith
      _ = DOZZ.gaussianCovariance (PY.prod (gaussianReal 0 1))
          (fun ω => Yc ω i) (fun ω => Yc ω j) := by
            symm
            simpa [Yc, hcSq] using
              gaussianCovariance_independent_common_scalar_add PY Y hY c i j
  have hcovYleXc (i j : ι) :
      DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j) ≤
        DOZZ.gaussianCovariance (PX.prod (gaussianReal 0 1))
          (fun ω => Xc ω i) (fun ω => Xc ω j) := by
    have hlower := (abs_le.mp (hcov i j)).1
    calc
      DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j) ≤
          DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) + C := by linarith
      _ = DOZZ.gaussianCovariance (PX.prod (gaussianReal 0 1))
          (fun ω => Xc ω i) (fun ω => Xc ω j) := by
            symm
            simpa [Xc, hcSq] using
              gaussianCovariance_independent_common_scalar_add PX X hX c i j
  let K : ℝ≥0∞ := ENNReal.ofReal (Real.exp A)
  let L : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-A))
  have hYfactor : DOZZ.finiteChaosMoment (PY.prod (gaussianReal 0 1)) Yc a γ p =
      K * DOZZ.finiteChaosMoment PY Y a γ p := by
    simpa [K, Yc, A, hcSq] using
      finiteChaosMoment_independent_common_scalar_factor PY Y hY a ha γ c p
  have hXfactor : DOZZ.finiteChaosMoment (PX.prod (gaussianReal 0 1)) Xc a γ p =
      K * DOZZ.finiteChaosMoment PX X a γ p := by
    simpa [K, Xc, A, hcSq] using
      finiteChaosMoment_independent_common_scalar_factor PX X hX a ha γ c p
  have hXleYc : DOZZ.finiteChaosMoment PX X a γ p ≤
      DOZZ.finiteChaosMoment (PY.prod (gaussianReal 0 1)) Yc a γ p :=
    kahane_finite_power_nonpos PX (PY.prod (gaussianReal 0 1)) X Yc hX hYc a ha γ p hp hcovXleYc
  have hYleXc : DOZZ.finiteChaosMoment PY Y a γ p ≤
      DOZZ.finiteChaosMoment (PX.prod (gaussianReal 0 1)) Xc a γ p :=
    kahane_finite_power_nonpos PY (PX.prod (gaussianReal 0 1)) Y Xc hY hXc a ha γ p hp hcovYleXc
  have hLK : L * K = 1 := by
    dsimp [L, K]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    rw [show Real.exp (-A) * Real.exp A = 1 by rw [← Real.exp_add]; simp]
    simp
  constructor
  · have hscaled := calc
        L * DOZZ.finiteChaosMoment PY Y a γ p ≤
            L * DOZZ.finiteChaosMoment (PX.prod (gaussianReal 0 1)) Xc a γ p := by
              gcongr
      _ = L * (K * DOZZ.finiteChaosMoment PX X a γ p) := by rw [hXfactor]
      _ = DOZZ.finiteChaosMoment PX X a γ p := by
            calc
              L * (K * DOZZ.finiteChaosMoment PX X a γ p) =
                  (L * K) * DOZZ.finiteChaosMoment PX X a γ p := by ac_rfl
              _ = DOZZ.finiteChaosMoment PX X a γ p := by rw [hLK]; simp
    simpa [L, A] using hscaled
  · simpa [K, A] using hXleYc.trans_eq hYfactor

/-- The two-sided finite constant trick for concave powers `0 < p < 1`. -/
theorem kahane_finite_constant_trick_subunit
    {ΩX ΩY : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    {ι : Type*} [Fintype ι]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (hX : DOZZ.IsCenteredJointlyGaussian PX X)
    (hY : DOZZ.IsCenteredJointlyGaussian PY Y)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (γ C p : ℝ)
    (hC : 0 ≤ C) (hp : 0 < p ∧ p < 1)
    (hcov : ∀ i j,
      |DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) -
        DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j)| ≤ C) :
    ENNReal.ofReal (Real.exp (-(γ ^ 2 * C / 2 * (p - p ^ 2)))) *
        DOZZ.finiteChaosMoment PY Y a γ p ≤ DOZZ.finiteChaosMoment PX X a γ p ∧
      DOZZ.finiteChaosMoment PX X a γ p ≤
        ENNReal.ofReal (Real.exp (γ ^ 2 * C / 2 * (p - p ^ 2))) *
          DOZZ.finiteChaosMoment PY Y a γ p := by
  classical
  let c : ℝ := Real.sqrt C
  let A : ℝ := γ ^ 2 * C / 2 * (p - p ^ 2)
  let Yc : ΩY × ℝ → ι → ℝ := fun ω i => Y ω.1 i + c * ω.2
  let Xc : ΩX × ℝ → ι → ℝ := fun ω i => X ω.1 i + c * ω.2
  have hcSq : c ^ 2 = C := by
    dsimp [c]
    exact Real.sq_sqrt hC
  have hYc : DOZZ.IsCenteredJointlyGaussian (PY.prod (gaussianReal 0 1)) Yc := by
    simpa [Yc] using independent_common_scalar_add_isCenteredJointlyGaussian PY Y hY c
  have hXc : DOZZ.IsCenteredJointlyGaussian (PX.prod (gaussianReal 0 1)) Xc := by
    simpa [Xc] using independent_common_scalar_add_isCenteredJointlyGaussian PX X hX c
  have hcovXleYc (i j : ι) :
      DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) ≤
        DOZZ.gaussianCovariance (PY.prod (gaussianReal 0 1))
          (fun ω => Yc ω i) (fun ω => Yc ω j) := by
    have hupper := (abs_le.mp (hcov i j)).2
    calc
      DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) ≤
          DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j) + C := by linarith
      _ = DOZZ.gaussianCovariance (PY.prod (gaussianReal 0 1))
          (fun ω => Yc ω i) (fun ω => Yc ω j) := by
            symm
            simpa [Yc, hcSq] using
              gaussianCovariance_independent_common_scalar_add PY Y hY c i j
  have hcovYleXc (i j : ι) :
      DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j) ≤
        DOZZ.gaussianCovariance (PX.prod (gaussianReal 0 1))
          (fun ω => Xc ω i) (fun ω => Xc ω j) := by
    have hlower := (abs_le.mp (hcov i j)).1
    calc
      DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j) ≤
          DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) + C := by linarith
      _ = DOZZ.gaussianCovariance (PX.prod (gaussianReal 0 1))
          (fun ω => Xc ω i) (fun ω => Xc ω j) := by
            symm
            simpa [Xc, hcSq] using
              gaussianCovariance_independent_common_scalar_add PX X hX c i j
  let K : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-A))
  let L : ℝ≥0∞ := ENNReal.ofReal (Real.exp A)
  have hExp : γ ^ 2 * c ^ 2 / 2 * (p ^ 2 - p) = -A := by
    rw [hcSq]
    dsimp [A]
    ring
  have hYfactor : DOZZ.finiteChaosMoment (PY.prod (gaussianReal 0 1)) Yc a γ p =
      K * DOZZ.finiteChaosMoment PY Y a γ p := by
    simpa [K, Yc, hExp] using
      finiteChaosMoment_independent_common_scalar_factor PY Y hY a ha γ c p
  have hXfactor : DOZZ.finiteChaosMoment (PX.prod (gaussianReal 0 1)) Xc a γ p =
      K * DOZZ.finiteChaosMoment PX X a γ p := by
    simpa [K, Xc, hExp] using
      finiteChaosMoment_independent_common_scalar_factor PX X hX a ha γ c p
  have hYcLeX : DOZZ.finiteChaosMoment (PY.prod (gaussianReal 0 1)) Yc a γ p ≤
      DOZZ.finiteChaosMoment PX X a γ p :=
    kahane_finite_power_concave PX (PY.prod (gaussianReal 0 1)) X Yc hX hYc a ha γ p hp
      hcovXleYc
  have hXcLeY : DOZZ.finiteChaosMoment (PX.prod (gaussianReal 0 1)) Xc a γ p ≤
      DOZZ.finiteChaosMoment PY Y a γ p :=
    kahane_finite_power_concave PY (PX.prod (gaussianReal 0 1)) Y Xc hY hXc a ha γ p hp
      hcovYleXc
  have hLK : L * K = 1 := by
    dsimp [L, K]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    rw [show Real.exp A * Real.exp (-A) = 1 by rw [← Real.exp_add]; simp]
    simp
  constructor
  · calc
      K * DOZZ.finiteChaosMoment PY Y a γ p =
          DOZZ.finiteChaosMoment (PY.prod (gaussianReal 0 1)) Yc a γ p := hYfactor.symm
      _ ≤ DOZZ.finiteChaosMoment PX X a γ p := hYcLeX
  · have hpre : K * DOZZ.finiteChaosMoment PX X a γ p ≤
        DOZZ.finiteChaosMoment PY Y a γ p := by
      calc
        K * DOZZ.finiteChaosMoment PX X a γ p =
            DOZZ.finiteChaosMoment (PX.prod (gaussianReal 0 1)) Xc a γ p := hXfactor.symm
        _ ≤ DOZZ.finiteChaosMoment PY Y a γ p := hXcLeY
    calc
      DOZZ.finiteChaosMoment PX X a γ p =
          L * (K * DOZZ.finiteChaosMoment PX X a γ p) := by
            rw [← mul_assoc, hLK]
            simp
      _ ≤ L * DOZZ.finiteChaosMoment PY Y a γ p := by gcongr

/-- The finite constant-trick comparison for concave powers. -/
theorem kahane_finite_constant_trick_concave
    {ΩX ΩY : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    {ι : Type*} [Fintype ι]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (hX : DOZZ.IsCenteredJointlyGaussian PX X)
    (hY : DOZZ.IsCenteredJointlyGaussian PY Y)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (γ C p : ℝ)
    (hC : 0 ≤ C) (hp : 0 < p ∧ p < 1)
    (hcov : ∀ i j,
      |DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) -
        DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j)| ≤ C) :
    ENNReal.ofReal (Real.exp (-(γ ^ 2 * C / 2 * (p - p ^ 2)))) *
        DOZZ.finiteChaosMoment PY Y a γ p ≤ DOZZ.finiteChaosMoment PX X a γ p ∧
      DOZZ.finiteChaosMoment PX X a γ p ≤
        ENNReal.ofReal (Real.exp (γ ^ 2 * C / 2 * (p - p ^ 2))) *
          DOZZ.finiteChaosMoment PY Y a γ p :=
  kahane_finite_constant_trick_subunit PX PY X Y hX hY a ha γ C p hC hp hcov

/-- The two-sided finite constant trick for convex powers in the interval `1 ≤ p ≤ 2`. -/
theorem kahane_finite_constant_trick_convex_one_two
    {ΩX ΩY : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    {ι : Type*} [Fintype ι]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (hX : DOZZ.IsCenteredJointlyGaussian PX X)
    (hY : DOZZ.IsCenteredJointlyGaussian PY Y)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (γ C p : ℝ)
    (hC : 0 ≤ C) (hp : 1 ≤ p ∧ p ≤ 2)
    (hcov : ∀ i j,
      |DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) -
        DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j)| ≤ C) :
    ENNReal.ofReal (Real.exp (-(γ ^ 2 * C / 2 * (p ^ 2 - p)))) *
        DOZZ.finiteChaosMoment PY Y a γ p ≤ DOZZ.finiteChaosMoment PX X a γ p ∧
      DOZZ.finiteChaosMoment PX X a γ p ≤
        ENNReal.ofReal (Real.exp (γ ^ 2 * C / 2 * (p ^ 2 - p))) *
          DOZZ.finiteChaosMoment PY Y a γ p := by
  classical
  let c : ℝ := Real.sqrt C
  let A : ℝ := γ ^ 2 * C / 2 * (p ^ 2 - p)
  let Yc : ΩY × ℝ → ι → ℝ := fun ω i => Y ω.1 i + c * ω.2
  let Xc : ΩX × ℝ → ι → ℝ := fun ω i => X ω.1 i + c * ω.2
  have hcSq : c ^ 2 = C := by
    dsimp [c]
    exact Real.sq_sqrt hC
  have hYc : DOZZ.IsCenteredJointlyGaussian (PY.prod (gaussianReal 0 1)) Yc := by
    simpa [Yc] using independent_common_scalar_add_isCenteredJointlyGaussian PY Y hY c
  have hXc : DOZZ.IsCenteredJointlyGaussian (PX.prod (gaussianReal 0 1)) Xc := by
    simpa [Xc] using independent_common_scalar_add_isCenteredJointlyGaussian PX X hX c
  have hcovXleYc (i j : ι) :
      DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) ≤
        DOZZ.gaussianCovariance (PY.prod (gaussianReal 0 1))
          (fun ω => Yc ω i) (fun ω => Yc ω j) := by
    have hupper := (abs_le.mp (hcov i j)).2
    calc
      DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) ≤
          DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j) + C := by linarith
      _ = DOZZ.gaussianCovariance (PY.prod (gaussianReal 0 1))
          (fun ω => Yc ω i) (fun ω => Yc ω j) := by
            symm
            simpa [Yc, hcSq] using
              gaussianCovariance_independent_common_scalar_add PY Y hY c i j
  have hcovYleXc (i j : ι) :
      DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j) ≤
        DOZZ.gaussianCovariance (PX.prod (gaussianReal 0 1))
          (fun ω => Xc ω i) (fun ω => Xc ω j) := by
    have hlower := (abs_le.mp (hcov i j)).1
    calc
      DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j) ≤
          DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) + C := by linarith
      _ = DOZZ.gaussianCovariance (PX.prod (gaussianReal 0 1))
          (fun ω => Xc ω i) (fun ω => Xc ω j) := by
            symm
            simpa [Xc, hcSq] using
              gaussianCovariance_independent_common_scalar_add PX X hX c i j
  let K : ℝ≥0∞ := ENNReal.ofReal (Real.exp A)
  let L : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-A))
  have hYfactor : DOZZ.finiteChaosMoment (PY.prod (gaussianReal 0 1)) Yc a γ p =
      K * DOZZ.finiteChaosMoment PY Y a γ p := by
    simpa [K, Yc, A, hcSq] using
      finiteChaosMoment_independent_common_scalar_factor PY Y hY a ha γ c p
  have hXfactor : DOZZ.finiteChaosMoment (PX.prod (gaussianReal 0 1)) Xc a γ p =
      K * DOZZ.finiteChaosMoment PX X a γ p := by
    simpa [K, Xc, A, hcSq] using
      finiteChaosMoment_independent_common_scalar_factor PX X hX a ha γ c p
  have hXleYc : DOZZ.finiteChaosMoment PX X a γ p ≤
      DOZZ.finiteChaosMoment (PY.prod (gaussianReal 0 1)) Yc a γ p := by
    by_cases hpone : p = 1
    · simpa [hpone] using (finiteChaosMoment_one_eq PX (PY.prod (gaussianReal 0 1))
        X Yc hX hYc a ha γ).le
    · by_cases hptwo : p = 2
      · simpa [hptwo] using kahane_finite_power_two PX (PY.prod (gaussianReal 0 1))
          X Yc hX hYc a ha γ hcovXleYc
      · exact kahane_finite_power_convex_one_two PX (PY.prod (gaussianReal 0 1))
          X Yc hX hYc a ha γ p
          ⟨lt_of_le_of_ne hp.1 (Ne.symm hpone), lt_of_le_of_ne hp.2 hptwo⟩ hcovXleYc
  have hYleXc : DOZZ.finiteChaosMoment PY Y a γ p ≤
      DOZZ.finiteChaosMoment (PX.prod (gaussianReal 0 1)) Xc a γ p := by
    by_cases hpone : p = 1
    · simpa [hpone] using (finiteChaosMoment_one_eq PY (PX.prod (gaussianReal 0 1))
        Y Xc hY hXc a ha γ).le
    · by_cases hptwo : p = 2
      · simpa [hptwo] using kahane_finite_power_two PY (PX.prod (gaussianReal 0 1))
          Y Xc hY hXc a ha γ hcovYleXc
      · exact kahane_finite_power_convex_one_two PY (PX.prod (gaussianReal 0 1))
          Y Xc hY hXc a ha γ p
          ⟨lt_of_le_of_ne hp.1 (Ne.symm hpone), lt_of_le_of_ne hp.2 hptwo⟩ hcovYleXc
  have hLK : L * K = 1 := by
    dsimp [L, K]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    rw [show Real.exp (-A) * Real.exp A = 1 by rw [← Real.exp_add]; simp]
    simp
  constructor
  · have hscaled := calc
        L * DOZZ.finiteChaosMoment PY Y a γ p ≤
            L * DOZZ.finiteChaosMoment (PX.prod (gaussianReal 0 1)) Xc a γ p := by
              gcongr
      _ = L * (K * DOZZ.finiteChaosMoment PX X a γ p) := by rw [hXfactor]
      _ = DOZZ.finiteChaosMoment PX X a γ p := by
            calc
              L * (K * DOZZ.finiteChaosMoment PX X a γ p) =
                  (L * K) * DOZZ.finiteChaosMoment PX X a γ p := by ac_rfl
              _ = DOZZ.finiteChaosMoment PX X a γ p := by rw [hLK]; simp
    simpa [L, A] using hscaled
  · simpa [K, A] using hXleYc.trans_eq hYfactor

/-- The two-sided finite constant trick at every natural power, including the mass and first-moment
cases. -/
theorem kahane_finite_constant_trick_nat
    {ΩX ΩY : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    {ι : Type*} [Fintype ι]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (hX : DOZZ.IsCenteredJointlyGaussian PX X)
    (hY : DOZZ.IsCenteredJointlyGaussian PY Y)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (γ C : ℝ) (n : ℕ)
    (hC : 0 ≤ C)
    (hcov : ∀ i j,
      |DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) -
        DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j)| ≤ C) :
    ENNReal.ofReal (Real.exp (-(γ ^ 2 * C / 2 * ((n : ℝ) ^ 2 - n))) ) *
        DOZZ.finiteChaosMoment PY Y a γ n ≤ DOZZ.finiteChaosMoment PX X a γ n ∧
      DOZZ.finiteChaosMoment PX X a γ n ≤
        ENNReal.ofReal (Real.exp (γ ^ 2 * C / 2 * ((n : ℝ) ^ 2 - n))) *
          DOZZ.finiteChaosMoment PY Y a γ n := by
  classical
  let p : ℝ := n
  let c : ℝ := Real.sqrt C
  let A : ℝ := γ ^ 2 * C / 2 * (p ^ 2 - p)
  let Yc : ΩY × ℝ → ι → ℝ := fun ω i => Y ω.1 i + c * ω.2
  let Xc : ΩX × ℝ → ι → ℝ := fun ω i => X ω.1 i + c * ω.2
  have hcSq : c ^ 2 = C := by
    dsimp [c]
    exact Real.sq_sqrt hC
  have hYc : DOZZ.IsCenteredJointlyGaussian (PY.prod (gaussianReal 0 1)) Yc := by
    simpa [Yc] using independent_common_scalar_add_isCenteredJointlyGaussian PY Y hY c
  have hXc : DOZZ.IsCenteredJointlyGaussian (PX.prod (gaussianReal 0 1)) Xc := by
    simpa [Xc] using independent_common_scalar_add_isCenteredJointlyGaussian PX X hX c
  have hcovXleYc (i j : ι) :
      DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) ≤
        DOZZ.gaussianCovariance (PY.prod (gaussianReal 0 1))
          (fun ω => Yc ω i) (fun ω => Yc ω j) := by
    have hupper := (abs_le.mp (hcov i j)).2
    calc
      DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) ≤
          DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j) + C := by linarith
      _ = DOZZ.gaussianCovariance (PY.prod (gaussianReal 0 1))
          (fun ω => Yc ω i) (fun ω => Yc ω j) := by
            symm
            simpa [Yc, hcSq] using
              gaussianCovariance_independent_common_scalar_add PY Y hY c i j
  have hcovYleXc (i j : ι) :
      DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j) ≤
        DOZZ.gaussianCovariance (PX.prod (gaussianReal 0 1))
          (fun ω => Xc ω i) (fun ω => Xc ω j) := by
    have hlower := (abs_le.mp (hcov i j)).1
    calc
      DOZZ.gaussianCovariance PY (fun ω => Y ω i) (fun ω => Y ω j) ≤
          DOZZ.gaussianCovariance PX (fun ω => X ω i) (fun ω => X ω j) + C := by linarith
      _ = DOZZ.gaussianCovariance (PX.prod (gaussianReal 0 1))
          (fun ω => Xc ω i) (fun ω => Xc ω j) := by
            symm
            simpa [Xc, hcSq] using
              gaussianCovariance_independent_common_scalar_add PX X hX c i j
  let K : ℝ≥0∞ := ENNReal.ofReal (Real.exp A)
  let L : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-A))
  have hYfactor : DOZZ.finiteChaosMoment (PY.prod (gaussianReal 0 1)) Yc a γ p =
      K * DOZZ.finiteChaosMoment PY Y a γ p := by
    simpa [K, Yc, A, p, hcSq] using
      finiteChaosMoment_independent_common_scalar_factor PY Y hY a ha γ c n
  have hXfactor : DOZZ.finiteChaosMoment (PX.prod (gaussianReal 0 1)) Xc a γ p =
      K * DOZZ.finiteChaosMoment PX X a γ p := by
    simpa [K, Xc, A, p, hcSq] using
      finiteChaosMoment_independent_common_scalar_factor PX X hX a ha γ c n
  have hXleYc : DOZZ.finiteChaosMoment PX X a γ p ≤
      DOZZ.finiteChaosMoment (PY.prod (gaussianReal 0 1)) Yc a γ p := by
    simpa [p] using kahane_finite_power_nat PX (PY.prod (gaussianReal 0 1))
      X Yc hX hYc a ha γ n hcovXleYc
  have hYleXc : DOZZ.finiteChaosMoment PY Y a γ p ≤
      DOZZ.finiteChaosMoment (PX.prod (gaussianReal 0 1)) Xc a γ p := by
    simpa [p] using kahane_finite_power_nat PY (PX.prod (gaussianReal 0 1))
      Y Xc hY hXc a ha γ n hcovYleXc
  have hLK : L * K = 1 := by
    dsimp [L, K]
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
    rw [show Real.exp (-A) * Real.exp A = 1 by rw [← Real.exp_add]; simp]
    simp
  constructor
  · have hscaled := calc
        L * DOZZ.finiteChaosMoment PY Y a γ p ≤
            L * DOZZ.finiteChaosMoment (PX.prod (gaussianReal 0 1)) Xc a γ p := by
              gcongr
        _ = L * (K * DOZZ.finiteChaosMoment PX X a γ p) := by rw [hXfactor]
        _ = DOZZ.finiteChaosMoment PX X a γ p := by
              calc
                L * (K * DOZZ.finiteChaosMoment PX X a γ p) =
                    (L * K) * DOZZ.finiteChaosMoment PX X a γ p := by ac_rfl
                _ = DOZZ.finiteChaosMoment PX X a γ p := by rw [hLK]; simp
    simpa [L, A, p] using hscaled
  · simpa [K, A, p] using hXleYc.trans_eq hYfactor


end DOZZ.Proofs

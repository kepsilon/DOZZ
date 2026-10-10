/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.FiniteGaussianCommonScalar
public import DOZZ.GMC.FiniteChaosPowerShift

/-! The finite constant trick for all convex powers. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- Two-sided finite-dimensional Kahane comparison for every convex real power. -/
theorem kahane_finite_constant_trick
    {ΩX ΩY : Type*} [MeasurableSpace ΩX] [MeasurableSpace ΩY]
    {ι : Type*} [Fintype ι]
    (PX : Measure ΩX) (PY : Measure ΩY)
    (X : ΩX → ι → ℝ) (Y : ΩY → ι → ℝ)
    (hX : DOZZ.IsCenteredJointlyGaussian PX X)
    (hY : DOZZ.IsCenteredJointlyGaussian PY Y)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (γ C p : ℝ)
    (hC : 0 ≤ C) (hp : p ≤ 0 ∨ 1 ≤ p)
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
    kahane_finite_power_convex PX (PY.prod (gaussianReal 0 1)) X Yc hX hYc a ha γ p hp hcovXleYc
  have hYleXc : DOZZ.finiteChaosMoment PY Y a γ p ≤
      DOZZ.finiteChaosMoment (PX.prod (gaussianReal 0 1)) Xc a γ p :=
    kahane_finite_power_convex PY (PX.prod (gaussianReal 0 1)) Y Xc hY hXc a ha γ p hp hcovYleXc
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


end DOZZ.Proofs

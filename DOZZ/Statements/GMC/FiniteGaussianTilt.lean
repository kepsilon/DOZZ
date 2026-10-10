/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.IsGaussianL2Limit
import DOZZ.GMC.FiniteGaussianTilt

/-! The statement `DOZZ.finite_gaussian_tilt`, proved by `DOZZ.Proofs.finite_gaussian_tilt`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Finite-dimensional Cameron–Martin tilt, allowing singular joint covariance. The shift is
`Cov(Z_i, ∑ⱼ aⱼ Zⱼ)` and the Wick normalization is the variance of that same linear functional.
See [KRV, Theorem 12.1]. -/
theorem finite_gaussian_tilt
    {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ)
    (hZ : IsCenteredJointlyGaussian P Z) (a : ι → ℝ)
    (F : (ι → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ ω,
      ENNReal.ofReal (Real.exp
        ((∑ i, a i * Z ω i) -
          (∑ i, ∑ j, a i * gaussianCovariance P (fun ω => Z ω i)
            (fun ω => Z ω j) * a j) / 2)) * F (Z ω) ∂P) =
    ∫⁻ ω, F (fun i => Z ω i +
      ∑ j, gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) * a j) ∂P := by exact DOZZ.Proofs.finite_gaussian_tilt P Z hZ a F hF

end DOZZ

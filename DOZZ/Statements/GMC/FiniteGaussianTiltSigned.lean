/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.IsGaussianL2Limit
import DOZZ.GMC.FiniteGaussianTiltSigned

/-! The statement `DOZZ.finite_gaussian_tilt_signed`,
proved by `DOZZ.Proofs.finite_gaussian_tilt_signed`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Signed finite-dimensional Cameron–Martin tilt. The shifted functional is integrable, which
also makes the Wick-weighted left integrand integrable by the nonnegative tilt identity.
See [KRV, Theorem 12.1]. -/
theorem finite_gaussian_tilt_signed
    {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ)
    (hZ : IsCenteredJointlyGaussian P Z) (a : ι → ℝ)
    (F : (ι → ℝ) → ℝ) (hF : Measurable F)
    (hI : Integrable (fun ω => F (fun i => Z ω i +
      ∑ j, gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) * a j)) P) :
    ∫ ω, Real.exp ((∑ i, a i * Z ω i) -
        (∑ i, ∑ j, a i * gaussianCovariance P (fun ω => Z ω i)
          (fun ω => Z ω j) * a j) / 2) * F (Z ω) ∂P =
      ∫ ω, F (fun i => Z ω i +
        ∑ j, gaussianCovariance P (fun ω => Z ω i) (fun ω => Z ω j) * a j) ∂P := by exact DOZZ.Proofs.finite_gaussian_tilt_signed P Z hZ a F hF hI

end DOZZ

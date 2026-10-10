/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.IsGaussianL2Limit
import DOZZ.GMC.EquatorGFFCameronMartin

/-! The statement `DOZZ.equatorGFF_cameron_martin_signed`,
proved by `DOZZ.Proofs.equatorGFF_cameron_martin_signed`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Signed-field Cameron–Martin corollary. Integrability of the shifted signed functional is the
interface needed for both Bochner integrals. A tilt by an independent scalar outside the `L²`
closure is obtained by adjoining it to the finite jointly Gaussian family instead.
See [KRV, Theorem 12.1] (corrected; erratum K2, see docs/ERRATA-AND-DEVIATIONS.md). -/
theorem equatorGFF_cameron_martin_signed
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (L : Ω → ℝ) (hL : IsGaussianL2Limit P X L)
    (t : ℝ) (H : (TestFn → ℝ) → ℝ) (hH : Measurable H)
    (hI : Integrable (fun ω => H (fun f => X ω f +
      t * gaussianCovariance P (fun ω => X ω f) L)) P) :
    ∫ ω, Real.exp (t * L ω - t ^ 2 / 2 * gaussianVariance P L) *
        H (fun f => X ω f) ∂P =
      ∫ ω, H (fun f => X ω f +
        t * gaussianCovariance P (fun ω => X ω f) L) ∂P := by exact DOZZ.Proofs.equatorGFF_cameron_martin_signed P X hX L hL t H hH hI

end DOZZ

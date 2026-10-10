/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.GaussCoefficientRatio
import DOZZ.Hypergeom.ClassificationCoefficientRatio

/-! The statement `DOZZ.real_gauss_solution_coefficient_ratio`,
proved by `DOZZ.Proofs.real_gauss_solution_coefficient_ratio`. -/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- The normalized form of [KRV, (Tsolution)] and [KRV, (Fundrelation)], only on the exact
nondegenerate `K₂` locus (erratum K27, see docs/ERRATA-AND-DEVIATIONS.md). The numerator Gamma
finiteness is a consequence to prove, not an added hypothesis. -/
theorem real_gauss_solution_coefficient_ratio {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) (a b c : ℝ)
    (hc : ∀ n : ℤ, c ≠ (n : ℝ)) (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℝ))
    (hK₂ : gaussK₂ a b c ≠ 0) (T : ℂ → ℝ) (hT : IsRealGaussSolution a b c T) :
    ∃! coeff : ℝ, ∀ z ∈ gaussCutPlane,
      T z = coeff * (‖gaussFMinus H a b c z‖ ^ 2 +
        gaussCoefficientRatio a b c * ‖gaussFPlus H a b c z‖ ^ 2) := by exact DOZZ.Proofs.real_gauss_solution_coefficient_ratio hH a b c hc hδ hK₂ T hT

end DOZZ

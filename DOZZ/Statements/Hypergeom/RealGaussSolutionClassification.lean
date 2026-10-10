/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.GaussCoefficientRatio
import DOZZ.Hypergeom.ClassificationAssembly

/-! The statement `DOZZ.real_gauss_solution_classification`,
proved by `DOZZ.Proofs.real_gauss_solution_classification`. -/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- Classification of the real single-valued C² solutions of the Gauss PDE, see [KRV, (Tsolution)]
and [KRV-local, Lemma 4.4]. The general statement preserves coefficient strata and uses conjugate
norm squares. -/
theorem real_gauss_solution_classification {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) (a b c : ℝ)
    (hc : ∀ n : ℤ, c ≠ (n : ℝ)) (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℝ))
    (T : ℂ → ℝ) (hT : IsRealGaussSolution a b c T) :
    ∃! v : ℝ × ℝ,
      gaussK₁ a b c * v.1 + gaussK₂ a b c * v.2 = 0 ∧
      ∀ z ∈ gaussCutPlane,
        T z = v.1 * ‖gaussFMinus H a b c z‖ ^ 2 +
          v.2 * ‖gaussFPlus H a b c z‖ ^ 2 := by exact DOZZ.Proofs.real_gauss_solution_classification hH a b c hc hδ T hT

end DOZZ

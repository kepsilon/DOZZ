/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.GaussCoefficientRatio
import DOZZ.Hypergeom.ClassificationDiagonalExtension

/-! The statement `DOZZ.gauss_diagonal_extension_iff`,
proved by `DOZZ.Proofs.gauss_diagonal_extension_iff`. -/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- Sufficiency in the classification of real solutions, proved via local cut crossing (no
loop-generator premise is assumed): every pair satisfying the undivided relation has a real
single-valued C² extension. No result in the proofs of the main theorems uses this direction. -/
theorem gauss_diagonal_extension_iff {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) (a b c : ℝ)
    (hc : ∀ n : ℤ, c ≠ (n : ℝ)) (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℝ))
    (coeff₁ coeff₂ : ℝ) :
    (∃ T : ℂ → ℝ, IsRealGaussSolution a b c T ∧
      ∀ z ∈ gaussCutPlane, T z = coeff₁ * ‖gaussFMinus H a b c z‖ ^ 2 +
        coeff₂ * ‖gaussFPlus H a b c z‖ ^ 2) ↔
      gaussK₁ a b c * coeff₁ + gaussK₂ a b c * coeff₂ = 0 := by exact DOZZ.Proofs.gauss_diagonal_extension_iff hH a b c hc hδ coeff₁ coeff₂

end DOZZ

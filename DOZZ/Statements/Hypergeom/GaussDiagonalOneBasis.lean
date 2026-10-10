/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.GaussCrossE
import DOZZ.Hypergeom.GaussDiagonalOneBasis

/-! The statement `DOZZ.gauss_diagonal_one_basis`,
proved by `DOZZ.Proofs.gauss_diagonal_one_basis`. -/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- Crossed diagonal form at 1 ([KRV, (newformula)], corrected as in erratum K1, see
docs/ERRATA-AND-DEVIATIONS.md): the cross terms cancel since `uv + A·wx = Γ(δ)Γ(-δ)(K₁ + A·K₂) = 0`
on the nondegenerate `K₂ ≠ 0` locus (erratum K27, see docs/ERRATA-AND-DEVIATIONS.md). -/
theorem gauss_diagonal_one_basis {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) (a b c : ℝ)
    (hc : ∀ n : ℤ, c ≠ (n : ℝ)) (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℝ))
    (hK₂ : gaussK₂ a b c ≠ 0) : ∀ z ∈ gaussCutPlane,
      ‖gaussFMinus H a b c z‖ ^ 2 + gaussCoefficientRatio a b c *
        ‖gaussFPlus H a b c z‖ ^ 2 =
      gaussCrossD a b c * ‖gaussGMinus H a b c z‖ ^ 2 +
        gaussCrossE a b c * ‖gaussGPlus H a b c z‖ ^ 2 := by exact DOZZ.Proofs.gauss_diagonal_one_basis hH a b c hc hδ hK₂

end DOZZ

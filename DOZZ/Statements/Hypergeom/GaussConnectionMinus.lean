/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.GaussCoefficientRatio
import DOZZ.Hypergeom.GaussConnectionMinus

/-! The statement `DOZZ.gauss_connection_minus`, proved by `DOZZ.Proofs.gauss_connection_minus`. -/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- The connection formula [KRV, (f+)], corrected as in erratum K1 (see
docs/ERRATA-AND-DEVIATIONS.md). Gamma inverses are the entire reciprocal, including genuine
denominator zeros. -/
theorem gauss_connection_minus {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) (a b c : ℂ)
    (hc : ∀ n : ℤ, c ≠ (n : ℂ)) (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℂ)) :
    ∀ z ∈ gaussCutPlane,
      gaussFMinus H a b c z =
        (Complex.Gamma c * Complex.Gamma (c - a - b) *
          (Complex.Gamma (c - a))⁻¹ * (Complex.Gamma (c - b))⁻¹) *
            gaussGMinus H a b c z +
        (Complex.Gamma c * Complex.Gamma (a + b - c) *
          (Complex.Gamma a)⁻¹ * (Complex.Gamma b)⁻¹) * gaussGPlus H a b c z := by exact DOZZ.Proofs.gauss_connection_minus hH a b c hc hδ

end DOZZ

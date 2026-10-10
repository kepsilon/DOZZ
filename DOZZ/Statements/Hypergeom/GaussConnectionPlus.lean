/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.GaussCoefficientRatio
import DOZZ.Hypergeom.GaussConnectionPlus

/-! The statement `DOZZ.gauss_connection_plus`, proved by `DOZZ.Proofs.gauss_connection_plus`. -/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- The connection formula [KRV, (f-)], corrected as in erratum K1 (see
docs/ERRATA-AND-DEVIATIONS.md); no duplicated (1−z)^δ. -/
theorem gauss_connection_plus {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) (a b c : ℂ)
    (hc : ∀ n : ℤ, c ≠ (n : ℂ)) (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℂ)) :
    ∀ z ∈ gaussCutPlane,
      gaussFPlus H a b c z =
        (Complex.Gamma (2 - c) * Complex.Gamma (c - a - b) *
          (Complex.Gamma (1 - a))⁻¹ * (Complex.Gamma (1 - b))⁻¹) *
            gaussGMinus H a b c z +
        (Complex.Gamma (2 - c) * Complex.Gamma (a + b - c) *
          (Complex.Gamma (a - c + 1))⁻¹ * (Complex.Gamma (b - c + 1))⁻¹) *
            gaussGPlus H a b c z := by exact DOZZ.Proofs.gauss_connection_plus hH a b c hc hδ

end DOZZ

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.GaussCoefficientRatio
import DOZZ.Hypergeom.ConnectionDet

/-! The statement `DOZZ.gauss_connection_det`, proved by `DOZZ.Proofs.gauss_connection_det`. -/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- Determinant `det M = (c-1)/δ` of the connection matrix of `gauss_connection_minus/plus`,
corrected as in erratum K1 (see docs/ERRATA-AND-DEVIATIONS.md). Reciprocal Gamma is entire. -/
theorem gauss_connection_det (a b c : ℂ)
    (hc : ∀ n : ℤ, c ≠ (n : ℂ)) (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℂ)) :
    (Complex.Gamma c * Complex.Gamma (c - a - b) *
        (Complex.Gamma (c - a))⁻¹ * (Complex.Gamma (c - b))⁻¹) *
      (Complex.Gamma (2 - c) * Complex.Gamma (a + b - c) *
        (Complex.Gamma (a - c + 1))⁻¹ * (Complex.Gamma (b - c + 1))⁻¹) -
      (Complex.Gamma c * Complex.Gamma (a + b - c) *
        (Complex.Gamma a)⁻¹ * (Complex.Gamma b)⁻¹) *
      (Complex.Gamma (2 - c) * Complex.Gamma (c - a - b) *
        (Complex.Gamma (1 - a))⁻¹ * (Complex.Gamma (1 - b))⁻¹) =
    (c - 1) / (c - a - b) := by exact DOZZ.Proofs.gauss_connection_det a b c hc hδ

end DOZZ

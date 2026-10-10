/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.GaussCoefficientRatio
import DOZZ.Hypergeom.BasisSpanning

/-! The statement `DOZZ.gauss_local_basis_one`, proved by `DOZZ.Proofs.gauss_local_basis_one`. -/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- The 1-basis and its Wronskian, [KRV, (Fpmdef')]. Only δ=c−a−b∉ℤ is needed at this endpoint. -/
theorem gauss_local_basis_one {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) (a b c : ℂ)
    (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℂ)) :
    DifferentiableOn ℂ (gaussGMinus H a b c) gaussCutPlane ∧
    DifferentiableOn ℂ (gaussGPlus H a b c) gaussCutPlane ∧
    (∀ z ∈ gaussCutPlane,
      gaussHolomorphicOperator a b c (gaussGMinus H a b c) z = 0 ∧
      gaussHolomorphicOperator a b c (gaussGPlus H a b c) z = 0 ∧
      gaussGMinus H a b c z * deriv (gaussGPlus H a b c) z -
        deriv (gaussGMinus H a b c) z * gaussGPlus H a b c z =
          -(c - a - b) * z ^ (-c) * (1 - z) ^ (c - a - b - 1)) ∧
    (∀ y : ℂ → ℂ, DifferentiableOn ℂ y gaussCutPlane →
      (∀ z ∈ gaussCutPlane, gaussHolomorphicOperator a b c y z = 0) →
      ∃! v : ℂ × ℂ, ∀ z ∈ gaussCutPlane,
        y z = v.1 * gaussGMinus H a b c z + v.2 * gaussGPlus H a b c z) := by exact DOZZ.Proofs.gauss_local_basis_one hH a b c hδ

end DOZZ

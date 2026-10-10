/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.GaussCrossE
import DOZZ.Hypergeom.Germs

/-! The statement `DOZZ.gauss_local_basis_germs`,
proved by `DOZZ.Proofs.gauss_local_basis_germs`. -/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- Endpoint germs used in the crossing and fusion comparisons of [KRV, §4.2] and [KRV, §4.3]. The
unpowered factors tend to one at their regular singular points; the two powered bases have the
displayed leading powers. -/
theorem gauss_local_basis_germs {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) (a b c : ℂ)
    (hc : ∀ n : ℤ, c ≠ (n : ℂ)) (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℂ)) :
    gaussFMinus H a b c 0 = 1 ∧
    HasDerivAt (gaussFMinus H a b c) (a * b / c) 0 ∧
    Tendsto (fun z : ℂ => gaussFPlus H a b c z / z ^ (1 - c))
      (nhdsWithin 0 gaussCutPlane) (nhds 1) ∧
    gaussGMinus H a b c 1 = 1 ∧
    HasDerivAt (gaussGMinus H a b c) (-(a * b / (1 + a + b - c))) 1 ∧
    Tendsto (fun z : ℂ => gaussGPlus H a b c z / (1 - z) ^ (c - a - b))
      (nhdsWithin 1 gaussCutPlane) (nhds 1) := by exact DOZZ.Proofs.gauss_local_basis_germs hH a b c hc hδ

end DOZZ

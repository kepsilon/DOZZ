/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.PlanarDifferenceKernel
import DOZZ.Hypergeom.Planar.WirtingerIntegral

/-! The statement `DOZZ.planar_wirtinger_integral`,
proved by `DOZZ.Proofs.planar_wirtinger_integral`. -/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- The differentiated identity [KRV, (gammaz)] (erratum K8, see docs/ERRATA-AND-DEVIATIONS.md).
Absolute convergence holds on the full window 0<k<β<2, including β=k+1 where the parent need not
converge. -/
theorem planar_wirtinger_integral (k β : ℝ) (hk : 0 < k)
    (hβ : k < β) (hβ₂ : β < 2) :
    ∀ z : ℂ, z ≠ 0 → Integrable (planarWirtingerKernel k β z) volume ∧
      (k / 2 : ℝ) * (k / 2 - 1 : ℝ) * (∫ u : ℂ, planarWirtingerKernel k β z u) =
        ((2 + k - β) / 2 : ℝ) * ((2 + k - β) / 2 - 1 : ℝ) *
          (‖z‖ ^ (2 + k - β) : ℝ) / z ^ 2 * planarGaussConstant k β := by exact DOZZ.Proofs.planar_wirtinger_integral k β hk hβ hβ₂

end DOZZ

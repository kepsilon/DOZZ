/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.PlanarDifferenceKernel
import DOZZ.Hypergeom.Planar.RieszNormalization

/-! The statement `DOZZ.planar_mixed_integral`, proved by `DOZZ.Proofs.planar_mixed_integral`. -/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- The differentiated identity [KRV, (gammazbarz)] (erratum K8, see docs/ERRATA-AND-DEVIATIONS.md),
on the same exact full window. No parent-integrability premise or principal-value convention is
smuggled into the statement. -/
theorem planar_mixed_integral (k β : ℝ) (hk : 0 < k)
    (hβ : k < β) (hβ₂ : β < 2) :
    ∀ z : ℂ, z ≠ 0 → Integrable (planarMixedKernel k β z) volume ∧
      (((k / 2) ^ 2 * (∫ u : ℂ, planarMixedKernel k β z u) : ℝ) : ℂ) =
        (((2 + k - β) / 2) ^ 2 * ‖z‖ ^ (k - β) : ℝ) *
          planarGaussConstant k β := by exact DOZZ.Proofs.planar_mixed_integral k β hk hβ hβ₂

end DOZZ

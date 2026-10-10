/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.PlanarDifferenceKernel
import DOZZ.Hypergeom.Planar.TaylorIntegral

/-! The statement `DOZZ.planar_taylor_integral`, proved by `DOZZ.Proofs.planar_taylor_integral`. -/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- The corrected parent integral of [KRV, §12.8] (erratum K8, see docs/ERRATA-AND-DEVIATIONS.md),
with its exact nonzero-z convergence window. Put k=γ²/2, β=γα₁. The range 2<γ²<4, γ/2<α₁<2/γ is
included. -/
theorem planar_taylor_integral (k β : ℝ) (hk : 0 < k)
    (hβ : k < β) (hβ₂ : β < 2) (hβlin : β < k + 1) :
    ∀ z : ℂ, Integrable (planarTaylorRemainder k β z) volume ∧
      ((∫ u : ℂ, planarTaylorRemainder k β z u) : ℂ) =
        (‖z‖ ^ (2 + k - β) : ℝ) * planarGaussConstant k β := by exact DOZZ.Proofs.planar_taylor_integral k β hk hβ hβ₂ hβlin

end DOZZ

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.PlanarDifferenceKernel
import DOZZ.Hypergeom.Planar.DifferenceIntegral

/-! The statement `DOZZ.planar_difference_integral`,
proved by `DOZZ.Proofs.planar_difference_integral`. -/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- Absolutely convergent exactly on the KRV window `k+1<β<2` (nonempty iff `k<1`,
i.e. `γ²<2`). This is the counterterm-free collision kernel. -/
theorem planar_difference_integral (k β : ℝ) (hk : 0 < k) (hβ : k + 1 < β) (hβ₂ : β < 2) :
    ∀ z : ℂ, Integrable (planarDifferenceKernel k β z) volume ∧
      ((∫ u : ℂ, planarDifferenceKernel k β z u) : ℂ) =
        (‖z‖ ^ (2 + k - β) : ℝ) * planarGaussConstant k β := by exact DOZZ.Proofs.planar_difference_integral k β hk hβ hβ₂

end DOZZ

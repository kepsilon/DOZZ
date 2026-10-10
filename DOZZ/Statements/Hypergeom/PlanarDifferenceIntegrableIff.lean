/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.PlanarDifferenceKernel
import DOZZ.Hypergeom.Planar.DifferenceIntegrableIff

/-! The statement `DOZZ.planar_difference_integrable_iff`,
proved by `DOZZ.Proofs.planar_difference_integrable_iff`. -/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- Exact absolute-integrability test for the kernel of [KRV-local, Lemma 4.5] at `z ≠ 0`: the
origin needs `β < 2` and infinity needs `k + 1 < β`; for `k ≥ 1` both sides are false. -/
theorem planar_difference_integrable_iff (k β : ℝ) (hk : 0 < k) (z : ℂ) (hz : z ≠ 0) :
    Integrable (planarDifferenceKernel k β z) volume ↔ k + 1 < β ∧ β < 2 := by exact DOZZ.Proofs.planar_difference_integrable_iff k β hk z hz

end DOZZ

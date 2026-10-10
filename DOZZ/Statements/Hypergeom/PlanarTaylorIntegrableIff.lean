/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.PlanarDifferenceKernel
import DOZZ.Hypergeom.Planar.TaylorIntegrableIff

/-! The statement `DOZZ.planar_taylor_integrable_iff`,
proved by `DOZZ.Proofs.planar_taylor_integrable_iff`. -/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- Exact convergence test for the PLUS-subtracted parent away from z=0; Taylor estimates of
[KRV, §12.8] (erratum K8, see docs/ERRATA-AND-DEVIATIONS.md). This is absolute integrability, not a
totalized Bochner-value test. -/
theorem planar_taylor_integrable_iff (k β : ℝ) (hk : 0 < k)
    (z : ℂ) (hz : z ≠ 0) :
    Integrable (planarTaylorRemainder k β z) volume ↔ k < β ∧ β < 2 ∧ β < k + 1 := by exact DOZZ.Proofs.planar_taylor_integrable_iff k β hk z hz

end DOZZ

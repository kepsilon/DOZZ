/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.PlanarDifferenceKernel
import DOZZ.Hypergeom.Planar.DerivativeIntegrable

/-! The statement `DOZZ.planar_derivative_integrable_iff`,
proved by `DOZZ.Proofs.planar_derivative_integrable_iff`. -/

public section

open MeasureTheory Filter Set
open scoped Topology

namespace DOZZ

/-- Exact convergence of both differentiated kernels of [KRV, (gammaz)] and [KRV, (gammazbarz)]
(erratum K8, see docs/ERRATA-AND-DEVIATIONS.md). The kernels are ordinary Lebesgue-integrable at u=z
precisely when k>0. -/
theorem planar_derivative_integrable_iff (k β : ℝ) (hk : 0 < k)
    (z : ℂ) (hz : z ≠ 0) :
    (Integrable (planarWirtingerKernel k β z) volume ↔ k < β ∧ β < 2) ∧
      (Integrable (planarMixedKernel k β z) volume ↔ k < β ∧ β < 2) := by exact DOZZ.Proofs.planar_derivative_integrable_iff k β hk z hz

end DOZZ

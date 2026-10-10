/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Correlations.ExtendedSeibergN

/-! The definition `DOZZ.nPointCoulombPrefactor`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The finite-position Coulomb prefactor in [KRV, (Z1)]. Its real-power totalization at coincident
positions lies outside the domain of that formula; all theorems using it require pairwise distinct
points. -/
noncomputable def nPointCoulombPrefactor {N : ℕ}
    (α : Fin N → ℝ) (z : Fin N → ℂ) : ℝ :=
  ∏ i : Fin N, ∏ j : Fin N,
    if i < j then Real.rpow ‖z i - z j‖ (-(α i * α j)) else 1

end DOZZ

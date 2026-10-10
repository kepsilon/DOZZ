/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Correlations.NPointCoulombPrefactor

/-! The definition `DOZZ.unitVolumeNPointCorrelation`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The unit-volume N-point moment, literally extending the formulas [KRV, (Z1)] and
[KRV, (unitvol)]. Its interpretation in [KRV] and all theorems using it are restricted to
`ExtendedSeibergN`, where the moment is finite; `toReal` is only a totalized extension away from
that domain. -/
noncomputable def unitVolumeNPointCorrelation {Ω : Type*} [MeasurableSpace Ω]
    {N : ℕ} (P : Measure Ω) (M : Ω → Measure ℂ) (γ : ℝ)
    (α : Fin N → ℝ) (z : Fin N → ℂ) : ℝ :=
  2 / γ * nPointCoulombPrefactor α z *
    (∫⁻ ω, ENNReal.rpow (coulombMass γ (M ω) α z 0) (-nPointSExp γ α) ∂P).toReal

end DOZZ

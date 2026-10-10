/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.StructureConstant

/-! The definition `DOZZ.unitVolumeStructureConstant`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- The unit-volume structure constant `C̄ = μ^s C / Γ(s) = (2/γ) E[ρ^{-s}]` ([KRV, (unitvol)]). -/
noncomputable def unitVolumeStructureConstant {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ : ℝ) : ℝ :=
  2 / γ * (∫⁻ ω, rho γ (M ω) α₁ α₂ α₃ ^ (-sExp γ α₁ α₂ α₃) ∂P).toReal

end DOZZ

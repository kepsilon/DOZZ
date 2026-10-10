/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.Rho

/-! The definition `DOZZ.structureConstant`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- The structure constant by the moment formula [KRV, (expression3pointstruct)]:
`C_γ = 2 μ^{-s} γ^{-1} Γ(s) E[ρ^{-s}]`. -/
noncomputable def structureConstant {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : Ω → Measure ℂ) (γ μ α₁ α₂ α₃ : ℝ) : ℝ :=
  2 * μ ^ (-sExp γ α₁ α₂ α₃) / γ * Real.Gamma (sExp γ α₁ α₂ α₃) *
    (∫⁻ ω, rho γ (M ω) α₁ α₂ α₃ ^ (-sExp γ α₁ α₂ α₃) ∂P).toReal

end DOZZ

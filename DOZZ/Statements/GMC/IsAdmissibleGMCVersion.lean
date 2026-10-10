/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.RegularizedLogChaosTestMass

/-! The definition `DOZZ.IsAdmissibleGMCVersion`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- A measurable random measure carried by `U`, finite on compact subsets of `U`, whose integrals
of continuous tests with compact support in `U` are the limits in probability of the
regularized Wick integrals. -/
def IsAdmissibleGMCVersion {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U : Set ℂ) (dens : ℂ → ℝ) (Y : Ω → ℝ → ℂ → ℝ)
    (γ : ℝ) (M : Ω → Measure ℂ) : Prop :=
  Measurable M ∧ (∀ ω, M ω Uᶜ = 0) ∧ (∀ ω K, IsCompact K → K ⊆ U → M ω K < ⊤) ∧
    ∀ f : BoundedContinuousFunction ℂ ℝ,
      HasCompactSupport (f : ℂ → ℝ) → tsupport (f : ℂ → ℝ) ⊆ U →
        TendstoInMeasure P
          (fun r ω => regularizedLogChaosTestMass P U dens Y γ r ω f) atTop
          (fun ω => ∫ x, f x ∂M ω)

end DOZZ

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.FiniteChaosMass

/-! The definition `DOZZ.finiteChaosMoment`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Extended expected `p`th power of a finite chaos mass, retaining infinity for divergent or
negative moments at zero. See the Kahane comparison used in [KRV, §9.2] and [KRV, §12.2]. -/
noncomputable def finiteChaosMoment {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ) (a : ι → ℝ) (γ p : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (finiteChaosMass P Z a γ ω)) p ∂P

end DOZZ

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.IsGaussianL2Limit

/-! The definition `DOZZ.finiteChaosMass`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- A finite Wick chaos sum with the actual diagonal variance normalization. See the Kahane
comparison used in [KRV, §9.2] and [KRV, §12.2]. -/
noncomputable def finiteChaosMass {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι]
    (P : Measure Ω) (Z : Ω → ι → ℝ) (a : ι → ℝ) (γ : ℝ) (ω : Ω) : ℝ :=
  ∑ i, a i * Real.exp
    (γ * Z ω i - γ ^ 2 / 2 * gaussianVariance P (fun ω => Z ω i))

end DOZZ

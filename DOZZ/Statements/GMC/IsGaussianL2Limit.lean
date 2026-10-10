/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.GaussianVariance

/-! The definition `DOZZ.IsGaussianL2Limit`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- `L` belongs to the Gaussian `L²(P)` closure of the real test evaluations of `X`.
See [KRV, Theorem 12.1]. -/
def IsGaussianL2Limit {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (L : Ω → ℝ) : Prop :=
  MemLp L 2 P ∧
    ∃ f : ℕ → TestFn,
      Tendsto (fun n => eLpNorm (fun ω => L ω - X ω (f n)) 2 P) atTop (𝓝 0)

end DOZZ

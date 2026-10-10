/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.CircleEnergyGap

/-! The definition `DOZZ.IsCircleAverage`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- `Xc ω x r` is the circle average `X_r(x)` of [KRV, (circleav)] (radius `e^{-r}`): jointly
measurable in `(ω, x)` for each `r`, and the `L²(P)` limit of `X(f_n)` along every test sequence
converging to the circle measure in log-energy. -/
def IsCircleAverage {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) : Prop :=
  (∀ r : ℝ, Measurable (fun p : Ω × ℂ => Xc p.1 p.2 r)) ∧
    (∀ (x : ℂ) (r : ℝ), MemLp (fun ω => Xc ω x r) 2 P) ∧
    ∀ (x : ℂ) (r : ℝ) (f : ℕ → TestFn),
      Tendsto (fun n => circleEnergyGap x r (f n)) atTop (𝓝 0) →
        Tendsto (fun n => eLpNorm (fun ω => X ω (f n) - Xc ω x r) 2 P) atTop (𝓝 0)

end DOZZ

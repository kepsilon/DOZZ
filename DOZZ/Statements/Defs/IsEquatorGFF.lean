/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.GffCov

/-! The definition `DOZZ.IsEquatorGFF`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- `X` is the equator-pinned GFF of [KRV, §2.1] under `P`: each test evaluation is measurable
and centered Gaussian with variance `gffCov f f`. Since `X ω` is linear, this fixes every
finite-dimensional law (joint Gaussianity with covariance `gffCov`). -/
def IsEquatorGFF {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) : Prop :=
  IsProbabilityMeasure P ∧
    ∀ f : TestFn, Measurable (fun ω => X ω f) ∧
      ∃ v : ℝ≥0, (v : ℝ) = gffCov f f ∧ P.map (fun ω => X ω f) = gaussianReal 0 v

end DOZZ

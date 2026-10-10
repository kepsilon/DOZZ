/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.ReflectionR
import DOZZ.Brownian.Lateral.LawUniqueness

/-! The statement `DOZZ.isLateralGMCOf_map_eq`, proved by `DOZZ.Proofs.isLateralGMCOf_map_eq`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The circle-average lateral projection has the same law across characterized field/GMC
models. See [KRV, §3.1]. -/
theorem isLateralGMCOf_map_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') (γ : ℝ) (Z : Ω → Measure ℝ) (Z' : Ω' → Measure ℝ)
    (hZ : IsLateralGMCOf P γ Z) (hZ' : IsLateralGMCOf P' γ Z') :
    P.map Z = P'.map Z' := by exact DOZZ.Proofs.isLateralGMCOf_map_eq P P' γ Z Z' hZ hZ'

end DOZZ

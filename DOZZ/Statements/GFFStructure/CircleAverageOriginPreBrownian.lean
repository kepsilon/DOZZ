/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GFFStructure.CircleLogPotential
import DOZZ.GFFStructure.CircleCovariance

/-! The statement `DOZZ.circleAverage_origin_preBrownian`,
proved by `DOZZ.Proofs.circleAverage_origin_preBrownian`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

universe u

namespace DOZZ

/-- Two independent radial finite-dimensional Brownian laws for every witness, and the inner path
independent of the exterior field on `{‖w‖ ≥ 1}` ([KRV, Remark 2.2]); used in [KRV, §10.2]. -/
theorem circleAverage_origin_preBrownian {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) :
    IsPreBrownianReal (fun t : ℝ≥0 => fun ω => Xc ω 0 t) P ∧
    IsPreBrownianReal (fun t : ℝ≥0 => fun ω => Xc ω 0 (-(t : ℝ))) P ∧
    IndepFun (fun ω => fun t : ℝ≥0 => Xc ω 0 t)
      (fun ω => fun t : ℝ≥0 => Xc ω 0 (-(t : ℝ))) P ∧
    IndepFun (fun ω => fun t : ℝ≥0 => Xc ω 0 t)
      (fun ω => fun f : {f : TestFn // tsupport f ⊆ {w : ℂ | 1 ≤ ‖w‖}} => X ω f.val) P := by exact DOZZ.Proofs.circleAverage_origin_preBrownian P X Xc hX hc

end DOZZ

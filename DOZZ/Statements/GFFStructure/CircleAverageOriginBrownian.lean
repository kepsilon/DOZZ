/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GFFStructure.CircleLogPotential
import DOZZ.GFFStructure.CircleCovariance

/-! The statement `DOZZ.circleAverage_origin_brownian`,
proved by `DOZZ.Proofs.circleAverage_origin_brownian`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

universe u

namespace DOZZ

/-- On a continuous witness the two radial processes are Brownian paths ([KRV, Remark 2.2]). Use
`exists_continuous_circleAverage` for arbitrary witnesses. -/
theorem circleAverage_origin_brownian {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2)) :
    IsBrownianReal (fun t : ℝ≥0 => fun ω => Xc ω 0 t) P ∧
    IsBrownianReal (fun t : ℝ≥0 => fun ω => Xc ω 0 (-(t : ℝ))) P := by exact DOZZ.Proofs.circleAverage_origin_brownian P X Xc hX hc hcont

end DOZZ

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GFFStructure.CircleLogPotential
import DOZZ.GFFStructure.CircleCovariance

/-! The statement `DOZZ.circleAverage_exterior_brownian`,
proved by `DOZZ.Proofs.circleAverage_exterior_brownian`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

universe u

namespace DOZZ

/-- Continuous-witness path upgrade of [KRV, Remark 2.2]. -/
theorem circleAverage_exterior_brownian {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (c : ℂ) (hout : 2 ≤ ‖c‖) :
    IsBrownianReal (fun t : ℝ≥0 => fun ω => Xc ω c t - Xc ω c 0) P := by exact DOZZ.Proofs.circleAverage_exterior_brownian P X Xc hX hc hcont c hout

end DOZZ

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.ReflectionR
import DOZZ.Brownian.Barrier.Maximum

/-! The statement `DOZZ.negativeDriftBrownian_maximum_tail`,
proved by `DOZZ.Proofs.negativeDriftBrownian_maximum_tail`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The exponential law of the maximum of standard Brownian motion with drift `-ν`. -/
theorem negativeDriftBrownian_maximum_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (hB : ProbabilityTheory.IsBrownianReal B P) (ν x : ℝ)
    (hν : 0 < ν) (hx : 0 ≤ x) :
    P {ω | ∃ t : ℝ≥0, x < B t ω - ν * t} = ENNReal.ofReal (Real.exp (-2 * ν * x)) := by exact DOZZ.Proofs.negativeDriftBrownian_maximum_tail P B hB ν x hν hx

end DOZZ

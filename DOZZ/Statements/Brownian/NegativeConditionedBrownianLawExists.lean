/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.IsNegativeConditionedBrownianProcess
import DOZZ.Brownian.Coupling.RadialTiltDensity

/-! The statement `DOZZ.negativeConditionedBrownianLaw_exists`,
proved by `DOZZ.Proofs.negativeConditionedBrownianLaw_exists`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- Existence of the conditioned entrance law, with its law characterized rather than selected
using `Classical.choose`. See [KRV, §12.4]. -/
theorem negativeConditionedBrownianLaw_exists (ν : ℝ) (hν : 0 ≤ ν) :
    ∃! P : Measure BrownianPath, IsNegativeConditionedBrownianLaw ν P := by exact DOZZ.Proofs.negativeConditionedBrownianLaw_exists ν hν

end DOZZ

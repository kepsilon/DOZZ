/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.FieldChaosMass

/-! The definition `DOZZ.gmcReferenceMeasure`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- The deterministic reference measure `σ(dx)=|x|_+^{-4}d²x` of the equator GMC. See
[KRV, (Meps1) and (law)]. -/
noncomputable def gmcReferenceMeasure : Measure ℂ :=
  volume.withDensity (fun x => ENNReal.ofReal (normPlus x ^ (-4 : ℝ)))

end DOZZ

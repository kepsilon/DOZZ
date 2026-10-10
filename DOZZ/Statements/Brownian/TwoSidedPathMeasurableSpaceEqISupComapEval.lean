/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.TwoSidedPath

/-! The statement `DOZZ.twoSidedPath_measurableSpace_eq_iSup_comap_eval`, proved in this file. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The same evaluation characterization holds for two-sided continuous paths. -/
theorem twoSidedPath_measurableSpace_eq_iSup_comap_eval :
    (inferInstance : MeasurableSpace TwoSidedPath) =
      ⨆ t : ℝ, (inferInstance : MeasurableSpace ℝ).comap (fun p : TwoSidedPath => p t) :=
  ContinuousMap.measurableSpace_eq_iSup_comap_eval

end DOZZ

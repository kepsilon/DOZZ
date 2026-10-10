/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.GammaHalfTwoRootedTerm

/-! The definition `DOZZ.IsComplexLittleOAtZero`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- Little-o at the punctured origin, with the norm convention made explicit. -/
def IsComplexLittleOAtZero (κ : ℝ) (f : ℂ → ℂ) : Prop :=
  Tendsto (fun z => ‖f z‖ / ‖z‖ ^ κ)
    (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}) (nhds 0)

end DOZZ

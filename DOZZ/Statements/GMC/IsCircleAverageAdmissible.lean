/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.IsCompatibleAdmissibleRegularizations
import DOZZ.GMC.CircleAverage

/-! The statement `DOZZ.isCircleAverage_admissible`,
proved by `DOZZ.Proofs.isCircleAverage_admissible`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Circle averages of an equator GFF (radius `ε`) are admissible on every open chart, with the
equator reference density. -/
theorem isCircleAverage_admissible
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (U : Set ℂ) (hU : IsOpen U) :
    IsAdmissibleLogRegularization P U (fun x => normPlus x ^ (-4 : ℝ)) 1
      (fun ω ε x => Xc ω x (Real.log (1 / ε))) := by exact DOZZ.Proofs.isCircleAverage_admissible P X hX Xc hXc U hU

end DOZZ

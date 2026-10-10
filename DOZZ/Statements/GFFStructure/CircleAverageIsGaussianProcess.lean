/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GFFStructure.CircleLogPotential
import DOZZ.GFFStructure.GaussianClosure

/-! The statement `DOZZ.circleAverage_isGaussianProcess`,
proved by `DOZZ.Proofs.circleAverage_isGaussianProcess`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

universe u

namespace DOZZ

/-- Joint Gaussianity and centering of every witness, see [KRV, (hatGformula)] and
[KRV, (circleav)]. -/
theorem circleAverage_isGaussianProcess {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) :
    IsGaussianProcess (fun p : ℂ × ℝ => fun ω => Xc ω p.1 p.2) P ∧
      ∀ x r, (∫ ω, Xc ω x r ∂P) = 0 := by exact DOZZ.Proofs.circleAverage_isGaussianProcess P X Xc hX hc

end DOZZ

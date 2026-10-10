/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GFFStructure.CircleLogPotential
import DOZZ.GFFStructure.CircleVersion

/-! The statement `DOZZ.exists_continuous_circleAverage`,
proved by `DOZZ.Proofs.exists_continuous_circleAverage`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

universe u

namespace DOZZ

/-- Jointly continuous modification of the given witness (see [KRV, §2.1]). Continuity is not
asserted for an arbitrary original witness. -/
theorem exists_continuous_circleAverage {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) :
    ∃ Y : Ω → ℂ → ℝ → ℝ,
      IsCircleAverage P X Y ∧
      Measurable (fun p : Ω × (ℂ × ℝ) => Y p.1 p.2.1 p.2.2) ∧
      (∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Y ω p.1 p.2)) ∧
      (∀ x r, (fun ω => Y ω x r) =ᵐ[P] (fun ω => Xc ω x r)) := by exact DOZZ.Proofs.exists_continuous_circleAverage P X Xc hX hc

end DOZZ

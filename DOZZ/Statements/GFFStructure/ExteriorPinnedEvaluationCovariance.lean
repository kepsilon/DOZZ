/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GFFStructure.PoissonCollarValue
import DOZZ.GFFStructure.CircleCovariance

/-! The statement `DOZZ.exteriorPinnedEvaluation_covariance`,
proved by `DOZZ.Proofs.exteriorPinnedEvaluation_covariance`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

universe u

namespace DOZZ

/-- Exterior-pin covariance for global tests (see [KRV, (hatGformula)] and [KRV, (circleav)]). -/
theorem exteriorPinnedEvaluation_covariance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (R : ℝ) (hR : 1 < R) (f g : TestFn) :
    MemLp (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω f) 2 P ∧
    covariance (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω f)
      (fun ω => exteriorPinnedEvaluation X Xc R (by linarith) ω g) P =
      (∫ x : ℂ, f x * (∫ y : ℂ, exteriorPinnedKernel R (by linarith) x y * g y)) := by exact DOZZ.Proofs.exteriorPinnedEvaluation_covariance P X Xc hX hc R hR f g

end DOZZ

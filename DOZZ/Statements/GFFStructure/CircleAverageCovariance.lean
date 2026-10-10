/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GFFStructure.CircleLogPotential
import DOZZ.GFFStructure.CircleCovariance

/-! The statement `DOZZ.circleAverage_covariance`,
proved by `DOZZ.Proofs.circleAverage_covariance`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

universe u

namespace DOZZ

/-- Covariance of the circle averages about all centers, see [KRV, (hatGformula)] and
[KRV, (circleav)]. -/
theorem circleAverage_covariance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (x y : ℂ) (r s : ℝ) :
    covariance (fun ω => Xc ω x r) (fun ω => Xc ω y s) P =
      -circleLogPotential ‖x - y‖₊
          ⟨Real.exp (-r), Real.exp_pos _⟩ ⟨Real.exp (-s), Real.exp_pos _⟩ +
        circleLogPotential ‖x‖₊ ⟨Real.exp (-r), Real.exp_pos _⟩ ⟨1, by norm_num⟩ +
        circleLogPotential ‖y‖₊ ⟨Real.exp (-s), Real.exp_pos _⟩ ⟨1, by norm_num⟩ := by exact DOZZ.Proofs.circleAverage_covariance P X Xc hX hc x y r s

end DOZZ

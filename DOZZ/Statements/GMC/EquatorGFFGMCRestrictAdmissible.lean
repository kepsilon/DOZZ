/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.IsCompatibleAdmissibleRegularizations
import DOZZ.GMC.Moments.InversionAdmissibleVersion

/-! The statement `DOZZ.equatorGFF_GMC_restrict_admissible`,
proved by `DOZZ.Proofs.equatorGFF_GMC_restrict_admissible`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- On every open chart, each `IsGMCOf` version restricts almost surely to the admissible version
of the circle-average regularization. -/
theorem equatorGFF_GMC_restrict_admissible
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (U : Set ℂ) (hU : IsOpen U) :
    ∃ N : Ω → Measure ℂ,
      IsAdmissibleGMCVersion P U (fun x => normPlus x ^ (-4 : ℝ))
        (fun ω ε x => Xc ω x (Real.log (1 / ε))) γ N ∧
      ∀ᵐ ω ∂P, (M ω).restrict U = N ω := by exact DOZZ.Proofs.equatorGFF_GMC_restrict_admissible P X hX γ hγ hγ2 M hM Xc hXc U hU

end DOZZ

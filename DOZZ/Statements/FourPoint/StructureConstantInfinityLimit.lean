/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.ThreePointFiniteCorrelation
import DOZZ.FourPoint.Infinity.Assembly

/-! The statement `DOZZ.structureConstant_infinity_limit`,
proved by `DOZZ.Proofs.structureConstant_infinity_limit`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- Bridge from [KRV, (Climit)] to [KRV, (expression3pointstruct)]: in the ordinary Seiberg domain
with `s > 0`, the infinity-normalized finite-position correlation converges to the moment formula
`structureConstant` for `C`. -/
theorem structureConstant_infinity_limit {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ α₁ α₂ α₃ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hμ : 0 < μ)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ < α₁ + α₂ + α₃)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    Tendsto
      (fun z : ℂ => ‖z‖ ^ (4 * (conformalWeight γ (α₃ : ℂ)).re) *
        threePointFiniteCorrelation P M γ μ α₁ α₂ α₃ z)
      (Filter.cocompact ℂ)
      (nhds (structureConstant P M γ μ α₁ α₂ α₃)) := by exact DOZZ.Proofs.structureConstant_infinity_limit P X M γ μ α₁ α₂ α₃ hγ hγ₂ hμ hα₁ hα₂ hα₃ hs hX hM

end DOZZ

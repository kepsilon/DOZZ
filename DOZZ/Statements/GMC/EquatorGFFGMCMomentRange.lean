/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.GmcMassMoment
import DOZZ.GMC.SharpMoments.MomentRange

/-! The statement `DOZZ.equatorGFF_GMC_moment_range`,
proved by `DOZZ.Proofs.equatorGFF_GMC_moment_range`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- On each bounded nonempty open set the moment is finite exactly for `p < 4/γ²`, including all
negative `p`; at and above the endpoint it diverges. See [KRV, (condmom)]. -/
theorem equatorGFF_GMC_moment_range
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (O : Set ℂ)
    (hOopen : IsOpen O) (hObounded : Bornology.IsBounded O) (hOne : O.Nonempty)
    (p : ℝ) :
    (gmcMassMoment P M O p < ⊤) ↔ p < 4 / γ ^ 2 := by exact DOZZ.Proofs.equatorGFF_GMC_moment_range P X hX γ hγ hγ2 M hM O hOopen hObounded hOne p

end DOZZ

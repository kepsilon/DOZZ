/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.WeightedGmcBallMoment
import DOZZ.GMC.SharpMoments.WeightedLocalRange

/-! The statement `DOZZ.equatorGFF_GMC_weighted_local_moment_range`,
proved by `DOZZ.Proofs.equatorGFF_GMC_weighted_local_moment_range`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Sharp one-root weighted local moment threshold: for `α < Q`, positive orders are finite
exactly below both the GMC bulk threshold and the insertion threshold. See [KRV, (annulus)], with
the global domain [KRV, (ThextendedSeibergbounds)]. -/
theorem equatorGFF_GMC_weighted_local_moment_range
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (α : ℝ) (hα : α < Q γ)
    (p : ℝ) (hp : 0 < p) (z : ℂ) (r : ℝ) (hr : 0 < r) :
    (weightedGmcBallMoment P M γ α z r p < ⊤) ↔
      p < min (4 / γ ^ 2) (2 / γ * (Q γ - α)) := by exact DOZZ.Proofs.equatorGFF_GMC_weighted_local_moment_range P X hX γ hγ hγ2 M hM α hα p hp z r hr

end DOZZ

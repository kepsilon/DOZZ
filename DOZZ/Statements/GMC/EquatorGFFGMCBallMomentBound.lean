/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.GmcMassMoment
import DOZZ.GMC.BallAnnulus.Ball

/-! The statement `DOZZ.equatorGFF_GMC_ball_moment_bound`,
proved by `DOZZ.Proofs.equatorGFF_GMC_ball_moment_bound`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- Two-sided ball-mass scaling with one constant uniform on compact center sets. See
[KRV, (momentscaling)]. -/
theorem equatorGFF_GMC_ball_moment_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (p : ℝ) (hp : p < 4 / γ ^ 2) (K : Set ℂ) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ K, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ENNReal.ofReal (C⁻¹ * Real.rpow ε (γ * Q γ * p - γ ^ 2 * p ^ 2 / 2)) ≤
          gmcMassMoment P M (Metric.ball z ε) p ∧
        gmcMassMoment P M (Metric.ball z ε) p ≤
          ENNReal.ofReal (C * Real.rpow ε (γ * Q γ * p - γ ^ 2 * p ^ 2 / 2)) := by exact DOZZ.Proofs.equatorGFF_GMC_ball_moment_bound P X hX γ hγ hγ2 M hM p hp K hK

end DOZZ

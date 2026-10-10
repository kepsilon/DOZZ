/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.GmcMassMoment
import DOZZ.GMC.BallAnnulus.Annulus

/-! The statement `DOZZ.equatorGFF_GMC_annulus_moment_bound`,
proved by `DOZZ.Proofs.equatorGFF_GMC_annulus_moment_bound`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ

/-- The annulus estimate of [KRV, (annulus)], including negative orders and compact-uniform
centers. -/
theorem equatorGFF_GMC_annulus_moment_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (α p : ℝ) (hp : p < 4 / γ ^ 2)
    (K : Set ℂ) (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ z ∈ K, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (∫⁻ ω, ENNReal.rpow
          (∫⁻ x in {x : ℂ | ε < ‖x - z‖ ∧ ‖x - z‖ < 2 * ε},
            ENNReal.ofReal (‖x - z‖ ^ (-γ * α)) ∂M ω) p ∂P) ≤
        ENNReal.ofReal (C * Real.rpow ε
          (γ * (Q γ - α) * p - γ ^ 2 * p ^ 2 / 2)) := by exact DOZZ.Proofs.equatorGFF_GMC_annulus_moment_bound P X hX γ hγ hγ2 M hM α p hp K hK

end DOZZ

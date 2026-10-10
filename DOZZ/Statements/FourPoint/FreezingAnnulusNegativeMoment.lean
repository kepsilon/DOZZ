/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.FreezingAnnulusMass
import DOZZ.FourPoint.FreezingAnnulusNegativeMoment

/-! The statement `DOZZ.freezing_annulus_negative_moment`,
proved by `DOZZ.Proofs.freezing_annulus_negative_moment`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The supercritical freezing negative-moment estimate [KRV, (freezingannulus)], with its exact
charge threshold and the constant uniform in `0 < ε ≤ 1`. -/
theorem freezing_annulus_negative_moment {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (X : Ω → Distr)
    (γ α p : ℝ) (z : ℂ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hX : IsEquatorGFF P X)
    (hGMC : IsGMCOf P X γ M)
    (hα : Q γ < α) (hp : 0 < p) (hthreshold : α - Q γ < γ * p) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        (∫⁻ ω, ENNReal.rpow
          (freezingAnnulusMass γ α (M ω) z ε) (-p) ∂P) ≤
            ENNReal.ofReal (C * ε ^ ((α - Q γ) ^ 2 / 2)) := by exact DOZZ.Proofs.freezing_annulus_negative_moment P M X γ α p z hγ hγ₂ hX hGMC hα hp hthreshold

end DOZZ

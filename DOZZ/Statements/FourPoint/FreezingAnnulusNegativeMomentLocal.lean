/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.FreezingAnnulusMassLocal
import DOZZ.FourPoint.FreezingAnnulusNegativeMomentLocal

/-! The statement `DOZZ.freezing_annulus_negative_moment_local`,
proved by `DOZZ.Proofs.freezing_annulus_negative_moment_local`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- Localized freezing, with the constant uniform over centers in a compact set (used in
[KRV, §9.2]). It implies the unbounded form [KRV, (freezingannulus)]. -/
theorem freezing_annulus_negative_moment_local {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (X : Ω → Distr)
    (γ α p R : ℝ) (K : Set ℂ) (hK : IsCompact K)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hX : IsEquatorGFF P X)
    (hGMC : IsGMCOf P X γ M) (hR : 0 < R)
    (hα : Q γ < α) (hp : 0 < p) (hthreshold : α - Q γ < γ * p) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
      ∀ z ∈ K, ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        (∫⁻ ω, ENNReal.rpow (freezingAnnulusMassLocal γ α (M ω) z ε R) (-p) ∂P) ≤
          ENNReal.ofReal (C * ε ^ ((α - Q γ) ^ 2 / 2)) := by exact DOZZ.Proofs.freezing_annulus_negative_moment_local P M X γ α p R K hK hγ hγ₂ hX hGMC hR hα hp hthreshold

end DOZZ

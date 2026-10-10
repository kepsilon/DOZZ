/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Shift.Wrappers
public import DOZZ.FourPoint.Crossing.GammaHalfCrossing

/-! Proof of `DOZZ.reflectionR_first_shift_meromorphic` from the unit-volume conjunct of the γ/2
crossing `DOZZ.gammaHalf_crossing`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

theorem reflectionR_first_shift_meromorphic
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hμ : 0 < μ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∃ B : ℝ → Ω → BrownianPath ×
        BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α : ℝ, γ / 2 < α → α < Q γ →
            IsReflectionData P γ α (B α) Z) ∧
            ∃ h : ℝ, 0 < h ∧ ∃ R : ℂ → ℂ,
              MeromorphicOn R {z | |z.im| < h} ∧
              (∀ α : ℝ, γ / 2 < α → α < Q γ →
                R (α : ℂ) =
                  (reflectionR P γ μ α (B α) Z : ℂ)) ∧
              ∀ᶠ z in codiscrete ℂ,
                R (z - γ / 2) =
                  -(μ * Real.pi : ℂ) * R z /
                    (lFun (-((γ : ℂ) ^ 2) / 4) *
                      lFun ((γ : ℂ) * z / 2 - (γ : ℂ) ^ 2 / 4) *
                      lFun (2 + (γ : ℂ) ^ 2 / 2 - (γ : ℂ) * z / 2)) := by
  exact reflectionR_first_shift_meromorphic_of_crossing P X M γ μ hγ hγ2 hμ hX hM
    (fun μ' α' ε α hμ' h1 h2 h3 h4 h5 =>
      (gammaHalf_crossing P X M γ μ' α' ε α hγ hγ2 hμ' h1 h2 h3 h4 h5 hX hM).2)

end DOZZ.Proofs

end

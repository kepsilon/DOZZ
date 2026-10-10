/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.DualR.Wrapper
public import DOZZ.FourPoint.Crossing.GammaHalfCrossing
public import DOZZ.FourPoint.Dual.FullFusion
public import DOZZ.ShiftEquations.Shifts.Seeds.SeedTwo

/-! Proof of `DOZZ.reflectionR_dual_shift_unknown_constant` from the unit-volume conjunct of the γ/2
crossing `DOZZ.gammaHalf_crossing` and the second dual crossing seed, obtained from the dual fusion
statement `DOZZ.dual_full_fusion_and_asymptotic` via `dual_crossing_seed_two_of_fusion`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

theorem reflectionR_dual_shift_unknown_constant
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hγirr : Irrational (γ ^ 2)) (hμ : 0 < μ)
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
              ∃ cγ : ℂ, cγ ≠ 0 ∧
                cγ = ((γ : ℂ) ^ 2 / 4) * (μ * Real.pi : ℂ) * R γ ∧
                ∀ᶠ z in codiscrete ℂ,
                  R z = -cγ * R (z + 2 / γ) /
                    (lFun (-4 / (γ : ℂ) ^ 2) * lFun (2 * z / γ) *
                      lFun (2 + 4 / (γ : ℂ) ^ 2 - 2 * z / γ)) := by
  exact reflectionR_dual_shift_unknown_constant_of_crossing_seed P X M γ μ hγ hγ2 hγirr hμ hX hM
    (fun μ' α' ε α hμ' h1 h2 h3 h4 h5 =>
      (gammaHalf_crossing P X M γ μ' α' ε α hγ hγ2 hμ' h1 h2 h3 h4 h5 hX hM).2)
    (fun α ε α' hα hε hα' hs => dual_crossing_seed_two_of_fusion
      (fun hH P M X γ μ α₁ α₂ α₃ η ξ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 hX hM =>
        dual_full_fusion_and_asymptotic hH P M X γ μ α₁ α₂ α₃ η ξ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
          h11 h12 h13 h14 hX hM)
      P M X γ μ α ε α' hγ hγ2 hμ hα hε hα' hs hX hM)

end DOZZ.Proofs

end

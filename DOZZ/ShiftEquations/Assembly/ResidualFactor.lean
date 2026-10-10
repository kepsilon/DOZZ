/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Residual.Composition
public import DOZZ.FourPoint.Crossing.GammaHalfCrossing
public import DOZZ.FourPoint.Dual.FullFusion
public import DOZZ.FourPoint.SeedOne.Assembly
public import DOZZ.ShiftEquations.Shifts.Seeds.SeedTwo
public import DOZZ.ShiftEquations.Shifts.Rtheor

/-! Proof of `DOZZ.unitVolume_residual_factor_eq_one` (the single input of the main theorems
`DOZZ.dozz_main` and `DOZZ.dozz_unitVolume`): a reduction to the γ/2 crossing
`DOZZ.gammaHalf_crossing`, the two dual crossing seeds and the identification of the reflection
coefficient off its poles. Seed one is `DOZZ.dual_crossing_seed_one`; seed two and the off-pole
identification come from the dual fusion statement `DOZZ.dual_full_fusion_and_asymptotic` through
the reductions `dual_crossing_seed_two_of_fusion` and `reflection_Rtheor_off_poles_of_seedTwo`. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

theorem unitVolume_residual_factor_eq_one
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ μ η : ℝ) (U : ℂ → ℂ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hγirr : Irrational (γ ^ 2)) (hμ : 0 < μ)
    (hη : 0 < η ∧ Q γ - 2 * η > γ ∧ 3 * η < Q γ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hU : IsUpsilon γ U) :
    ∃ B : ℝ → Ω → BrownianPath ×
        BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α, γ / 2 < α → α < Q γ →
            IsReflectionData P γ α (B α) Z) ∧
            ∃ cγ : ℂ, cγ = 1 ∧
              ∀ α₁ α₂ α₃ : ℝ,
                Q γ - η < α₁ → α₁ < Q γ →
                Q γ - η < α₂ → α₂ < Q γ →
                Q γ - η < α₃ → α₃ < Q γ →
                  (unitVolumeStructureConstant P M γ α₁ α₂ α₃ : ℂ) =
                    cγ * ((μ : ℂ) ^ ((sExp γ α₁ α₂ α₃ : ℂ)) /
                      Complex.Gamma (sExp γ α₁ α₂ α₃ : ℂ) *
                        dozzFormula γ μ U (α₁ : ℂ) (α₂ : ℂ) (α₃ : ℂ)) := by
  exact unitVolume_residual_factor_eq_one_of_crossing_seeds P X M γ μ η U hγ hγ2 hγirr hμ hη hX hM hU
    (fun P X M γ μ α' ε α hγ hγ₂ hμ h1 h2 h3 h4 h5 hX hM =>
      gammaHalf_crossing P X M γ μ α' ε α hγ hγ₂ hμ h1 h2 h3 h4 h5 hX hM)
    (fun P M X γ μ α ε α' hγ hγ₂ hμ hα hε hα' hs hX hM =>
      dual_crossing_seed_one P M X γ μ α ε α' hγ hγ₂ hμ hα hε hα' hs hX hM)
    (fun P M X γ μ α ε α' hγ hγ₂ hμ hα hε hα' hs hX hM =>
      dual_crossing_seed_two_of_fusion
      (fun hH P M X γ μ α₁ α₂ α₃ η ξ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 hX hM =>
        dual_full_fusion_and_asymptotic hH P M X γ μ α₁ α₂ α₃ η ξ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
          h11 h12 h13 h14 hX hM)
      P M X γ μ α ε α' hγ hγ₂ hμ hα hε hα' hs hX hM)
    (fun P γ μ α hγ hγ2 hμ hα hPole B Z hData =>
      reflection_Rtheor_off_poles_of_seedTwo
        (fun P M X γ μ α ε α' hγ hγ₂ hμ hα hε hα' hs hX hM =>
          dual_crossing_seed_two_of_fusion
          (fun hH P M X γ μ α₁ α₂ α₃ η ξ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 hX hM =>
        dual_full_fusion_and_asymptotic hH P M X γ μ α₁ α₂ α₃ η ξ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
          h11 h12 h13 h14 hX hM)
          P M X γ μ α ε α' hγ hγ₂ hμ hα hε hα' hs hX hM)
        P γ μ α hγ hγ2 hμ hα hPole B Z hData)

end DOZZ.Proofs

end

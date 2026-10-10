/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.ShiftEquations.TwoPoleWindow
import DOZZ.ShiftEquations.Assembly.ResidualFactor

/-! The statement `DOZZ.unitVolume_residual_factor_eq_one`,
proved by `DOZZ.Proofs.unitVolume_residual_factor_eq_one`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- For irrational `γ²`, symmetry and continuation make the residual factor independent of all three
charges ([KRV, §11]), and the corrected equal-charge three-to-two bridge fixes that scalar to 1.
This is stated on a strict near-`Q` cube, where `s > 0` and no Gamma pole occurs. -/
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
                        dozzFormula γ μ U (α₁ : ℂ) (α₂ : ℂ) (α₃ : ℂ)) := by exact DOZZ.Proofs.unitVolume_residual_factor_eq_one P X M γ μ η U hγ hγ2 hγirr hμ hη hX hM hU

end DOZZ

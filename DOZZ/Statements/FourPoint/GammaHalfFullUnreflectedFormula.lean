/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.IsComplexLittleOAtZero
import DOZZ.FourPoint.BPZ.GammaHalfFullUnreflectedFormula

/-! The statement `DOZZ.gammaHalf_full_unreflected_formula`,
proved by `DOZZ.Proofs.gammaHalf_full_unreflected_formula`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The full unreflected `γ/2` diagonal formula [KRV, Theorem 9.1] on its exact interval. This
includes `γ² = 2`, by continuity in `γ` at fixed nonzero `z` before any fusion limit. -/
theorem gammaHalf_full_unreflected_formula {Ω : Type*} [MeasurableSpace Ω]
    {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H)
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ α₁ α₂ α₃ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hμ : 0 < μ)
    (hαlo : γ / 2 < α₁) (hαhi : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    let a := gaussParameterA γ (γ / 2) α₁ α₂ α₃
    let b := gaussParameterB γ (γ / 2) α₁ α₂ α₃
    let c := gaussParameterC γ (γ / 2) α₁
    ∀ z ∈ gaussCutPlane,
      fourPointT P M γ μ (-γ / 2) α₁ α₂ α₃ z =
        structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ *
            ‖gaussFMinus H a b c z‖ ^ 2 +
          (-μ * (planarGaussConstant (γ ^ 2 / 2) (γ * α₁)).re) *
            structureConstant P M γ μ (α₁ + γ / 2) α₂ α₃ *
              ‖gaussFPlus H a b c z‖ ^ 2 := by exact DOZZ.Proofs.gammaHalf_full_unreflected_formula hH P X M γ μ α₁ α₂ α₃ hγ hγ₂ hμ hαlo hαhi hα₂ hα₃ hs hX hM

end DOZZ

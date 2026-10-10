/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.GammaHalfOuterMoment
import DOZZ.FourPoint.ReflectedOuter.GammaHalfReflectedOuterLittleO

/-! The statement `DOZZ.gammaHalf_reflected_outer_littleO`,
proved by `DOZZ.Proofs.gammaHalf_reflected_outer_littleO`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The reflected outer-region correction is `o(|z|^κ)`. The buffer `ξ` is required to exceed the
local fusion exponent on the stated neighborhood. -/
theorem gammaHalf_reflected_outer_littleO {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ ξ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hξ : 0 < ξ) (hξ₂ : ξ < 1)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃)
    (hα₁ : α₁ < Q γ) (hreflect : Q γ - α₁ < γ / 2)
    (hslack : γ * (Q γ - α₁) < ξ)
    (hfreeze : γ * (Q γ - α₁) <
      (1 - ξ) * (γ * (Q γ - α₁) + (α₁ + γ / 2 - Q γ) ^ 2 / 2))
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    IsComplexLittleOAtZero (γ * (Q γ - α₁))
      (fun z : ℂ =>
        ((gammaHalfOuterMoment P M γ α₁ α₂ α₃
            ((α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ) z ξ -
          gammaHalfMoment P M γ α₁ α₂ α₃
            ((α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ) 0 : ℝ) : ℂ)) := by exact DOZZ.Proofs.gammaHalf_reflected_outer_littleO P X M γ α₁ α₂ α₃ ξ hγ hγ₂ hξ hξ₂ hα₂ hα₃ hs hα₁ hreflect hslack hfreeze hX hM

end DOZZ

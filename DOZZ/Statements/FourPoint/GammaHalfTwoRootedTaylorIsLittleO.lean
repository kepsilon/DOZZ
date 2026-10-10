/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.IsComplexLittleOAtZero
import DOZZ.FourPoint.GammaHalfTwoRootedTaylorIsLittleO

/-! The statement `DOZZ.gammaHalf_twoRooted_Taylor_is_littleO`,
proved by `DOZZ.Proofs.gammaHalf_twoRooted_Taylor_is_littleO`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The two-rooted correction is negligible in the supercritical domain [KRV, Lemma 9.3]. The `γ`
bound is strict here because the diagonal integral of the paper requires `γ² > 2`. -/
theorem gammaHalf_twoRooted_Taylor_is_littleO {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hγsq : 2 < γ ^ 2)
    (hα₁ : γ / 2 < α₁) (hα₁₂ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    IsComplexLittleOAtZero (γ * (Q γ - α₁))
      (gammaHalfTwoRootedTerm P M γ α₁ α₂ α₃
        ((α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ)) := by exact DOZZ.Proofs.gammaHalf_twoRooted_Taylor_is_littleO P X M γ α₁ α₂ α₃ hγ hγ₂ hγsq hα₁ hα₁₂ hα₂ hα₃ hs hX hM

end DOZZ

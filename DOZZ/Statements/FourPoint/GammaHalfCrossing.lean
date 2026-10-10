/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.GammaHalfUnitCrossingMultiplier
import DOZZ.FourPoint.Crossing.GammaHalfCrossing

/-! The statement `DOZZ.gammaHalf_crossing`, proved by `DOZZ.Proofs.gammaHalf_crossing`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The ordinary `γ/2` crossing relation [KRV, Proposition 9.8] on its physical domain. The
equivalent unit-volume identity is recorded as a paired conclusion, using the Gamma ratio of the
same proposition. -/
theorem gammaHalf_crossing {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ α' ε α : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hμ : 0 < μ)
    (hεlo : γ / 2 < ε) (hεhi : ε < 2 / γ)
    (hα : α < Q γ) (hα' : α' < Q γ)
    (hs : 2 * Q γ < α + α' + ε - γ / 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    structureConstant P M γ μ (α' - γ / 2) ε α =
        gammaHalfCrossingMultiplier γ μ α' ε α *
          structureConstant P M γ μ α' (ε + γ / 2) α ∧
      unitVolumeStructureConstant P M γ (α' - γ / 2) ε α =
        gammaHalfUnitCrossingMultiplier γ μ α' ε α *
          unitVolumeStructureConstant P M γ α' (ε + γ / 2) α := by exact DOZZ.Proofs.gammaHalf_crossing P X M γ μ α' ε α hγ hγ₂ hμ hεlo hεhi hα hα' hs hX hM

end DOZZ

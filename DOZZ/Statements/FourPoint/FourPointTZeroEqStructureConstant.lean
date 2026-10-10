/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.ThreePointFiniteCorrelation
import DOZZ.FourPoint.FourPointTZeroEqStructureConstant

/-! The statement `DOZZ.fourPointT_zero_eq_structureConstant`,
proved by `DOZZ.Proofs.fourPointT_zero_eq_structureConstant`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- Fusing the degenerate insertion at zero changes the first three-point charge by `-χ`
([KRV, (Fundrelation1)]). -/
theorem fourPointT_zero_eq_structureConstant {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ μ χ α₁ α₂ α₃ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hμ : 0 < μ)
    (hα₁ : α₁ - χ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ < α₁ + α₂ + α₃ - χ)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    fourPointT P M γ μ (-χ) α₁ α₂ α₃ 0 =
      structureConstant P M γ μ (α₁ - χ) α₂ α₃ := by exact DOZZ.Proofs.fourPointT_zero_eq_structureConstant P X M γ μ χ α₁ α₂ α₃ hγ hγ₂ hμ hα₁ hα₂ hα₃ hs hX hM

end DOZZ

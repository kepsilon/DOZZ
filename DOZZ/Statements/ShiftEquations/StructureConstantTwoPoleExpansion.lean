/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.ShiftEquations.TwoPoleWindow
import DOZZ.ShiftEquations.TwoPole.Assembly

/-! The statement `DOZZ.structureConstant_two_pole_expansion`,
proved by `DOZZ.Proofs.structureConstant_two_pole_expansion`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- The tail-subtracted Mellin transform has exactly the two simple residues
[KRV, Proposition 10.1]. The coefficients below are the corrected coefficients of erratum K26 (see
docs/ERRATA-AND-DEVIATIONS.md) after the separated insertion position factors cancel; the remainder
is analytic across both poles. -/
theorem structureConstant_two_pole_expansion
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ η δ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hX : IsEquatorGFF P X)
    (hM : IsGMCOf P X γ M)
    (hWindow : TwoPoleWindow γ η δ) :
    ∃ B : ℝ → Ω → BrownianPath ×
        BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          IsReflectionData P γ (2 / γ + η)
            (B (2 / γ + η)) Z ∧
          IsReflectionData P γ (Q γ - η - γ / 2)
            (B (Q γ - η - γ / 2)) Z ∧
            ∃ V : Set ℂ, IsOpen V ∧
              (∀ x : ℝ, -2 * η - δ < x ∧ x < 1 / γ → (x : ℂ) ∈ V) ∧
              ∃ F r : ℂ → ℂ,
                MeromorphicOn F V ∧ DifferentiableOn ℂ r V ∧
                (∀ x : ℝ, 2 * η < x ∧ x < 1 / γ →
                  F (x : ℂ) =
                    (unitVolumeStructureConstant P M γ (Q γ - η - γ / 2) x
                      (2 / γ + η) : ℂ)) ∧
                ∀ᶠ z in codiscrete ℂ, z ∈ V →
                  F z =
                    (twoPoleFirstResidue P γ B Z η : ℂ) / (z - 2 * η) +
                    (twoPoleSecondResidue P γ B Z η : ℂ) / (z + 2 * η) + r z := by exact DOZZ.Proofs.structureConstant_two_pole_expansion P X M γ η δ hγ hγ2 hX hM hWindow

end DOZZ

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.ShiftEquations.TwoPoleSecondResidue
import DOZZ.ShiftEquations.Assembly.BarRRepresentation

/-! The statement `DOZZ.reflectionBarR_holomorphic_representation`,
proved by `DOZZ.Proofs.reflectionBarR_holomorphic_representation`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- On every compact subinterval of `(γ/2, Q)`, the reflection moment has a holomorphic extension
represented by the exact multiple of `Cbar(α, γ, α)` ([KRV, (formulaforbarR)]). The coefficient
`rbarCoefficient` carries the corrected constant `+2π/γ` (erratum K29, see
docs/ERRATA-AND-DEVIATIONS.md). -/
theorem reflectionBarR_holomorphic_representation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (I : Set ℝ) (hIcompact : IsCompact I)
    (hI : ∀ α ∈ I, γ / 2 < α ∧ α < Q γ) :
    ∃ B : ℝ → Ω → BrownianPath ×
        BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
          (∀ α ∈ I,
            IsReflectionData P γ α (B α) Z) ∧
            ∃ V : Set ℂ, IsOpen V ∧
              (∀ α ∈ I, (α : ℂ) ∈ V) ∧
              ∃ f : ℂ → ℂ, DifferentiableOn ℂ f V ∧
                (∀ α ∈ I,
                  f (α : ℂ) =
                    (unitVolumeStructureConstant P M γ α γ α : ℂ)) ∧
                DifferentiableOn ℂ
                  (fun z => rbarCoefficient γ z * f z) V ∧
                (∀ α ∈ I,
                  rbarCoefficient γ (α : ℂ) * f (α : ℂ) =
                    (reflectionBarR P γ α (B α) Z : ℂ)) := by exact DOZZ.Proofs.reflectionBarR_holomorphic_representation P X M γ hγ hγ2 hX hM I hIcompact hI

end DOZZ

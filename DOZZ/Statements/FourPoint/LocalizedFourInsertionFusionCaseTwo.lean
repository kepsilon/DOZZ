/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.FourFusionMass
import DOZZ.FourPoint.LocalizedFourInsertionFusionCaseTwo

/-! The statement `DOZZ.localized_four_insertion_fusion_case_two`,
proved by `DOZZ.Proofs.localized_four_insertion_fusion_case_two`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- Generalized localized four-insertion fusion estimate, case two. -/
theorem localized_four_insertion_fusion_case_two {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ R : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hR : 0 < R)
    (K : Set ℂ) (hK : IsCompact K)
    (A : Set (Fin 4 → ℝ)) (hA : IsCompact A)
    (S : Set ℝ) (hS : IsCompact S)
    (hcharges : ∀ α ∈ A, ∀ i : Fin 4, α i < Q γ)
    (horders : ∀ α ∈ A, ∀ q ∈ S,
      0 < q ∧ q ≥ fourFusionNu4 γ α / γ)
    (hcase : ∀ α ∈ A, ∀ q ∈ S,
      0 < fourFusionNu2 γ α ∧ 0 ≤ fourFusionNu3 γ α ∧
        α 2 ≤ 0 ∧ 0 ≤ α 2 + α 3)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∃ C : ℝ, 0 < C ∧
      ∀ α ∈ A, ∀ q ∈ S, ∀ y : Fin 4 → ℂ,
        (∀ i, y i ∈ K) → OrderedFourFusionCenters y →
        (∀ i j : Fin 4, i ≠ j → y i ≠ y j) →
        (∫⁻ ω, ENNReal.rpow (fourFusionMass γ (M ω) α y R) (-q) ∂P) ≤
          ENNReal.ofReal (C * (‖y 0 - y 1‖ / ‖y 0 - y 2‖) ^
                (fourFusionNu2 γ α ^ 2 / 2) *
            (‖y 0 - y 2‖ / ‖y 0 - y 3‖) ^
                ((fourFusionNu3 γ α ^ 2 - (α 2) ^ 2) / 2) *
              ‖y 0 - y 3‖ ^ (fourFusionNu4 γ α ^ 2 / 2)) := by exact DOZZ.Proofs.localized_four_insertion_fusion_case_two P X M γ R hγ hγ₂ hR K hK A hA S hS hcharges horders hcase hX hM

end DOZZ

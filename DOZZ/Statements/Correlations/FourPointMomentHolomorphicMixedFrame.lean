/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Correlations.BridgeMultiplicity
import DOZZ.Correlations.Analytic.FourPointHolomorphic

/-! The statement `DOZZ.fourPointMoment_holomorphic_mixed_frame`,
proved by `DOZZ.Proofs.fourPointMoment_holomorphic_mixed_frame`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- Holomorphic extension for the four-point moment with insertion points `(z, 0, 1, ∞)`. -/
theorem fourPointMoment_holomorphic_mixed_frame
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) (z : ℂ) (hz : z ≠ 0 ∧ z ≠ 1) :
    ∃ V : Set (Fin 4 → ℂ), IsOpen V ∧
      (∀ α : Fin 4 → ℝ, (∀ i, α i < Q γ) → 0 < nPointSExp γ α →
        complexifyNCharges α ∈ V) ∧
      ∃ f : (Fin 4 → ℂ) → ℂ, DifferentiableOn ℂ f V ∧
        ∀ α : Fin 4 → ℝ, (∀ i, α i < Q γ) → 0 < nPointSExp γ α →
          f (complexifyNCharges α) =
            ((∫⁻ ω, ENNReal.rpow
              (coulombMass γ (M ω) ![α 0, α 1, α 2] ![z, 0, 1] (α 3))
              (-nPointSExp γ α) ∂P).toReal : ℂ) := by exact DOZZ.Proofs.fourPointMoment_holomorphic_mixed_frame P X M γ hγ hγ2 hX hM z hz

end DOZZ

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Correlations.ComplexifyNCharges
import DOZZ.Correlations.Analytic.NPointHolomorphic

/-! The statement `DOZZ.unitVolumeNPoint_holomorphic_near_extended_domain`,
proved by `DOZZ.Proofs.unitVolumeNPoint_holomorphic_near_extended_domain`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- Analytic continuation ([KRV, Theorem 6.1]): for fixed distinct insertion points, the real
unit-volume N-point moment on `U_N` is the restriction of a jointly holomorphic function on a
complex neighborhood of `U_N`. The neighborhood is controlled in the maximum norm on the charges. -/
theorem unitVolumeNPoint_holomorphic_near_extended_domain
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (hN : 3 ≤ N)
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hX : IsEquatorGFF P X)
    (hM : IsGMCOf P X γ M) (z : Fin N → ℂ)
    (hz : ∀ i j, i ≠ j → z i ≠ z j) :
    ∃ V : Set (Fin N → ℂ), IsOpen V ∧
      (∀ α : Fin N → ℝ, ExtendedSeibergN γ α → complexifyNCharges α ∈ V) ∧
      ∃ f : (Fin N → ℂ) → ℂ,
        DifferentiableOn ℂ f V ∧
          ∀ α : Fin N → ℝ, ExtendedSeibergN γ α →
            f (complexifyNCharges α) =
              (unitVolumeNPointCorrelation P M γ α z : ℂ) := by exact DOZZ.Proofs.unitVolumeNPoint_holomorphic_near_extended_domain hN P X M γ hγ hγ2 hX hM z hz

end DOZZ

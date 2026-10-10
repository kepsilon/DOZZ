/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.ShiftEquations.MobiusMap
import DOZZ.ShiftEquations.Mobius.Covariance

/-! The statement `DOZZ.unitVolumeNPoint_mobius_covariance_extended`,
proved by `DOZZ.Proofs.unitVolumeNPoint_mobius_covariance_extended`. -/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ

/-- For every real extended-Seiberg charge vector, the finite-position unit-volume moment transforms
with the primary weights, including at `s = 0` and at negative integers. The statement uses the
literal finite-position formula of [KRV, (Z1)] and [KRV, (unitvol)], so no ordinary zero-mode
integral is being continued through `s ≤ 0`. -/
theorem unitVolumeNPoint_mobius_covariance_extended
    {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (hN : 3 ≤ N)
    (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ) (γ : ℝ)
    (α : Fin N → ℝ) (z : Fin N → ℂ) (ψ : MobiusChart)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M)
    (hα : ExtendedSeibergN γ α)
    (hz : ∀ i j, i ≠ j → z i ≠ z j)
    (hfinite : ∀ i, ψ.c * z i + ψ.d ≠ 0) :
    unitVolumeNPointCorrelation P M γ α
        (fun i => mobiusMap ψ (z i)) =
      (∏ i : Fin N,
        Real.rpow ‖deriv (mobiusMap ψ) (z i)‖
          (-2 * (conformalWeight γ (α i : ℂ)).re)) *
        unitVolumeNPointCorrelation P M γ α z := by exact DOZZ.Proofs.unitVolumeNPoint_mobius_covariance_extended hN P X M γ α z ψ hγ hγ2 hX hM hα hz hfinite

end DOZZ

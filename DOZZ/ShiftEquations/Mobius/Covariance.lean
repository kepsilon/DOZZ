/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.ShiftEquations.MobiusMap
import DOZZ.ShiftEquations.Mobius.MomentCovariance

/-!
# Möbius covariance of the unit-volume N-point moment

The finite-position unit-volume moment is `2/γ · C(α, z) · E[I_z^{-s}]` with the Coulomb prefactor
`C(α, z) = ∏_{i<k} |zᵢ - zₖ|^{-αᵢαₖ}`. Under a chart `ψ` with finite images, the chord identity
`|ψzᵢ - ψzₖ|² = |ψ'(zᵢ)| |ψ'(zₖ)| |zᵢ - zₖ|²` turns the prefactor into
`∏ᵢ |ψ'(zᵢ)|^{-αᵢ(Σα - αᵢ)/2} C(α, z)`, and the moment picks up `∏ᵢ |ψ'(zᵢ)|^{γ αᵢ s / 2}`
(`coulombMass_mobius_moment`). The exponents add to `-2 Re Δ_{αᵢ}` (`mobius_weight_exponent`). No
zero-mode integral is continued, so the identity holds for every real charge vector, including
`s ≤ 0`.
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

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
        unitVolumeNPointCorrelation P M γ α z := by
  have _ := hN
  have _ := hα
  have _ := hz
  have hj : ∀ i, 0 < ‖deriv (mobiusMap ψ) (z i)‖ := fun i =>
    norm_deriv_mobiusMap_pos ψ (hfinite i)
  have hpre := nPointCoulombPrefactor_eq_of_dist α z (fun i => mobiusMap ψ (z i))
    (fun i => ‖deriv (mobiusMap ψ) (z i)‖) hj
    fun i k _ => norm_mobiusMap_sub_sq ψ (hfinite i) (hfinite k)
  have hweight : ∏ i : Fin N, Real.rpow ‖deriv (mobiusMap ψ) (z i)‖
        (-2 * (conformalWeight γ (α i : ℂ)).re) =
      (∏ i, ‖deriv (mobiusMap ψ) (z i)‖ ^ (-(α i * ((∑ k, α k) - α i)) / 2)) *
        ∏ i, ‖deriv (mobiusMap ψ) (z i)‖ ^ (γ * α i * nPointSExp γ α / 2) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Real.rpow_eq_pow, ← Real.rpow_add (hj i), mobius_weight_exponent γ hγ.ne' α i]
  unfold unitVolumeNPointCorrelation
  rw [hpre, coulombMass_mobius_moment P X hX γ hγ hγ2 M hM α z ψ hfinite, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ => (Real.rpow_pos_of_pos (hj i) _).le),
    hweight]
  ring

end DOZZ.Proofs

end

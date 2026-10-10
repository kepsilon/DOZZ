/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.GammaHalfUnitCrossingMultiplier
public import DOZZ.Correlations.Residue.FullFromUnit
import Mathlib.Tactic

/-! # The unit-volume normalization of half-charge crossing

The zero-mode orders differ by exactly one. Cancellation uses positive Gamma
arguments and a positive cosmological constant, so no totalized pole is divided out.
-/

public section
open MeasureTheory
namespace DOZZ.Proofs

/-- Removing the zero-mode normalization from a full crossing identity gives
exactly the unit-volume multiplier of [KRV, Proposition 9.8]. -/
theorem gammaHalf_crossing_unit_of_full {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (γ μ α' ε α : ℝ)
    (hγ : 0 < γ) (hμ : 0 < μ)
    (hs : 2 * Q γ < α + α' + ε - γ / 2)
    (hfull : structureConstant P M γ μ (α' - γ / 2) ε α =
      gammaHalfCrossingMultiplier γ μ α' ε α *
        structureConstant P M γ μ α' (ε + γ / 2) α) :
    unitVolumeStructureConstant P M γ (α' - γ / 2) ε α =
      gammaHalfUnitCrossingMultiplier γ μ α' ε α *
        unitVolumeStructureConstant P M γ α' (ε + γ / 2) α := by
  let s := sExp γ (α' - γ / 2) ε α
  have hspos : 0 < s := div_pos (by linarith only [hs]) hγ
  have hr : sExp γ α' (ε + γ / 2) α = s + 1 := by
    dsimp [s, sExp]
    field_simp
    ring
  have hleft : (α + α' + ε - γ / 2 - 2 * Q γ) / γ = s := by
    dsimp [s, sExp]
    congr 1
    ring
  have hright : (α + α' + ε + γ / 2 - 2 * Q γ) / γ = s + 1 := by
    rw [← hr]
    unfold sExp
    congr 1
    ring
  have hG : Real.Gamma s ≠ 0 := (Real.Gamma_pos_of_pos hspos).ne'
  have hp : μ ^ (-s) ≠ 0 := (Real.rpow_pos_of_pos hμ (-s)).ne'
  have hpow : μ ^ (-(s + 1)) = μ ^ (-s) * μ⁻¹ := by
    rw [show -(s + 1) = -s + -1 by ring, Real.rpow_add hμ, Real.rpow_neg_one]
  rw [residue_structureConstant_eq_unitVolume,
    residue_structureConstant_eq_unitVolume, hr, hpow] at hfull
  change μ ^ (-s) * Real.Gamma s * _ = _ at hfull
  unfold gammaHalfUnitCrossingMultiplier
  rw [hleft, hright]
  apply (mul_left_cancel₀ (mul_ne_zero hp hG))
  calc
    _ = gammaHalfCrossingMultiplier γ μ α' ε α *
        (μ ^ (-s) * μ⁻¹ * Real.Gamma (s + 1) *
          unitVolumeStructureConstant P M γ α' (ε + γ / 2) α) := hfull
    _ = _ := by field_simp [hG]

end DOZZ.Proofs

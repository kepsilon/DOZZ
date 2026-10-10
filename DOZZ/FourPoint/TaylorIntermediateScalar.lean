/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.TaylorMassInterpolation

/-! Endpoint-safe scalar reduction for the intermediate positive Taylor square. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Bound the absolute numerator, reduce the local square order, and insert the weighted mass.
All four masses may be zero or infinite; only the deterministic weights are finite positive. -/
theorem intermediate_scalar_bound (A L I W : ℝ≥0∞) (d w p s : ℝ)
    (hd : 0 < d) (hw : 0 < w) (hp : 0 ≤ p) (hs : 0 < s) (hs2 : s ≤ 2)
    (hA : A ≤ ENNReal.ofReal d⁻¹ * L) (hL : L ≤ I) (hW : L ≤ ENNReal.ofReal w * W) :
    A ^ 2 * I ^ (-p - 2) ≤ ENNReal.ofReal ((d⁻¹) ^ 2 * w ^ s) * (W ^ s * I ^ (-p - s)) := by
  have hcoef : 0 ≤ (d⁻¹) ^ 2 := sq_nonneg _
  calc
    A ^ 2 * I ^ (-p - 2) ≤ (ENNReal.ofReal d⁻¹ * L) ^ 2 * I ^ (-p - 2) :=
      mul_le_mul' (pow_le_pow_left' hA 2) le_rfl
    _ = (ENNReal.ofReal d⁻¹) ^ 2 * (L ^ 2 * I ^ (-p - 2)) := by
      rw [mul_pow, mul_assoc]
    _ ≤ (ENNReal.ofReal d⁻¹) ^ 2 * (L ^ s * I ^ (-p - s)) :=
      mul_le_mul' le_rfl (mass_interpolation_bound L I p s hp hs hs2 hL)
    _ ≤ (ENNReal.ofReal d⁻¹) ^ 2 * ((ENNReal.ofReal w * W) ^ s * I ^ (-p - s)) :=
      mul_le_mul' le_rfl (mul_le_mul' (ENNReal.rpow_le_rpow hW hs.le) le_rfl)
    _ = ENNReal.ofReal ((d⁻¹) ^ 2 * w ^ s) * (W ^ s * I ^ (-p - s)) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hs.le, ENNReal.ofReal_rpow_of_pos hw,
        ← ENNReal.ofReal_pow (inv_nonneg.mpr hd.le), ENNReal.ofReal_mul hcoef]
      ac_rfl

end DOZZ.Proofs

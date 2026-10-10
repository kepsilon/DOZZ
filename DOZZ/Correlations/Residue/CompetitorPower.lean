/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Residue.TailMoments

/-! Deterministic power comparisons for the noncritical mass. -/

@[expose] public section
open MeasureTheory Filter Topology Set
namespace DOZZ.Proofs

/-- A bounded higher moment controls all the positive powers below it. -/
theorem residue_rpow_le_one_add (x q r : ℝ) (hx : 0 ≤ x) (hq : 0 ≤ q) (hqr : q ≤ r) :
    x ^ q ≤ 1 + x ^ r := by
  rcases le_total x 1 with hx1 | hx1
  · exact (Real.rpow_le_one hx hx1 hq).trans (le_add_of_nonneg_right (Real.rpow_nonneg hx _))
  · exact (Real.rpow_le_rpow_of_exponent_le hx1 hqr).trans
      (le_add_of_nonneg_left zero_le_one)

/-- An adjustable comparison makes the multiplier of the critical moment arbitrarily close
 to one. It does not require independence between the critical mass and its competitor. -/
theorem residue_add_rpow_le (a b q δ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hq : 0 ≤ q) (hδ : 0 < δ) :
    (a + b) ^ q ≤ (1 + δ) ^ q * a ^ q + (1 + 1 / δ) ^ q * b ^ q := by
  rcases le_total b (δ * a) with hh | hh
  · calc (a + b) ^ q ≤ ((1 + δ) * a) ^ q :=
        Real.rpow_le_rpow (add_nonneg ha hb) (by nlinarith only [hh]) hq
      _ = (1 + δ) ^ q * a ^ q := Real.mul_rpow (by positivity) ha
      _ ≤ _ := le_add_of_nonneg_right (mul_nonneg (by positivity) (Real.rpow_nonneg hb _))
  · have hba : a ≤ b / δ := (le_div_iff₀ hδ).mpr (by simpa only [mul_comm] using hh)
    calc (a + b) ^ q ≤ ((1 + 1 / δ) * b) ^ q :=
        Real.rpow_le_rpow (add_nonneg ha hb) (by calc a + b ≤ b / δ + b := by linarith only [hba]
                 _ = (1 + 1 / δ) * b := by ring) hq
      _ = (1 + 1 / δ) ^ q * b ^ q := Real.mul_rpow (by positivity) hb
      _ ≤ _ := le_add_of_nonneg_left (mul_nonneg (by positivity) (Real.rpow_nonneg ha _))

/-- The competitor coefficient may be bounded using the fixed critical order. -/
theorem residue_add_rpow_le_fixed (a b q β δ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hq : 0 ≤ q) (hqβ : q ≤ β) (hδ : 0 < δ) :
    (a + b) ^ q ≤ (1 + δ) ^ β * a ^ q + (1 + 1 / δ) ^ β * b ^ q := by
  apply (residue_add_rpow_le a b q δ ha hb hq hδ).trans
  apply add_le_add
  · exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by linarith only [hδ]) hqβ)
      (Real.rpow_nonneg ha _)
  · exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (by have := one_div_pos.mpr hδ; linarith only [this]) hqβ)
      (Real.rpow_nonneg hb _)

end DOZZ.Proofs

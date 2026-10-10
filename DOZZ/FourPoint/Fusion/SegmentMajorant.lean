/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.ConvexMass
/-! # Absolute majorants controlled by one inverse mass -/
@[expose] public section
open Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs
/-- A common endpoint majorant is also a majorant for every positive segment. -/
theorem fusion_convex_mass_majorant (J a b C : ℝ≥0∞) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (ha : J ≤ C * a) (hb : J ≤ C * b) :
    J ≤ C * (ENNReal.ofReal t * a + ENNReal.ofReal (1 - t) * b) := by
  have hsum : ENNReal.ofReal t + ENNReal.ofReal (1 - t) = 1 := by
    rw [← ENNReal.ofReal_add ht.1 (sub_nonneg.mpr ht.2)]; simp
  calc
    J = ENNReal.ofReal t * J + ENNReal.ofReal (1 - t) * J := by rw [← add_mul, hsum, one_mul]
    _ ≤ ENNReal.ofReal t * (C * a) + ENNReal.ofReal (1 - t) * (C * b) :=
      add_le_add (mul_le_mul' le_rfl ha) (mul_le_mul' le_rfl hb)
    _ = _ := by ring
/-- A linear numerator bounded by the full mass consumes one inverse order, including zero
and infinite extended-mass values. -/
theorem fusion_linear_inverse_mass_bound (A I C : ℝ≥0∞) (p : ℝ) (hp : 0 ≤ p)
    (hA : A ≤ C * I) : A * I ^ (-p - 1) ≤ C * I ^ (-p) := by
  by_cases hI0 : I = 0
  · have hA0 : A = 0 := le_zero_iff.mp (by simpa only [hI0, mul_zero] using hA)
    simp only [hA0, zero_mul]
    exact zero_le
  by_cases hIt : I = ⊤
  · simp only [hIt, ENNReal.top_rpow_of_neg (by linarith : -p - 1 < 0), mul_zero]
    exact zero_le
  have he : I * I ^ (-p - 1) = I ^ (-p) := by
    nth_rw 1 [← ENNReal.rpow_one I]
    rw [← ENNReal.rpow_add 1 (-p - 1) hI0 hIt]
    congr 1
    ring
  calc
    _ ≤ C * I * I ^ (-p - 1) := mul_le_mul' hA le_rfl
    _ = _ := by rw [mul_assoc, he]
end DOZZ.Proofs

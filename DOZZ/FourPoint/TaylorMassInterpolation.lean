/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.TaylorKernelMass

/-! Positive square interpolation with every extended-mass endpoint retained. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- A local mass can reduce its square to any strictly positive order at most two.
The zero and infinite full-mass cases follow the extended-power conventions. -/
theorem mass_interpolation_bound (A I : ℝ≥0∞) (p r : ℝ)
    (hp : 0 ≤ p) (hr : 0 < r) (hr2 : r ≤ 2) (hA : A ≤ I) :
    A ^ 2 * I ^ (-p - 2) ≤ A ^ r * I ^ (-p - r) := by
  by_cases hA0 : A = 0
  · simp only [hA0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), ENNReal.zero_rpow_of_pos hr,
      zero_mul]
    exact le_rfl
  by_cases hI0 : I = 0
  · exact False.elim (hA0 (le_zero_iff.mp (hI0 ▸ hA)))
  by_cases hItop : I = ⊤
  · have hneg2 : -p - 2 < 0 := by linarith only [hp]
    have hnegr : -p - r < 0 := by linarith only [hp, hr]
    simp only [hItop, ENNReal.top_rpow_of_neg hneg2, ENNReal.top_rpow_of_neg hnegr, mul_zero]
    exact le_rfl
  have hAtop : A ≠ ⊤ := ne_top_of_le_ne_top hItop hA
  have hsplit : A ^ 2 = A ^ r * A ^ (2 - r) := by
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_add r (2 - r) hA0 hAtop]
    congr 1
    ring
  have hcombine : I ^ (2 - r) * I ^ (-p - 2) = I ^ (-p - r) := by
    rw [← ENNReal.rpow_add (2 - r) (-p - 2) hI0 hItop]
    congr 1
    ring
  rw [hsplit, mul_assoc]
  calc
    A ^ r * (A ^ (2 - r) * I ^ (-p - 2)) ≤
        A ^ r * (I ^ (2 - r) * I ^ (-p - 2)) :=
      mul_le_mul' le_rfl (mul_le_mul' (ENNReal.rpow_le_rpow hA (sub_nonneg.mpr hr2)) le_rfl)
    _ = A ^ r * I ^ (-p - r) := by rw [hcombine]

/-- A numerator bounded by a deterministic multiple of the full mass leaves one inverse
moment. -/
theorem square_inverse_mass_bound (A I : ℝ≥0∞) (k p : ℝ)
    (hk : 0 ≤ k) (hp : 0 ≤ p) (hA : A ≤ ENNReal.ofReal k * I) :
    A ^ 2 * I ^ (-p - 2) ≤ ENNReal.ofReal (k ^ 2) * I ^ (-p) := by
  by_cases hI0 : I = 0
  · have hA0 : A = 0 := le_zero_iff.mp (by simpa only [hI0, mul_zero] using hA)
    simp only [hA0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    exact zero_le
  by_cases hItop : I = ⊤
  · have hneg2 : -p - 2 < 0 := by linarith only [hp]
    simp only [hItop, ENNReal.top_rpow_of_neg hneg2, mul_zero]
    exact zero_le
  have hcombine : I ^ 2 * I ^ (-p - 2) = I ^ (-p) := by
    rw [← ENNReal.rpow_two, ← ENNReal.rpow_add 2 (-p - 2) hI0 hItop]
    congr 1
    ring
  calc
    A ^ 2 * I ^ (-p - 2) ≤ (ENNReal.ofReal k * I) ^ 2 * I ^ (-p - 2) :=
      mul_le_mul' (pow_le_pow_left' hA 2) le_rfl
    _ = ENNReal.ofReal (k ^ 2) * I ^ (-p) := by
      rw [mul_pow, mul_assoc, hcombine, ← ENNReal.ofReal_pow hk]

end DOZZ.Proofs

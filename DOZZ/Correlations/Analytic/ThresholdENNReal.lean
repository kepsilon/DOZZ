/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.ThresholdExponential

/-! The exponential threshold arithmetic in the ENNReal moment estimates. -/

@[expose] public section
open scoped ENNReal
namespace DOZZ.Proofs

/-- The ENNReal threshold bound converts to the same exponential estimate as the real one.
The constants may vanish. -/
theorem threshold_ennreal_bound (D B C rate τ m h r : ℝ)
    (hD : 0 ≤ D) (hB : 0 ≤ B) (hC : 0 ≤ C) (hh : 0 ≤ h) (hr : 0 ≤ r) :
    ENNReal.ofReal (Real.exp (-τ * r)) * ENNReal.ofReal D +
      ENNReal.ofReal B *
        ((ENNReal.ofReal (Real.exp (-rate * r)) * ENNReal.ofReal C) /
          (ENNReal.ofReal (Real.exp (-τ * r))) ^ m) ^ h ≤
      ENNReal.ofReal ((D + B * C ^ h) * Real.exp (-(min τ ((rate - τ * m) * h)) * r)) := by
  rw [← ENNReal.ofReal_mul (Real.exp_nonneg _),
    ← ENNReal.ofReal_mul (Real.exp_nonneg _),
    ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),
    ← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos (Real.exp_pos _) _),
    ENNReal.ofReal_rpow_of_nonneg
      (div_nonneg (mul_nonneg (Real.exp_nonneg _) hC) (Real.rpow_nonneg (Real.exp_nonneg _) _)) hh,
    ← ENNReal.ofReal_mul hB,
    ← ENNReal.ofReal_add (mul_nonneg (Real.exp_nonneg _) hD)
      (mul_nonneg hB (Real.rpow_nonneg
        (div_nonneg (mul_nonneg (Real.exp_nonneg _) hC) (Real.rpow_nonneg (Real.exp_nonneg _) _)) _))]
  apply ENNReal.ofReal_le_ofReal
  simpa only [mul_comm] using threshold_exponential_bound D B C rate τ m h r hD hB hC hr

end DOZZ.Proofs

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! The local monodromy invariance step in the real-solution classification. -/

@[expose] public section

namespace DOZZ.Proofs

/-- A nonintegral real exponent has nontrivial monodromy around a puncture. -/
theorem realMonodromyPhase_ne_one_of_not_int (t : ℝ)
    (ht : ∀ n : ℤ, t ≠ (n : ℝ)) :
    Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)) ≠ 1 := by
  intro hphase
  rw [Complex.exp_eq_one_iff] at hphase
  obtain ⟨n, hn⟩ := hphase
  have hbase : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  have harg :
      (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ) =
        (2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) := by
    calc
      (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ) =
          (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := hn
      _ = (2 * (Real.pi : ℂ) * Complex.I) * (n : ℂ) := by ring
  have htn : (t : ℂ) = (n : ℂ) := mul_left_cancel₀ hbase harg
  exact ht n (by exact_mod_cast htn)

/-- The local power `z^(1-c)` has nontrivial monodromy whenever `c` is nonintegral. -/
theorem gaussZeroMonodromyPhase_ne_one
    (c : ℝ) (hc : ∀ n : ℤ, c ≠ (n : ℝ)) :
    Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) * ((1 - c : ℝ) : ℂ)) ≠ 1 := by
  apply realMonodromyPhase_ne_one_of_not_int
  intro n hn
  apply hc (1 - n)
  push_cast
  linarith


end DOZZ.Proofs

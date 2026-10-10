/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.SeparatedTail.MixedMoment
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! The extended-real Markov step for the literal joint-tail event of
`DOZZ.separatedSingularMass_joint_tail`. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal

namespace DOZZ.Proofs

/-- A mixed moment bound controls the joint upper tail, even for masses which can be infinite.
This keeps the event of `DOZZ.separatedSingularMass_joint_tail` in extended values rather than
replacing it by a real-part event. -/
theorem separatedTail_joint_tail_le_of_mixed_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (W2 W3 : Ω → ℝ≥0∞) (hW2 : AEMeasurable W2 P) (hW3 : AEMeasurable W3 P)
    (a2 a3 : ℝ) (ha2 : 0 ≤ a2) (ha3 : 0 ≤ a3)
    (B : ℝ≥0∞) (hB : B ≠ ⊤)
    (hbound : (∫⁻ ω, W2 ω ^ a2 * W3 ω ^ a3 ∂P) ≤ B)
    (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    (P {ω | ENNReal.ofReal u < W2 ω ∧ ENNReal.ofReal v < W3 ω}).toReal ≤
      B.toReal * u ^ (-a2) * v ^ (-a3) := by
  let T : ℝ≥0∞ := ENNReal.ofReal u ^ a2 * ENNReal.ofReal v ^ a3
  have hsub : {ω | ENNReal.ofReal u < W2 ω ∧ ENNReal.ofReal v < W3 ω} ⊆
      {ω | T ≤ W2 ω ^ a2 * W3 ω ^ a3} := fun ω hω =>
    mul_le_mul' (ENNReal.rpow_le_rpow hω.1.le ha2) (ENNReal.rpow_le_rpow hω.2.le ha3)
  have hmarkov := mul_meas_ge_le_lintegral₀ ((hW2.pow_const a2).mul (hW3.pow_const a3)) T
  have hle : T * P {ω | ENNReal.ofReal u < W2 ω ∧ ENNReal.ofReal v < W3 ω} ≤ B :=
    (mul_le_mul_right (measure_mono hsub) T).trans (hmarkov.trans hbound)
  have hreal := ENNReal.toReal_mono hB hle
  rw [ENNReal.toReal_mul] at hreal
  have hTr : T.toReal = u ^ a2 * v ^ a3 := by
    simp only [T, ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hu.le,
      ENNReal.toReal_ofReal hv.le]
  rw [hTr] at hreal
  have hpos : 0 < u ^ a2 * v ^ a3 := mul_pos (Real.rpow_pos_of_pos hu _) (Real.rpow_pos_of_pos hv _)
  have hr : (P {ω | ENNReal.ofReal u < W2 ω ∧ ENNReal.ofReal v < W3 ω}).toReal ≤
      B.toReal / (u ^ a2 * v ^ a3) := (le_div_iff₀ hpos).mpr (by
    simpa only [mul_comm] using hreal)
  convert hr using 1
  rw [Real.rpow_neg hu.le, Real.rpow_neg hv.le]
  ring

end DOZZ.Proofs

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! A finite first moment controls all subunit positive moments on a probability space. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace DOZZ.Proofs

/-- For an exponent in `[0,1]`, an extended nonnegative number's power is bounded by one plus
the number. The argument covers both zero and infinity. -/
theorem ennreal_rpow_le_one_add_of_mem_unitInterval
    (x : ℝ≥0∞) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    x ^ p ≤ 1 + x := by
  by_cases hx : x ≤ 1
  · exact (ENNReal.rpow_le_one hx hp0).trans (by simp)
  · have hx1 : 1 ≤ x := le_of_not_ge hx
    calc
      x ^ p ≤ x ^ (1 : ℝ) := ENNReal.rpow_le_rpow_of_exponent_le hx1 hp1
      _ = x := ENNReal.rpow_one x
      _ ≤ 1 + x := le_add_of_nonneg_left (by norm_num)

/-- On a probability space, finite first moment implies finite `p`th extended moment for every
`p ∈ [0,1]`, with the explicit bound `1 + E[f]`. -/
theorem lintegral_rpow_le_one_add_of_probability
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ≥0∞) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∫⁻ ω, (f ω) ^ p ∂P ≤ 1 + ∫⁻ ω, f ω ∂P := by
  calc
    ∫⁻ ω, (f ω) ^ p ∂P ≤ ∫⁻ ω, (1 + f ω) ∂P :=
      lintegral_mono fun ω => ennreal_rpow_le_one_add_of_mem_unitInterval (f ω) hp0 hp1
    _ = 1 + ∫⁻ ω, f ω ∂P := by
      rw [lintegral_add_left' aemeasurable_const, lintegral_one]
      simp

end DOZZ.Proofs

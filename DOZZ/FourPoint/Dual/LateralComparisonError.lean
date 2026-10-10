/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Dual.SeparatedRegions
import Mathlib.Tactic
/-! Quantitative real error from the two conditional lateral comparisons. -/
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace DOZZ.Proofs

/-- Two multiplicative comparisons, with one bounded expectation, give a signed real error
linear in their small Gaussian correction exponent. Both expectations are proved finite. -/
theorem dual_lateral_comparison_real_bound (a b : ℝ≥0∞) (t C : ℝ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hC : 0 ≤ C) (ha : a ≤ ENNReal.ofReal C)
    (hab : a ≤ ENNReal.ofReal (Real.exp t)*b)
    (hba : b ≤ ENNReal.ofReal (Real.exp t)*a) :
    |a.toReal-b.toReal| ≤ (2*Real.exp 1*C)*t := by
  have haFin : a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top ha
  have hbFin : b ≠ ⊤ := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top haFin) hba
  have hxy : a.toReal ≤ Real.exp t*b.toReal := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos t).le] using
      ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbFin) hab
  have hyx : b.toReal ≤ Real.exp t*a.toReal := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos t).le] using
      ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top haFin) hba
  have hxC : a.toReal ≤ C := by
    simpa only [ENNReal.toReal_ofReal hC] using ENNReal.toReal_mono ENNReal.ofReal_ne_top ha
  have hm1 : 1 ≤ Real.exp t := Real.one_le_exp_iff.mpr ht
  have hm : Real.exp t ≤ Real.exp 1 := Real.exp_le_exp.mpr ht1
  have hd : Real.exp t-1 ≤ 2*t := by
    have hb := Real.abs_exp_sub_one_le (x := t) (by simpa only [abs_of_nonneg ht] using ht1)
    simpa only [abs_of_nonneg (sub_nonneg.mpr hm1), abs_of_nonneg ht] using hb
  have hd0 : 0 ≤ Real.exp t-1 := sub_nonneg.mpr hm1
  have hyC : b.toReal ≤ Real.exp t*C := hyx.trans (mul_le_mul_of_nonneg_left hxC (Real.exp_pos t).le)
  have hxMC : a.toReal ≤ Real.exp t*C := hxC.trans (le_mul_of_one_le_left hC hm1)
  have hleft : a.toReal-b.toReal ≤ (Real.exp t-1)*(Real.exp t*C) := by
    calc
      a.toReal-b.toReal ≤ (Real.exp t-1)*b.toReal := by linarith only [hxy]
      _ ≤ _ := mul_le_mul_of_nonneg_left hyC hd0
  have hright : b.toReal-a.toReal ≤ (Real.exp t-1)*(Real.exp t*C) := by
    calc
      b.toReal-a.toReal ≤ (Real.exp t-1)*a.toReal := by linarith only [hyx]
      _ ≤ _ := mul_le_mul_of_nonneg_left hxMC hd0
  have hbd : (Real.exp t-1)*(Real.exp t*C) ≤ (2*Real.exp 1*C)*t := by
    calc
      _ ≤ (2*t)*(Real.exp 1*C) :=
        mul_le_mul hd (mul_le_mul_of_nonneg_right hm hC) (by positivity) (by positivity)
      _ = _ := by ring
  exact abs_le.mpr ⟨by linarith only [hright.trans hbd], hleft.trans hbd⟩

end DOZZ.Proofs

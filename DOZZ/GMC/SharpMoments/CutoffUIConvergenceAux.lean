/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! # Elementary tools for convergence in probability of split quantities

Markov's inequality for a positive power, a triangle inequality for real parts of quantities that
split into a bad and a good part, and the three-way split of the event that such a difference is
large. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Markov's inequality for a positive power. -/
theorem meas_ge_le_lintegral_rpow_div {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f : Ω → ℝ≥0∞} (hf : AEMeasurable f P) {a : ℝ≥0∞} (ha : a ≠ 0) (ha' : a ≠ ⊤) {t : ℝ}
    (ht : 0 < t) :
    P {ω | a ≤ f ω} ≤ (∫⁻ ω, f ω ^ t ∂P) / a ^ t := by
  have hat0 : a ^ t ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.mpr ha) ha').ne'
  have hat : a ^ t ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ht.le ha'
  refine le_trans (measure_mono fun ω hω => ?_) (meas_ge_le_lintegral_div (hf.pow_const t) hat0
    hat)
  exact ENNReal.rpow_le_rpow hω ht.le

/-- Real parts of two quantities split into bad and good parts. -/
theorem toReal_abs_sub_le_of_split {a b c a' b' c' : ℝ≥0∞} (ha : a = b + c) (ha' : a' = b' + c')
    (hb : b ≠ ⊤) (hc : c ≠ ⊤) (hb' : b' ≠ ⊤) (hc' : c' ≠ ⊤) :
    |a.toReal - a'.toReal| ≤ b.toReal + b'.toReal + |c.toReal - c'.toReal| := by
  subst ha ha'
  rw [ENNReal.toReal_add hb hc, ENNReal.toReal_add hb' hc']
  have h1 := ENNReal.toReal_nonneg (a := b)
  have h2 := ENNReal.toReal_nonneg (a := b')
  rw [abs_le]
  constructor
  · have := neg_abs_le (c.toReal - c'.toReal)
    linarith
  · have := le_abs_self (c.toReal - c'.toReal)
    linarith

/-- If a real number is at least `e`, one of three nonnegative summands bounding it is at least
`e / 3`. -/
theorem le_of_three_le_sum {e x y z w : ℝ} (hxw : e ≤ w) (hw : w ≤ x + y + z) :
    e / 3 ≤ x ∨ e / 3 ≤ y ∨ e / 3 ≤ z := by
  by_contra h
  push Not at h
  linarith [h.1, h.2.1, h.2.2]

/-- The probability that two split quantities differ by at least `ε` is controlled by the
moments of the bad parts and the `L¹` distance of the good parts. -/
theorem prob_edist_le_of_split {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Zr Z badr badl goodr goodl : Ω → ℝ≥0∞)
    (hZr : ∀ᵐ ω ∂P, Zr ω = badr ω + goodr ω) (hZ : ∀ᵐ ω ∂P, Z ω = badl ω + goodl ω)
    (hbr : ∀ᵐ ω ∂P, badr ω ≠ ⊤) (hbl : ∀ᵐ ω ∂P, badl ω ≠ ⊤) (hgr : ∀ᵐ ω ∂P, goodr ω ≠ ⊤)
    (hgl : ∀ᵐ ω ∂P, goodl ω ≠ ⊤) (hbrm : AEMeasurable badr P) (hblm : AEMeasurable badl P)
    (hgm : AEMeasurable (fun ω => ENNReal.ofReal |(goodr ω).toReal - (goodl ω).toReal|) P)
    {e : ℝ} (he : 0 < e) {ε : ℝ≥0∞} (hεe : ENNReal.ofReal e ≤ ε) {t : ℝ} (ht : 0 < t) :
    P {ω | ε ≤ edist (Zr ω).toReal (Z ω).toReal} ≤
      (∫⁻ ω, badr ω ^ t ∂P) / ENNReal.ofReal (e / 3) ^ t +
        (∫⁻ ω, badl ω ^ t ∂P) / ENNReal.ofReal (e / 3) ^ t +
          (∫⁻ ω, ENNReal.ofReal |(goodr ω).toReal - (goodl ω).toReal| ∂P) /
            ENNReal.ofReal (e / 3) := by
  set a : ℝ≥0∞ := ENNReal.ofReal (e / 3) with ha
  have ha0 : a ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hat : a ≠ ⊤ := ENNReal.ofReal_ne_top
  set B1 : Set Ω := {ω | a ≤ badr ω} with hB1
  set B2 : Set Ω := {ω | a ≤ badl ω} with hB2
  set B3 : Set Ω := {ω | a ≤ ENNReal.ofReal |(goodr ω).toReal - (goodl ω).toReal|} with hB3
  have hle : {ω | ε ≤ edist (Zr ω).toReal (Z ω).toReal} ≤ᵐ[P] (B1 ∪ B2 ∪ B3 : Set Ω) := by
    filter_upwards [hZr, hZ, hbr, hbl, hgr, hgl] with ω h1 h2 h3 h4 h5 h6 hA
    have hA' : ε ≤ ENNReal.ofReal |(Zr ω).toReal - (Z ω).toReal| := by
      rw [edist_dist, Real.dist_eq] at hA
      exact hA
    have he' : e ≤ |(Zr ω).toReal - (Z ω).toReal| :=
      (ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)).mp (hεe.trans hA')
    have hsplit := toReal_abs_sub_le_of_split h1 h2 h3 h5 h4 h6
    rcases le_of_three_le_sum he' hsplit with hx | hx | hx
    · left; left
      show a ≤ badr ω
      rw [ha, ← ENNReal.ofReal_toReal h3]
      exact ENNReal.ofReal_le_ofReal hx
    · left; right
      show a ≤ badl ω
      rw [ha, ← ENNReal.ofReal_toReal h4]
      exact ENNReal.ofReal_le_ofReal hx
    · right
      exact ENNReal.ofReal_le_ofReal hx
  calc P {ω | ε ≤ edist (Zr ω).toReal (Z ω).toReal} ≤ P (B1 ∪ B2 ∪ B3) := measure_mono_ae hle
    _ ≤ P B1 + P B2 + P B3 := (measure_union_le _ _).trans
        (add_le_add_left (measure_union_le _ _) _)
    _ ≤ _ := by
        gcongr
        · exact meas_ge_le_lintegral_rpow_div hbrm ha0 hat ht
        · exact meas_ge_le_lintegral_rpow_div hblm ha0 hat ht
        · exact meas_ge_le_lintegral_div hgm ha0 hat

end DOZZ.Proofs

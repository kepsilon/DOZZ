/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.CutoffUIConvergenceAux

/-! # Probability estimates for the mass decomposition -/

@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The mass difference is small unless a local error or the exterior difference is large.
This estimate requires no first moment of the exterior part. -/
theorem fusion_probability_split_bound {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Zr Z badr badl goodr goodl : Ω → ℝ≥0∞)
    (hZr : ∀ᵐ ω ∂P, Zr ω = badr ω + goodr ω) (hZ : ∀ᵐ ω ∂P, Z ω = badl ω + goodl ω)
    (hbr : ∀ᵐ ω ∂P, badr ω ≠ ⊤) (hbl : ∀ᵐ ω ∂P, badl ω ≠ ⊤) (hgr : ∀ᵐ ω ∂P, goodr ω ≠ ⊤)
    (hgl : ∀ᵐ ω ∂P, goodl ω ≠ ⊤)
    {e : ℝ} (he : 0 < e) {ε : ℝ≥0∞} (hεe : ENNReal.ofReal e ≤ ε) :
    P {ω | ε ≤ edist (Zr ω).toReal (Z ω).toReal} ≤
      P {ω | ENNReal.ofReal (e / 3) ≤ badr ω} +
      P {ω | ENNReal.ofReal (e / 3) ≤ badl ω} +
      P {ω | ENNReal.ofReal (e / 3) ≤ ENNReal.ofReal |(goodr ω).toReal - (goodl ω).toReal|} := by
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

end DOZZ.Proofs

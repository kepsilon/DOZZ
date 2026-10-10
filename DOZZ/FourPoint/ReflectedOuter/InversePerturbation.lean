/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.ReflectedOuter.InverseDifference
import Mathlib.Tactic

/-! # Relative inverse-power comparison for positive finite ENNReal masses -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The quarter-mass bound and relative mass perturbation pass to two additive inverse-power
bounds. This lemma is applied only where the supplied masses are finite and positive. -/
theorem reflected_ennreal_inverse_relative_comparison (p d : ℝ) (hp : 0 < p) (hd : 0 ≤ d)
    (S T : ℝ≥0∞) (hS : S ≠ 0) (hSt : S ≠ ⊤)
    (hl : ENNReal.ofReal (1 / 4 : ℝ) * S ≤ T)
    (hu : T ≤ S + ENNReal.ofReal d * S) (hv : S ≤ T + ENNReal.ofReal d * S) :
    T ^ (-p) ≤ S ^ (-p) +
      ENNReal.ofReal (p * (1 / 4 : ℝ) ^ (-(p + 1)) * d) * S ^ (-p) ∧
    S ^ (-p) ≤ T ^ (-p) +
      ENNReal.ofReal (p * (1 / 4 : ℝ) ^ (-(p + 1)) * d) * S ^ (-p) := by
  let L : ℝ := p * (1 / 4 : ℝ) ^ (-(p + 1)) * d
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hT : T ≠ 0 := ne_zero_of_lt ((ENNReal.mul_pos
    (ENNReal.ofReal_pos.mpr (by norm_num : (0 : ℝ) < 1 / 4)).ne' hS).trans_le hl)
  have hTt : T ≠ ⊤ := ne_top_of_le_ne_top
    (ENNReal.add_ne_top.mpr ⟨hSt, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSt⟩) hu
  have hs : 0 < S.toReal := ENNReal.toReal_pos hS hSt
  have hlow : S.toReal / 4 ≤ T.toReal := by
    have hh := ENNReal.toReal_mono hTt hl
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 4)] at hh
    linarith only [hh]
  have herr : |T.toReal - S.toReal| ≤ d * S.toReal := by
    have ht := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
      ⟨hSt, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSt⟩) hu
    have hs' := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
      ⟨hTt, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSt⟩) hv
    rw [ENNReal.toReal_add hSt (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSt),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hd] at ht
    rw [ENNReal.toReal_add hTt (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSt),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal hd] at hs'
    exact abs_le.mpr ⟨by linarith only [hs'], by linarith only [ht]⟩
  have hh := reflected_real_inverse_relative_bound p d S.toReal T.toReal hp hs hlow herr
  have hSp := ENNReal.rpow_ne_top_of_ne_zero hS hSt (y := -p)
  have hTp := ENNReal.rpow_ne_top_of_ne_zero hT hTt (y := -p)
  have hRp : ENNReal.ofReal L * S ^ (-p) ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSp
  refine ⟨?_, ?_⟩
  · apply (ENNReal.toReal_le_toReal hTp (ENNReal.add_ne_top.mpr ⟨hSp, hRp⟩)).mp
    rw [ENNReal.toReal_add hSp hRp, ENNReal.toReal_mul, ENNReal.toReal_ofReal hL,
      ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow]
    have h := (le_abs_self (T.toReal ^ (-p) - S.toReal ^ (-p))).trans hh
    linarith only [h]
  · apply (ENNReal.toReal_le_toReal hSp (ENNReal.add_ne_top.mpr ⟨hTp, hRp⟩)).mp
    rw [ENNReal.toReal_add hTp hRp, ENNReal.toReal_mul, ENNReal.toReal_ofReal hL,
      ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow]
    have h := (neg_le_abs (T.toReal ^ (-p) - S.toReal ^ (-p))).trans hh
    linarith only [h]

end DOZZ.Proofs

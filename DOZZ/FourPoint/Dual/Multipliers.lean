/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.DualCrossingL
public import DOZZ.FourPoint.Dual.Parameters
public import DOZZ.ShiftEquations.Rbar.Multiplier
import Mathlib.Tactic

/-! # Nonvanishing of the literal dual crossing multipliers

The full seed domain contains no poles or zero factors in the totalized Gamma ratios.
Existing real Gamma ratio lemmas are reused.
-/

public section

namespace DOZZ.Proofs

/-- The real Gamma ratio is nonzero between one and two as well. -/
theorem dual_lR_ne_zero_of_mem_one_two {r : ℝ} (h1 : 1 < r) (h2 : r < 2) :
    lR r ≠ 0 := by
  refine div_ne_zero (Real.Gamma_pos_of_pos (by linarith only [h1])).ne' ?_
  apply Real.Gamma_ne_zero
  exact real_ne_neg_nat_of_frac (k := -1) (by push_cast; linarith only [h2])
    (by push_cast; linarith only [h1])


end DOZZ.Proofs

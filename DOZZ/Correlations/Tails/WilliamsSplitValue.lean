/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.WilliamsAuxiliaryLaw
public import DOZZ.Brownian.Reflection.MassBlocks

/-! Pointwise reconstruction of the drifted Brownian path from its marked maximum split. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The forward conditioned candidate and reversed stopped prefix, in the half ordering of
`DOZZ.twoSidedConditionedValue`. -/
noncomputable def williamsSplitPaths (ν : ℝ) (p : BrownianPath) :
    BrownianPath × BrownianPath :=
  ((williamsReversedMark ν p).2, (williamsReversedMark ν p).1.2.2)

/-- At every original nonnegative time, the maximum-centered two-sided path reconstructs
the original drifted path minus its marked height. This is a deterministic identity. -/
theorem williams_split_value (ν : ℝ) (p : BrownianPath) (t : ℝ≥0) :
    twoSidedConditionedValue (fun _ : Unit => williamsSplitPaths ν p) ()
      ((t : ℝ) - (driftedBrownianMaximumTime ν p : ℝ)) =
        p t - ν * (t : ℝ) - driftedBrownianMaximum ν p := by
  let σ := driftedBrownianMaximumTime ν p
  by_cases hst : σ ≤ t
  · have hs : 0 ≤ (t : ℝ) - (σ : ℝ) := sub_nonneg.mpr (by exact_mod_cast hst)
    have he : σ + (NNReal.mk ((t : ℝ) - (σ : ℝ)) hs) = t := by
      apply NNReal.eq
      simp only [NNReal.coe_add, NNReal.coe_mk]
      ring
    change twoSidedConditionedValue (fun _ : Unit => williamsSplitPaths ν p) ()
      ((t : ℝ) - (σ : ℝ)) = _
    rw [twoSidedConditionedValue, dite_eq_left hs]
    change p (σ + (NNReal.mk ((t : ℝ) - (σ : ℝ)) hs)) -
      ν * ((σ + (NNReal.mk ((t : ℝ) - (σ : ℝ)) hs) : ℝ≥0) : ℝ) -
        driftedBrownianMaximum ν p = _
    rw [he]
  · have hts : t < σ := lt_of_not_ge hst
    have hs : ¬ 0 ≤ (t : ℝ) - (σ : ℝ) := not_le.mpr
      (sub_neg.mpr (by exact_mod_cast hts))
    have hnn : 0 ≤ -((t : ℝ) - (σ : ℝ)) := by
      exact neg_nonneg.mpr (le_of_lt (sub_neg.mpr (by exact_mod_cast hts)))
    have he : (NNReal.mk (-((t : ℝ) - (σ : ℝ))) hnn) = σ - t := by
      apply NNReal.eq
      rw [NNReal.coe_sub hts.le]
      simp only [NNReal.coe_mk]
      ring
    change twoSidedConditionedValue (fun _ : Unit => williamsSplitPaths ν p) ()
      ((t : ℝ) - (σ : ℝ)) = _
    rw [twoSidedConditionedValue, dite_eq_right hs]
    change (stopBrownianPath (⟨fun u => p u - ν * (u : ℝ), by fun_prop⟩ : BrownianPath) σ)
      (σ - min (NNReal.mk (-((t : ℝ) - (σ : ℝ))) hnn) σ) -
        driftedBrownianMaximum ν p = _
    rw [he, min_eq_left tsub_le_self, tsub_tsub_cancel_of_le hts.le]
    change p (min t σ) - ν * ((min t σ : ℝ≥0) : ℝ) - driftedBrownianMaximum ν p = _
    rw [min_eq_left hts.le]


end DOZZ.Proofs

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.ConditionedPositiveEntranceDensity

/-!
# Deterministic last-exit kernel cancellation

This is the kernel algebra in the post-last-exit part of `thm:reversal`. Conditioning the
positive Doob process to avoid `c` changes its killed kernel to the same Doob kernel shifted by
`c`. The probabilistic conditioning itself is at a deterministic time.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace DOZZ.Proofs

/-- Drifted Brownian transition density killed at the lower boundary `c`. -/
noncomputable def brownianKilledAboveDensity (ν t c x y : ℝ) : ℝ :=
  if 0 ≤ ν ∧ 0 < t ∧ c < x ∧ c < y then
    Real.exp (ν * (y - x) - ν ^ 2 * t / 2) *
      (brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x - 2 * c))
  else 0

/-- The killed kernel after applying the original positive Doob transform. -/
noncomputable def conditionedKilledAboveDensity (ν t c x y : ℝ) : ℝ :=
  brownianKilledAboveDensity ν t c x y * conditionedH ν y / conditionedH ν x

/-- The avoidance probability, conditional on the current positive state. -/
noncomputable def lastExitAvoidanceFactor (ν c y : ℝ) : ℝ :=
  if c < y then conditionedH ν (y - c) / conditionedH ν y else 0

/-- The conditioned killed kernel, corrected by the probability of avoiding `c` in the future,
is the entrance-process transition kernel translated down by `c`. -/
theorem conditionedKilledAboveDensity_avoidance_shift
    (ν t c x y : ℝ) (hν : 0 < ν) (ht : 0 < t)
    (hcx : c < x) (hcy : c < y)
    (hx : conditionedH ν x ≠ 0) (hy : conditionedH ν y ≠ 0)
    (hxc : conditionedH ν (x - c) ≠ 0) (hyc : conditionedH ν (y - c) ≠ 0) :
    conditionedKilledAboveDensity ν t c x y *
        (lastExitAvoidanceFactor ν c y / lastExitAvoidanceFactor ν c x) =
      conditionedPositiveTransitionDensity ν t (x - c) (y - c) := by
  have hxc_pos : 0 < x - c := sub_pos.mpr hcx
  have hyc_pos : 0 < y - c := sub_pos.mpr hcy
  simp [conditionedKilledAboveDensity, brownianKilledAboveDensity,
    lastExitAvoidanceFactor, conditionedPositiveTransitionDensity,
    brownianHeatDensity, hν.le, ht, hcx, hcy, hxc_pos, hyc_pos]
  field_simp [hx, hy, hxc, hyc]
  ring_nf

end DOZZ.Proofs

end

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.BrownianMaximumReferenceLaw
public import Mathlib.Probability.Distributions.Exponential

/-!
# Normalization of the Williams maximum law

The reference measure in the Williams disintegration is the rate-`2ν` exponential law. This
module identifies its density with Mathlib's exponential distribution and records its probability
normalization.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DOZZ.Proofs

/-- The Brownian maximum reference density is Mathlib's exponential density at rate `2ν`. -/
theorem brownianMaximumReferenceLaw_eq_expMeasure (ν : ℝ) :
    brownianMaximumReferenceLaw ν = ProbabilityTheory.expMeasure (2 * ν) := by
  unfold brownianMaximumReferenceLaw ProbabilityTheory.expMeasure ProbabilityTheory.gammaMeasure
  apply withDensity_congr_ae
  filter_upwards [MeasureTheory.volume.ae_ne (0 : ℝ)] with x hx
  by_cases hxpos : 0 < x
  · simp [ProbabilityTheory.gammaPDF_eq, hxpos.le, hxpos]
  · have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hxpos) hx
    simp [ProbabilityTheory.gammaPDF_eq, not_lt.mpr hxneg.le, not_le_of_gt hxneg]

/-- The Williams reference law is a probability measure whenever the drift is positive. -/
theorem isProbabilityMeasure_brownianMaximumReferenceLaw {ν : ℝ} (hν : 0 < ν) :
    IsProbabilityMeasure (brownianMaximumReferenceLaw ν) := by
  rw [brownianMaximumReferenceLaw_eq_expMeasure]
  exact ProbabilityTheory.isProbabilityMeasure_expMeasure (by nlinarith)

end DOZZ.Proofs

end

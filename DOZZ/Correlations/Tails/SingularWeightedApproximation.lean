/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.SingularCompactApproximation

/-! Increasing singular cutoffs with a finite spatial multiplier and translated center. -/

@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace DOZZ.Proofs

theorem singular_compact_weighted_lintegral_tendsto
    (f : BoundedContinuousFunction ℂ ℝ) (hfc : HasCompactSupport (f : ℂ → ℝ))
    (hf : ∀ x, 0 ≤ f x) (β : ℝ) (hβ : 0 ≤ β) (z : ℂ)
    (w : ℂ → ℝ≥0∞) (hw : Measurable w) (hwf : ∀ x, w x ≠ ∞) (μ : Measure ℂ) :
    Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (singularCompactTest f hfc β n (x-z)) * w x ∂μ)
      atTop (𝓝 (∫⁻ x, ENNReal.ofReal (f (x-z)) *
        (ENNReal.ofReal ‖x-z‖) ^ (-β) * w x ∂μ)) := by
  apply lintegral_tendsto_of_tendsto_of_monotone
    (fun n => ((ENNReal.measurable_ofReal.comp
      ((singularCompactTest f hfc β n).continuous.measurable.comp
        (measurable_id.sub_const z))).mul hw).aemeasurable)
    (ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
  · intro n m hnm
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal
      (singular_compact_test_mono f hfc hf β hβ (x-z) hnm)) le_rfl
  · exact ENNReal.Tendsto.mul_const
      (singular_compact_test_tendsto f hfc hf β (x-z)) (Or.inr (hwf x))


end DOZZ.Proofs

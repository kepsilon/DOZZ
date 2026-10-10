/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.OffCenterRegression

/-! The literal Gaussian pin law used by copied-multiplier moment bounds. -/

@[expose] public section
open MeasureTheory ProbabilityTheory

namespace DOZZ.Proofs

theorem offCenter_pin_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (z : ℂ) (hz : 2 ≤ ‖z‖) :
    HasLaw (fun ω => Xc ω z 0) (gaussianReal 0 (2*Real.log ‖z‖).toNNReal) P := by
  obtain ⟨hG,hm⟩ := circleAverage_isGaussianProcess P X Xc hX hc
  have hg := hG.hasGaussianLaw_eval (z,(0 : ℝ))
  refine ⟨hg.aemeasurable,?_⟩
  rw [hg.map_eq_gaussianReal, hm, ← covariance_self hg.aemeasurable,
    offCenter_origin_variance X Xc hX hc z hz]


end DOZZ.Proofs

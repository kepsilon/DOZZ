/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.UnitVolumeStructureConstant
import DOZZ.Upsilon.Continuation
import DOZZ.GFF.Assembly
import DOZZ.GMC.Assembly.CircleGMCExists

/-!
# Existence of Upsilon and an equator GFF with its GMC

Assemble the entire Upsilon construction and the circle GMC of the concrete scale-space
white-noise equator field. The sample space is in `Type`, as required by `DOZZ.dozz_existence`.
-/

public section

open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Set
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- Upsilon and a probability space carrying an equator GFF with its circle GMC exist for every
`0 < γ < 2`: proof of `DOZZ.dozz_existence`. -/
theorem dozz_existence (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) :
    (∃ U : ℂ → ℂ, IsUpsilon γ U) ∧
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : Ω → Distr) (M : Ω → Measure ℂ),
        IsEquatorGFF P X ∧ IsGMCOf P X γ M := by
  refine ⟨exists_IsUpsilon hγ hγ2, ?_⟩
  obtain ⟨_, M, _, hM⟩ := equatorGFF_circle_average_GMC_exists
    (GaussianFields.scaleSpaceWhiteNoiseMeasure 2) equatorGFFDistribution
    isEquatorGFF_equatorGFFDistribution γ hγ hγ2
  exact ⟨GaussianFields.ScaleSpaceWhiteNoiseSpace 2, inferInstance,
    GaussianFields.scaleSpaceWhiteNoiseMeasure 2, equatorGFFDistribution, M,
    isEquatorGFF_equatorGFFDistribution, hM⟩

end DOZZ.Proofs

end

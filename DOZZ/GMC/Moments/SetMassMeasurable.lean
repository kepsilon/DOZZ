/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.IsGMCOf
public import DOZZ.GMC.Construction.GMCMeasurableVersion

/-! Measurability of set masses for arbitrary weak-limit GMC versions. -/

@[expose] public section

open MeasureTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- Every measurable-set evaluation of an arbitrary `IsGMCOf` version is a.e. measurable.
The measurable modification is supplied by the weak-limit measurable-version theorem. -/
theorem gmc_set_mass_aemeasurable_of_isGMCOf
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (A : Set ℂ) (hA : MeasurableSet A) :
    AEMeasurable (fun ω => M ω A) P := by
  obtain ⟨N, hNmeas, _hNfinite, hMN⟩ :=
    equatorGFF_GMC_measurable_version P X hX γ hγ hγ2 M hM
  have hEval : Measurable (fun ω => N ω A) :=
    (Measure.measurable_coe hA).comp hNmeas
  apply hEval.aemeasurable.congr
  filter_upwards [hMN] with ω hω
  rw [hω]

end DOZZ.Proofs

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.AdmissibleGMCCoordinateChange
public import DOZZ.GMC.Moments.InversionAdmissible
public import DOZZ.GMC.Moments.InversionReference

/-! Admissible GMC transport in the punctured inversion chart. -/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

private theorem gmcReferenceMeasure_restrict_inversionChart_map :
    (gmcReferenceMeasure.restrict inversionChart).map (fun x : ℂ => x⁻¹) =
      gmcReferenceMeasure.restrict inversionChart := by
  classical
  have hU : MeasurableSet inversionChart := isOpen_compl_singleton.measurableSet
  have hpre : (fun x : ℂ => x⁻¹) ⁻¹' inversionChart = inversionChart := by
    ext x
    simp [inversionChart]
  let hpres : MeasurePreserving (fun x : ℂ => x⁻¹)
      gmcReferenceMeasure gmcReferenceMeasure := by
    refine ⟨by fun_prop, ?_⟩
    exact gmcReferenceMeasure_map_complexInv
  have hrestrict := hpres.restrict_preimage hU
  rw [hpre] at hrestrict
  exact hrestrict.map_eq

/-- The logarithmic reference measure on the punctured plane is invariant under inversion. -/
theorem logRegularizationReference_inversionChart_map :
    logRegularizationReference inversionChart (fun x => normPlus x ^ (-4 : ℝ)) =
      (logRegularizationReference inversionChart (fun x => normPlus x ^ (-4 : ℝ))).map
        complexInvOpenPartialHomeomorph := by
  have hRef : logRegularizationReference inversionChart
      (fun x => normPlus x ^ (-4 : ℝ)) =
        gmcReferenceMeasure.restrict inversionChart := by
    rw [logRegularizationReference_restrict_of_subset Set.univ inversionChart
      (fun x => normPlus x ^ (-4 : ℝ)) isOpen_compl_singleton.measurableSet
      (Set.subset_univ _)]
    simp [logRegularizationReference, gmcReferenceMeasure]
  rw [hRef]
  simpa [complexInvOpenPartialHomeomorph] using
    gmcReferenceMeasure_restrict_inversionChart_map.symm

/-- The finite-cutoff logarithmic chaos test mass transports exactly under inversion, with the
target test pulled back by the inverse chart map. -/
theorem regularizedLogChaosTestMass_inversion_coordinate_change
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P inversionChart
      (fun x => normPlus x ^ (-4 : ℝ)) 1 Y)
    (γ : ℝ) (f : BoundedContinuousFunction ℂ ℝ)
    (hfCompact : HasCompactSupport (f : ℂ → ℝ))
    (hfSupport : tsupport (f : ℂ → ℝ) ⊆ inversionChart) :
    ∃ g : BoundedContinuousFunction ℂ ℝ,
      HasCompactSupport (g : ℂ → ℝ) ∧
      tsupport (g : ℂ → ℝ) ⊆ inversionChart ∧
      (∀ x ∈ inversionChart, g x = f (complexInvOpenPartialHomeomorph x)) ∧
      (∀ x ∉ inversionChart, g x = 0) ∧
      ∀ r ω,
        regularizedLogChaosTestMass P inversionChart
            (fun x => normPlus x ^ (-4 : ℝ)) Y γ r ω g =
          regularizedLogChaosTestMass P inversionChart
            (fun x => normPlus x ^ (-4 : ℝ))
            (fun ω ε x => Y ω ε (complexInvOpenPartialHomeomorph x)) γ r ω f := by
  let Yinv : Ω → ℝ → ℂ → ℝ := fun ω ε x => Y ω ε (complexInvOpenPartialHomeomorph x)
  have hYinv : IsAdmissibleLogRegularization P inversionChart
      (fun x => normPlus x ^ (-4 : ℝ)) 1 Yinv := by
    simpa [Yinv, complexInvOpenPartialHomeomorph] using
      isAdmissibleLogRegularization_complexInv P
        (fun x => normPlus x ^ (-4 : ℝ)) 1 Y hY
  obtain ⟨g, hgCompact, hgSupport, hgOn, hgOff, hmass⟩ :=
    regularizedLogChaosTestMass_coordinate_change P inversionChart inversionChart
      (fun x => normPlus x ^ (-4 : ℝ)) (fun x => normPlus x ^ (-4 : ℝ)) 1 1
      Y Yinv hY hYinv complexInvOpenPartialHomeomorph rfl rfl
      logRegularizationReference_inversionChart_map
      (by
        intro ω ε y hy
        rfl)
      γ f hfCompact hfSupport
  refine ⟨g, hgCompact, hgSupport, ?_, hgOff, ?_⟩
  · intro x hx
    simpa [complexInvOpenPartialHomeomorph] using hgOn x hx
  · intro r ω
    simpa [Yinv, complexInvOpenPartialHomeomorph] using (hmass r ω).symm


end DOZZ.Proofs

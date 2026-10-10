/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.AdmissibleGMCRestriction
public import DOZZ.GMC.Construction.CircleCutoffTestMass
public import DOZZ.GMC.Construction.GMCMeasurableVersion
public import DOZZ.GMC.Construction.GMCUniqueAe

/-! Chart-supported admissible versions obtained directly from arbitrary `IsGMCOf` limits. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- Restrict an arbitrary weak-limit GMC version to an open chart and express its limit using any
circle-average witness of the field. This makes the second sphere chart available without using the
GMC construction theorem. -/
theorem isGMCOf_restrict_admissible_version
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (U : Set ℂ) (hU : IsOpen U) :
    ∃ N : Ω → Measure ℂ,
      IsAdmissibleGMCVersion P U (fun x => normPlus x ^ (-4 : ℝ))
        (fun ω ε x => Xc ω x (Real.log (1 / ε))) γ N ∧
      (∀ ω, IsFiniteMeasure (N ω)) ∧
      ∀ᵐ ω ∂P, (M ω).restrict U = N ω := by
  classical
  obtain ⟨N, hNmeas, hNfinite, hMN⟩ :=
    equatorGFF_GMC_measurable_version P X hX γ hγ hγ2 M hM
  rcases hM with ⟨_hMfinite, Xc0, hXc0, hMconv⟩
  let Y : Ω → ℝ → ℂ → ℝ := fun ω ε x => Xc ω x (Real.log (1 / ε))
  let Nc : Ω → Measure ℂ := fun ω => (N ω).restrict U
  have hNcmeas : Measurable Nc := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    have hEq : (fun ω => Nc ω s) = fun ω => N ω (s ∩ U) := by
      funext ω
      exact Measure.restrict_apply hs
    rw [hEq]
    exact (Measure.measurable_coe (hs.inter hU.measurableSet)).comp hNmeas
  have hNcsupport : ∀ ω, Nc ω Uᶜ = 0 := by
    intro ω
    rw [show Nc ω = (N ω).restrict U by rfl,
      Measure.restrict_apply (MeasurableSet.compl hU.measurableSet)]
    simp
  have hNccompact : ∀ ω K, IsCompact K → K ⊆ U → Nc ω K < ⊤ := by
    intro ω K hK hKU
    rw [show Nc ω = (N ω).restrict U by rfl,
      Measure.restrict_apply hK.measurableSet,
      Set.inter_eq_left.mpr hKU]
    exact lt_of_le_of_lt (measure_mono (Set.subset_univ K))
      (hNfinite ω).measure_univ_lt_top
  have hNcfinite : ∀ ω, IsFiniteMeasure (Nc ω) := by
    intro ω
    apply isFiniteMeasure_restrict.mpr
    exact ne_of_lt (lt_of_le_of_lt (measure_mono (Set.subset_univ U))
      (hNfinite ω).measure_univ_lt_top)
  have hcutoffs (f : BoundedContinuousFunction ℂ ℝ)
      (hfcompact : HasCompactSupport (f : ℂ → ℝ))
      (hfU : tsupport (f : ℂ → ℝ) ⊆ U) (r : ℝ) :
      (fun ω => regularizedLogChaosTestMass P U (fun x => normPlus x ^ (-4 : ℝ))
          Y γ r ω f) =ᵐ[P] fun ω => ∫ x, f x ∂regularizedGMC P Xc γ r ω := by
    have hfzero := boundedContinuousFunction_eq_zero_off_tsupport_subset f U hfU
    have hrestrict : logRegularizationReference U (fun x => normPlus x ^ (-4 : ℝ)) =
        (logRegularizationReference Set.univ (fun x => normPlus x ^ (-4 : ℝ))).restrict U :=
      logRegularizationReference_restrict_of_subset Set.univ U
        (fun x => normPlus x ^ (-4 : ℝ)) hU.measurableSet (Set.subset_univ _)
    have hMass : ∀ ω,
        regularizedLogChaosTestMass P U (fun x => normPlus x ^ (-4 : ℝ))
            Y γ r ω f =
          regularizedLogChaosTestMass P Set.univ (fun x => normPlus x ^ (-4 : ℝ))
            Y γ r ω f := by
      intro ω
      rw [regularizedLogChaosTestMass, regularizedLogChaosTestMass, hrestrict]
      exact integral_restrict_eq_integral_of_zero_on_compl
        (logRegularizationReference Set.univ (fun x => normPlus x ^ (-4 : ℝ)))
        U hU.measurableSet
        (fun x => f x * Real.exp (γ * Y ω (Real.exp (-r)) x - γ ^ 2 / 2 *
          ∫ ω', Y ω' (Real.exp (-r)) x ^ 2 ∂P))
        (fun x hx => by rw [hfzero x hx, zero_mul])
    have hFull := circleCutoff_testMass_eq_regularizedGMC P X hX Xc hXc γ r
      (f := f)
    filter_upwards [] with ω
    rw [hMass ω, hFull]
  have hconv (f : BoundedContinuousFunction ℂ ℝ)
      (hfcompact : HasCompactSupport (f : ℂ → ℝ))
      (hfU : tsupport (f : ℂ → ℝ) ⊆ U) :
      TendstoInMeasure P
        (fun r ω => regularizedLogChaosTestMass P U
          (fun x => normPlus x ^ (-4 : ℝ)) Y γ r ω f) atTop
        (fun ω => ∫ x, f x ∂Nc ω) := by
    have hMconv' : TendstoInMeasure P
        (fun r ω => ∫ x, f x ∂regularizedGMC P Xc γ r ω) atTop
        (fun ω => ∫ x, f x ∂M ω) := by
      have hseq (r : ℝ) :
          (fun ω => ∫ x, f x ∂regularizedGMC P Xc γ r ω) =ᵐ[P]
            fun ω => ∫ x, f x ∂regularizedGMC P Xc0 γ r ω := by
        filter_upwards [regularizedGMC_ae_eq_of_circleAverage P X hX Xc Xc0 hXc hXc0 γ r]
          with ω hω
        rw [hω]
      exact TendstoInMeasure.congr (fun r => (hseq r).symm)
        (Filter.Eventually.of_forall fun _ => rfl) (hMconv f)
    have hseq (r : ℝ) := (hcutoffs f hfcompact hfU r).symm
    have hfzero := boundedContinuousFunction_eq_zero_off_tsupport_subset f U hfU
    have htarget : (fun ω => ∫ x, f x ∂M ω) =ᵐ[P]
        fun ω => ∫ x, f x ∂Nc ω := by
      filter_upwards [hMN] with ω hω
      rw [show Nc ω = (N ω).restrict U by rfl]
      rw [hω]
      exact (integral_restrict_eq_integral_of_zero_on_compl (N ω) U hU.measurableSet
        (fun x => f x) hfzero).symm
    exact TendstoInMeasure.congr hseq htarget hMconv'
  refine ⟨Nc, ?_, hNcfinite, ?_⟩
  · refine ⟨hNcmeas, hNcsupport, hNccompact, ?_⟩
    intro f hfcompact hfU
    exact hconv f hfcompact hfU
  · filter_upwards [hMN] with ω hω
    rw [show Nc ω = (N ω).restrict U by rfl, hω]

/-- Proof of `DOZZ.equatorGFF_GMC_restrict_admissible` (chart restriction), obtained from the
stronger measurable finite version above. -/
theorem equatorGFF_GMC_restrict_admissible
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (U : Set ℂ) (hU : IsOpen U) :
    ∃ N : Ω → Measure ℂ,
      IsAdmissibleGMCVersion P U (fun x => normPlus x ^ (-4 : ℝ))
        (fun ω ε x => Xc ω x (Real.log (1 / ε))) γ N ∧
      ∀ᵐ ω ∂P, (M ω).restrict U = N ω := by
  obtain ⟨N, hN, _hNfinite, hMN⟩ :=
    isGMCOf_restrict_admissible_version P X hX γ hγ hγ2 M hM Xc hXc U hU
  exact ⟨N, hN, hMN⟩

end DOZZ.Proofs

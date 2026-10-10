/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.IsAdmissibleGMCVersion
public import DOZZ.Statements.GMC.LogRegularizationReference
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Restriction of admissible GMC limits to measurable subcharts. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- Integrating a function which vanishes off a measurable set is unchanged by restricting the
measure to that set. -/
theorem integral_restrict_eq_integral_of_zero_on_compl
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (V : Set α)
    (hV : MeasurableSet V) (g : α → ℝ)
    (hg : ∀ x, x ∉ V → g x = 0) :
    ∫ x, g x ∂μ.restrict V = ∫ x, g x ∂μ := by
  have h := integral_union_eq_left_of_forall (μ := μ) (s := V) (t := Vᶜ)
    hV.compl hg
  rw [← setIntegral_univ]
  simpa using h.symm

/-- The log-regularization reference measure on a subchart is the restriction of the reference
measure on the original chart. -/
theorem logRegularizationReference_restrict_of_subset
    (U V : Set ℂ) (dens : ℂ → ℝ)
    (hV : MeasurableSet V) (hVU : V ⊆ U) :
    logRegularizationReference V dens = (logRegularizationReference U dens).restrict V := by
  rw [logRegularizationReference, logRegularizationReference]
  calc
    (volume.restrict V).withDensity (fun x => ENNReal.ofReal (dens x)) =
        ((volume.restrict U).withDensity (fun x => ENNReal.ofReal (dens x))).restrict V := by
          rw [MeasureTheory.restrict_withDensity hV,
            Measure.restrict_restrict_of_subset hVU]

/-- A compactly supported continuous test whose topological support lies in `V` vanishes outside
`V`. -/
theorem boundedContinuousFunction_eq_zero_off_tsupport_subset
    (f : BoundedContinuousFunction ℂ ℝ) (V : Set ℂ)
    (hfV : tsupport (f : ℂ → ℝ) ⊆ V) :
    ∀ x, x ∉ V → f x = 0 := by
  intro x hx
  by_contra hne
  have hxSupport : x ∈ Function.support (f : ℂ → ℝ) := by
    simpa [Function.mem_support] using hne
  exact hx (hfV (subset_tsupport (f : ℂ → ℝ) hxSupport))

/-- Restricting the limiting random measure to a measurable subchart preserves the admissible GMC
version property. The reference measure and every cutoff test integral restrict in the same way. -/
theorem admissibleGMCVersion_restrict_of_subset
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (U V : Set ℂ) (dens : ℂ → ℝ)
    (Y : Ω → ℝ → ℂ → ℝ) (γ : ℝ) (M : Ω → Measure ℂ)
    (hM : IsAdmissibleGMCVersion P U dens Y γ M)
    (hV : MeasurableSet V) (hVU : V ⊆ U) :
    IsAdmissibleGMCVersion P V dens Y γ (fun ω => (M ω).restrict V) := by
  rcases hM with ⟨hMMeas, hMSupport, hMCompact, hMLimit⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Measure.measurable_of_measurable_coe
    intro s hs
    have hcoe : (fun ω => (M ω).restrict V s) = fun ω => M ω (s ∩ V) := by
      funext ω
      exact Measure.restrict_apply hs
    rw [hcoe]
    exact (Measure.measurable_coe (hs.inter hV)).comp hMMeas
  · intro ω
    rw [Measure.restrict_apply (MeasurableSet.compl hV)]
    simp
  · intro ω K hK hKV
    rw [Measure.restrict_apply hK.measurableSet,
      Set.inter_eq_left.mpr hKV]
    exact hMCompact ω K hK (hKV.trans hVU)
  · intro f hfCompact hfSupport
    have hfzero := boundedContinuousFunction_eq_zero_off_tsupport_subset f V hfSupport
    have hMass (r : ℝ) (ω : Ω) :
        regularizedLogChaosTestMass P V dens Y γ r ω f =
          regularizedLogChaosTestMass P U dens Y γ r ω f := by
      rw [regularizedLogChaosTestMass, regularizedLogChaosTestMass,
        logRegularizationReference_restrict_of_subset U V dens hV hVU]
      exact integral_restrict_eq_integral_of_zero_on_compl
        (logRegularizationReference U dens) V hV
        (fun x => f x * Real.exp (γ * Y ω (Real.exp (-r)) x - γ ^ 2 / 2 *
          ∫ ω', Y ω' (Real.exp (-r)) x ^ 2 ∂P))
        (fun x hx => by rw [hfzero x hx, zero_mul])
    have hTarget (ω : Ω) :
        (∫ x, f x ∂(M ω).restrict V) = ∫ x, f x ∂M ω :=
      integral_restrict_eq_integral_of_zero_on_compl (M ω) V hV
        (fun x => f x) (hfzero)
    have hleft : ∀ r, (fun ω => regularizedLogChaosTestMass P U dens Y γ r ω f) =ᵐ[P]
        fun ω => regularizedLogChaosTestMass P V dens Y γ r ω f := by
      intro r
      exact Eventually.of_forall fun ω => (hMass r ω).symm
    have hright : (fun ω => ∫ x, f x ∂M ω) =ᵐ[P]
        fun ω => ∫ x, f x ∂(M ω).restrict V :=
      Eventually.of_forall fun ω => (hTarget ω).symm
    have hlim := hMLimit f hfCompact (hfSupport.trans hVU)
    exact TendstoInMeasure.congr hleft hright hlim

end DOZZ.Proofs

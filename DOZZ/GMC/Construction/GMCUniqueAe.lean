/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.IsGMCOf
import DOZZ.GFFStructure.GaussianClosure
import DOZZ.GMC.AdmissibleGMCCountableTests
import DOZZ.GMC.AdmissibleGMCDetermines
import Mathlib.MeasureTheory.Measure.WithDensity

/-! Almost-sure uniqueness of the circle-average GMC version. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- Equivalent circle-average witnesses give the same regularized random measure a.e. -/
theorem regularizedGMC_ae_eq_of_circleAverage
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc Yc : Ω → ℂ → ℝ → ℝ)
    (hXc : IsCircleAverage P X Xc) (hYc : IsCircleAverage P X Yc)
    (γ r : ℝ) :
    ∀ᵐ ω ∂P, regularizedGMC P Xc γ r ω = regularizedGMC P Yc γ r ω := by
  classical
  let _ := hX.1
  have hcoord (x : ℂ) : (fun ω => Xc ω x r) =ᵐ[P] fun ω => Yc ω x r :=
    circleAverage_ae_eq X Xc Yc hX hXc hYc x r
  have hEvent : MeasurableSet {q : ℂ × Ω | Xc q.2 q.1 r = Yc q.2 q.1 r} := by
    apply measurableSet_eq_fun
    · exact (hXc.1 r).comp measurable_swap
    · exact (hYc.1 r).comp measurable_swap
  have hIter : ∀ᵐ x ∂volume, ∀ᵐ ω ∂P, Xc ω x r = Yc ω x r :=
    ae_of_all _ hcoord
  have hJoint : ∀ᵐ ω ∂P, ∀ᵐ x ∂volume, Xc ω x r = Yc ω x r :=
    (Measure.ae_ae_comm hEvent).mp hIter
  have hVariance (x : ℂ) :
      (∫ ω, Xc ω x r ^ 2 ∂P) = ∫ ω, Yc ω x r ^ 2 ∂P := by
    apply integral_congr_ae
    filter_upwards [hcoord x] with ω hω
    rw [hω]
  let dX : Ω × ℂ → ℝ≥0∞ := fun q => ENNReal.ofReal
    (Real.exp (γ * Xc q.1 q.2 r - γ ^ 2 / 2 * ∫ ω, Xc ω q.2 r ^ 2 ∂P) *
      normPlus q.2 ^ (-4 : ℝ))
  let dY : Ω × ℂ → ℝ≥0∞ := fun q => ENNReal.ofReal
    (Real.exp (γ * Yc q.1 q.2 r - γ ^ 2 / 2 * ∫ ω, Yc ω q.2 r ^ 2 ∂P) *
      normPlus q.2 ^ (-4 : ℝ))
  have hDensity : ∀ᵐ ω ∂P, (fun x => dX (ω, x)) =ᵐ[volume]
      fun x => dY (ω, x) := by
    filter_upwards [hJoint] with ω hω
    filter_upwards [hω] with x hx
    simp only [dX, dY]
    rw [hVariance x, hx]
  filter_upwards [hDensity] with ω hω
  change volume.withDensity (fun x => dX (ω, x)) =
    volume.withDensity (fun x => dY (ω, x))
  exact withDensity_congr_ae hω

/-- Two finite random measures with the circle-average GMC convergence property agree a.e. -/
theorem equatorGFF_GMC_unique_ae
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (M N : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (hN : IsGMCOf P X γ N) :
    ∀ᵐ ω ∂P, M ω = N ω := by
  classical
  let _ := hX.1
  obtain ⟨Xc, hXc, hXM⟩ := hM.2
  obtain ⟨Yc, hYc, hYN⟩ := hN.2
  obtain ⟨K, hKcompact, hKU, hKmono, hKcover, hKcofinal, f, hf, hdense⟩ :=
    exists_countable_dense_admissible_tests Set.univ isOpen_univ
  have hTest : ∀ nm : ℕ × ℕ,
      (fun ω => ∫ x, f nm x ∂M ω) =ᵐ[P] fun ω => ∫ x, f nm x ∂N ω := by
    intro nm
    have hLeft : TendstoInMeasure P
        (fun r ω => ∫ x, f nm x ∂regularizedGMC P Xc γ r ω) atTop
        (fun ω => ∫ x, f nm x ∂M ω) := hXM (f nm)
    have hCutoff : ∀ r : ℝ,
        (fun ω => ∫ x, f nm x ∂regularizedGMC P Xc γ r ω) =ᵐ[P]
          fun ω => ∫ x, f nm x ∂regularizedGMC P Yc γ r ω := by
      intro r
      filter_upwards [regularizedGMC_ae_eq_of_circleAverage P X hX Xc Yc hXc hYc γ r]
        with ω hω
      rw [hω]
    have hLeft' : TendstoInMeasure P
        (fun r ω => ∫ x, f nm x ∂regularizedGMC P Yc γ r ω) atTop
        (fun ω => ∫ x, f nm x ∂M ω) := by
      apply TendstoInMeasure.congr hCutoff (Filter.Eventually.of_forall fun _ => rfl) hLeft
    have hRight : TendstoInMeasure P
        (fun r ω => ∫ x, f nm x ∂regularizedGMC P Yc γ r ω) atTop
        (fun ω => ∫ x, f nm x ∂N ω) := hYN (f nm)
    exact tendstoInMeasure_ae_unique hLeft' hRight
  have hAll : ∀ᵐ ω ∂P, ∀ nm : ℕ × ℕ,
      ∫ x, f nm x ∂M ω = ∫ x, f nm x ∂N ω := by
    rw [ae_all_iff]
    exact hTest
  filter_upwards [hAll] with ω hω
  apply admissible_countable_tests_determine_chart_measures Set.univ isOpen_univ
    (M ω) (N ω) ?_ ?_ ?_ ?_ K hKcompact hKU hKcofinal f ?_ ?_ ?_
  · simp
  · simp
  · intro L hL hLU
    have hfinite := (hM.1 ω).measure_univ_lt_top
    exact lt_of_le_of_lt (measure_mono (Set.subset_univ L)) hfinite
  · intro L hL hLU
    have hfinite := (hN.1 ω).measure_univ_lt_top
    exact lt_of_le_of_lt (measure_mono (Set.subset_univ L)) hfinite
  · intro n m
    exact ⟨(hf n m).1, (hf n m).2.1⟩
  · exact fun n g hg hgs δ hδ => hdense n g hg hgs δ hδ
  · exact fun n m => hω (n, m)

end DOZZ.Proofs

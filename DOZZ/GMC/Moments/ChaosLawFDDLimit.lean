/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import DOZZ.GMC.Moments.ChaosLawFDD

/-! Passage from cutoff chaos laws to laws of arbitrary limits in measure. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace DOZZ.Proofs

/-- Equality in law of finite-cutoff approximants passes to limits in measure. Separate
subsequences on the two probability spaces are synchronized by taking a further subsequence of the
first one; bounded continuous tests then pass by dominated convergence. -/
theorem map_eq_of_seq_map_eq_of_tendstoInMeasure
    {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace E]
    [PseudoEMetricSpace E] [BorelSpace E]
    [SecondCountableTopology E] [HasOuterApproxClosed E]
    {P : Measure Ω} {P' : Measure Ω'} [IsFiniteMeasure P] [IsFiniteMeasure P']
    (f : ℕ → Ω → E) (g : ℕ → Ω' → E) (fLimit : Ω → E) (gLimit : Ω' → E)
    (hf : ∀ n, AEMeasurable (f n) P) (hg : ∀ n, AEMeasurable (g n) P')
    (hflimit : AEMeasurable fLimit P) (hglimit : AEMeasurable gLimit P')
    (hmap : ∀ n, Measure.map (f n) P = Measure.map (g n) P')
    (hfconv : TendstoInMeasure P f atTop fLimit)
    (hgconv : TendstoInMeasure P' g atTop gLimit) :
    Measure.map fLimit P = Measure.map gLimit P' := by
  have htest : ∀ φ : BoundedContinuousFunction E ℝ,
      (∫ ω, φ (fLimit ω) ∂P) = ∫ ω, φ (gLimit ω) ∂P' := by
    intro φ
    obtain ⟨ns, hns, hfae⟩ := hfconv.exists_seq_tendsto_ae
    have hgsub : TendstoInMeasure P' (fun n => g (ns n)) atTop gLimit :=
      hgconv.comp hns.tendsto_atTop
    obtain ⟨ms, hms, hgae⟩ := hgsub.exists_seq_tendsto_ae
    let fs : ℕ → Ω → E := fun n => f (ns (ms n))
    let gs : ℕ → Ω' → E := fun n => g (ns (ms n))
    have hfs : ∀ n, AEMeasurable (fs n) P := fun n => hf _
    have hgs : ∀ n, AEMeasurable (gs n) P' := fun n => hg _
    have hmaps : ∀ n, Measure.map (fs n) P = Measure.map (gs n) P' := by
      intro n
      exact hmap (ns (ms n))
    have hfseq : ∀ᵐ ω ∂P, Tendsto (fun n => fs n ω) atTop (𝓝 (fLimit ω)) := by
      filter_upwards [hfae] with ω hω
      have hcomp := hω.comp hms.tendsto_atTop
      change Tendsto (fun n => f (ns (ms n)) ω) atTop (𝓝 (fLimit ω)) at hcomp
      exact hcomp
    have hgseq : ∀ᵐ ω ∂P', Tendsto (fun n => gs n ω) atTop (𝓝 (gLimit ω)) := by
      filter_upwards [hgae] with ω hω
      change Tendsto (fun n => g (ns (ms n)) ω) atTop (𝓝 (gLimit ω)) at hω
      exact hω
    exact integral_bcf_eq_of_map_eq_of_ae_tendsto fs gs fLimit gLimit
      hfs hgs hmaps hfseq hgseq φ
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro φ
  calc
    (∫ x, φ x ∂Measure.map fLimit P) = ∫ ω, φ (fLimit ω) ∂P :=
      integral_map hflimit φ.continuous.measurable.aestronglyMeasurable
    _ = ∫ ω, φ (gLimit ω) ∂P' := htest φ
    _ = ∫ x, φ x ∂Measure.map gLimit P' :=
      (integral_map hglimit φ.continuous.measurable.aestronglyMeasurable).symm

/-- Coordinatewise convergence in measure implies convergence in measure for a finite real vector.
The sup norm event is contained in the finite union of its coordinate events. -/
theorem tendstoInMeasure_pi_finite
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (f : ℕ → Ω → ι → ℝ) (g : Ω → ι → ℝ)
    (hcoord : ∀ i, TendstoInMeasure μ (fun n ω => f n ω i) atTop (fun ω => g ω i)) :
    TendstoInMeasure μ f atTop g := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hsubset (n : ℕ) : {ω | ε ≤ ‖f n ω - g ω‖} ⊆
      ⋃ i, {ω | ε ≤ ‖f n ω i - g ω i‖} := by
    intro ω hω
    change ε ≤ ‖f n ω - g ω‖ at hω
    by_contra hnot
    have hcoord : ∀ i, ‖(f n ω - g ω) i‖ < ε := by
      intro i
      apply lt_of_not_ge
      intro h
      exact hnot (Set.mem_iUnion.2 ⟨i, by simpa using h⟩)
    have hnorm : ‖f n ω - g ω‖ < ε :=
      (pi_norm_lt_iff hε).2 (by simpa only [Pi.sub_apply] using hcoord)
    exact (not_le_of_gt hnorm) hω
  have hsum : Tendsto (fun n => ∑ i : ι, μ {ω | ε ≤ ‖f n ω i - g ω i‖})
      atTop (𝓝 0) := by
    have hsum' : Tendsto (fun n => ∑ i : ι, μ {ω | ε ≤ ‖f n ω i - g ω i‖})
        atTop (𝓝 (∑ i : ι, (0 : ℝ≥0∞))) := by
      exact tendsto_finsetSum
        (f := fun i n => μ {ω | ε ≤ ‖f n ω i - g ω i‖}) (x := atTop)
        (a := fun _ => (0 : ℝ≥0∞)) Finset.univ
        (by intro i hi; exact (tendstoInMeasure_iff_norm.mp (hcoord i)) ε hε)
    simpa using hsum'
  have hle (n : ℕ) : μ {ω | ε ≤ ‖f n ω - g ω‖} ≤
      ∑ i : ι, μ {ω | ε ≤ ‖f n ω i - g ω i‖} := by
    exact (measure_mono (hsubset n)).trans (measure_iUnion_fintype_le μ _)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le) hle

/-- Finite-cutoff equality of all test-vector laws passes to arbitrary chaos limits specified by
test-integral convergence in measure. This is the limit transfer needed for `IsGMCOf`; it does not
construct a preferred GMC version. -/
theorem gmc_limit_test_vector_law
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsFiniteMeasure P] [IsFiniteMeasure P']
    {m : ℕ} (cutoffX : ℕ → Ω → Fin m → ℝ)
    (cutoffY : ℕ → Ω' → Fin m → ℝ) (limitX : Ω → Fin m → ℝ)
    (limitY : Ω' → Fin m → ℝ)
    (hcutoffX : ∀ n, AEMeasurable (cutoffX n) P)
    (hcutoffY : ∀ n, AEMeasurable (cutoffY n) P')
    (hlimitX : AEMeasurable limitX P) (hlimitY : AEMeasurable limitY P')
    (hcutoffLaw : ∀ n, Measure.map (cutoffX n) P = Measure.map (cutoffY n) P')
    (hconvX : ∀ j, TendstoInMeasure P (fun n ω => cutoffX n ω j) atTop
      (fun ω => limitX ω j))
    (hconvY : ∀ j, TendstoInMeasure P' (fun n ω => cutoffY n ω j) atTop
      (fun ω => limitY ω j)) :
    Measure.map limitX P = Measure.map limitY P' := by
  exact map_eq_of_seq_map_eq_of_tendstoInMeasure cutoffX cutoffY limitX limitY
    hcutoffX hcutoffY hlimitX hlimitY hcutoffLaw
    (tendstoInMeasure_pi_finite P cutoffX limitX hconvX)
    (tendstoInMeasure_pi_finite P' cutoffY limitY hconvY)



end DOZZ.Proofs

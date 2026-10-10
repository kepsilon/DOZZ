/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-/
module

public import DOZZ.GMC.Construction.RootedMeasureKernel
public import Mathlib.MeasureTheory.Measure.GiryMonad

/-! Measurable marked random measures and their expected rectangle masses. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace DOZZ.Proofs

/-- Attaching a measurable sample mark to a finite random measure gives a measurable measure
family on the product. No uniform bound on its masses is required. -/
theorem measurable_markedMeasure_family
    {Ω U V : Type*} [MeasurableSpace Ω] [MeasurableSpace U] [MeasurableSpace V]
    (M : Ω → Measure U) (hM : Measurable M) (hfinite : ∀ ω, IsFiniteMeasure (M ω))
    (q : Ω → V) (hq : Measurable q) :
    Measurable (fun ω => Measure.map (fun u => (u, q ω)) (M ω)) := by
  apply Measure.measurable_of_measurable_coe
  intro S hS
  have hmap (ω : Ω) : Measurable (fun u : U => (u, q ω)) :=
    measurable_id.prodMk measurable_const
  have heq : (fun ω => Measure.map (fun u => (u, q ω)) (M ω) S) =
      fun ω => ∫⁻ u, S.indicator (fun _ => (1 : ℝ≥0∞)) (u, q ω) ∂M ω := by
    funext ω
    rw [Measure.map_apply (hmap ω) hS]
    have hi := lintegral_indicator_const_comp (μ := M ω) (f := fun u : U => (u, q ω)) (hmap ω) hS 1
    simpa only [one_mul] using hi.symm
  rw [heq]
  apply measurable_lintegral_finite_family M hM hfinite
    (fun p : Ω × U => S.indicator (fun _ => (1 : ℝ≥0∞)) (p.2, q p.1))
  exact ((measurable_const.indicator hS).comp
    (measurable_snd.prodMk (hq.comp measurable_fst)))

/-- The expected marked measure is finite whenever the expected total mass is finite. -/
theorem isFiniteMeasure_bind_markedMeasure
    {Ω U V : Type*} [MeasurableSpace Ω] [MeasurableSpace U] [MeasurableSpace V]
    (P : Measure Ω) (M : Ω → Measure U) (hM : Measurable M)
    (hfinite : ∀ ω, IsFiniteMeasure (M ω)) (q : Ω → V) (hq : Measurable q)
    (hmean : (∫⁻ ω, M ω Set.univ ∂P) < ⊤) :
    IsFiniteMeasure (P.bind (fun ω => Measure.map (fun u => (u, q ω)) (M ω))) := by
  constructor
  rw [Measure.bind_apply MeasurableSet.univ
    (measurable_markedMeasure_family M hM hfinite q hq).aemeasurable]
  have heq (ω : Ω) : Measure.map (fun u => (u, q ω)) (M ω) Set.univ = M ω Set.univ := by
    rw [Measure.map_apply (show Measurable (fun u : U => (u, q ω)) from
      measurable_id.prodMk measurable_const) MeasurableSet.univ,
      Set.preimage_univ]
  simpa only [heq] using hmean

/-- Rectangle masses of the expected marked measure are the marked-law masses weighted by the
random mass of the root set. -/
theorem bind_markedMeasure_apply_prod
    {Ω U V : Type*} [MeasurableSpace Ω] [MeasurableSpace U] [MeasurableSpace V]
    (P : Measure Ω) (M : Ω → Measure U) (hM : Measurable M)
    (hfinite : ∀ ω, IsFiniteMeasure (M ω)) (q : Ω → V) (hq : Measurable q)
    (A : Set U) (hA : MeasurableSet A) (D : Set V) (hD : MeasurableSet D) :
    P.bind (fun ω => Measure.map (fun u => (u, q ω)) (M ω)) (A ×ˢ D) =
      Measure.map q (P.withDensity (fun ω => M ω A)) D := by
  rw [Measure.bind_apply (hA.prod hD)
    (measurable_markedMeasure_family M hM hfinite q hq).aemeasurable,
    Measure.map_apply hq hD, withDensity_apply _ (hD.preimage hq),
    ← lintegral_indicator (hD.preimage hq)]
  apply lintegral_congr
  intro ω
  rw [Measure.map_apply (show Measurable (fun u : U => (u, q ω)) from
      measurable_id.prodMk measurable_const) (hA.prod hD)]
  by_cases hω : q ω ∈ D
  · rw [Set.indicator_of_mem (show ω ∈ q ⁻¹' D from hω)]
    congr 1
    ext u
    simp only [Set.mem_preimage, Set.mem_prod, hω, and_true]
  · rw [Set.indicator_of_notMem (show ω ∉ q ⁻¹' D from hω)]
    have he : (fun u => (u, q ω)) ⁻¹' (A ×ˢ D) = ∅ := by
      ext u
      simp only [Set.mem_preimage, Set.mem_prod, hω, and_false, Set.mem_empty_iff_false]
    rw [he, measure_empty]

end DOZZ.Proofs

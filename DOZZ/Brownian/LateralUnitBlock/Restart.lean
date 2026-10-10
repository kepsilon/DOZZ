/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Barrier.Restart
public import DOZZ.Statements.Brownian.BrownianStoppedEvents
public import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# Restart at finite, possibly unbounded, raw stopping times

The restart theorem for bounded stopping times is localized to `A ∩ {τ ≤ n}`. Increasing
unions then identify the whole future law on every stopped event, without completing the
filtration.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace DOZZ.Proofs

/-- Every raw natural sigma algebra is contained in the sigma algebra of the whole path. -/
theorem lateralUnitBlock_naturalSigma_le_pathSigma {Ω : Type*} (B : Ω → BrownianPath) (t : ℝ≥0) :
    brownianNaturalSigma B t ≤ MeasurableSpace.comap B inferInstance := by
  apply iSup_le
  intro s
  apply iSup_le
  intro _
  exact ((ContinuousMap.measurable_eval s).comp
    (Measurable.of_comap_le le_rfl)).comap_le

/-- A finite raw stopping time is a measurable function of the original Brownian path. -/
theorem lateralUnitBlock_stoppingTime_measurable_pathSigma {Ω : Type*}
    (B : Ω → BrownianPath) (τ : Ω → ℝ≥0) (hτ : IsBrownianStoppingTime B τ) :
    Measurable[MeasurableSpace.comap B inferInstance] τ := by
  apply measurable_of_Iic
  intro t
  exact lateralUnitBlock_naturalSigma_le_pathSigma B t _ (hτ t)

/-- Stopped events are measurable functions of the original whole path. -/
theorem lateralUnitBlock_stoppedEvent_measurable_pathSigma {Ω : Type*}
    (B : Ω → BrownianPath) (τ : Ω → ℝ≥0) (G : Set Ω)
    (hG : G ∈ brownianStoppedEvents B τ) :
    MeasurableSet[MeasurableSpace.comap B inferInstance] G := by
  have hu : (⋃ n : ℕ, G ∩ {ω | τ ω ≤ (n : ℝ≥0)}) = G := by
    ext ω
    simp only [mem_iUnion]
    constructor
    · rintro ⟨n, hω⟩
      exact hω.1
    · intro hω
      obtain ⟨n, hn⟩ := exists_nat_ge (τ ω)
      exact ⟨n, hω, hn⟩
  rw [← hu]
  exact MeasurableSet.iUnion fun n => lateralUnitBlock_naturalSigma_le_pathSigma B n _ (hG n)

/-- The finite raw stopping-time predicate `DOZZ.IsBrownianStoppingTime` agrees with
`IsStoppingTime` for the raw filtration. -/
theorem lateralUnitBlock_isStoppingTime {Ω : Type*} [MeasurableSpace Ω]
    (B : Ω → BrownianPath) (hBm : ∀ t, Measurable fun ω => B ω t)
    (τ : Ω → ℝ≥0) (hτ : IsBrownianStoppingTime B τ) :
    IsStoppingTime (brownianRawFiltration (fun t ω => B ω t) hBm)
      (fun ω => (τ ω : WithTop ℝ≥0)) := by
  intro t
  change MeasurableSet[brownianNaturalSigma B t] {ω | (τ ω : WithTop ℝ≥0) ≤ t}
  simpa only [WithTop.coe_le_coe] using hτ t

/-- Finite-valued stopped events need no additional global-measurability premise. -/
theorem lateralUnitBlock_stoppedEvent_measurableSpace {Ω : Type*} [MeasurableSpace Ω]
    (B : Ω → BrownianPath) (hBm : ∀ t, Measurable fun ω => B ω t)
    (τ : Ω → ℝ≥0) (hτ : IsBrownianStoppingTime B τ)
    (G : Set Ω) (hG : G ∈ brownianStoppedEvents B τ) :
    MeasurableSet[(lateralUnitBlock_isStoppingTime B hBm τ hτ).measurableSpace] G := by
  refine ⟨?_, ?_⟩
  · have hu : (⋃ n : ℕ, G ∩ {ω | τ ω ≤ (n : ℝ≥0)}) = G := by
      ext ω
      simp only [mem_iUnion]
      constructor
      · rintro ⟨n, hω⟩
        exact hω.1
      · intro hω
        obtain ⟨n, hn⟩ := exists_nat_ge (τ ω)
        exact ⟨n, hω, hn⟩
    rw [← hu]
    exact MeasurableSet.iUnion fun n =>
      (le_iSup (fun t => brownianNaturalSigma B t) (n : ℝ≥0)) _ (hG n)
  · intro t
    change MeasurableSet[brownianNaturalSigma B t]
      (G ∩ {ω | (τ ω : WithTop ℝ≥0) ≤ t})
    simpa only [WithTop.coe_le_coe] using hG t

/-- A finite raw stopping time restarts the entire evaluation-generated Brownian process. -/
theorem lateralUnitBlock_stopped_process_restrict_map {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hm : ∀ s, Measurable (B s))
    (hBm : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime (brownianRawFiltration B hm)
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (A : Set Ω) (hA : MeasurableSet[hτ.measurableSpace] A) :
    (P.restrict A).map (fun ω t => B (τ ω + t) ω - B (τ ω) ω) =
      P A • P.map (fun ω t => B t ω) := by
  classical
  let 𝓕 := brownianRawFiltration B hm
  let V : Ω → ℝ≥0 → ℝ := fun ω t => B (τ ω + t) ω - B (τ ω) ω
  have hV : Measurable V := Measurable.of_eval fun t =>
    measurable_brownian_random_increment B hBm τ
      (measurable_finite_brownian_stoppingTime _ τ hτ) t
  let Aₙ : ℕ → Set Ω := fun n => A ∩ {ω | τ ω ≤ (n : ℝ≥0)}
  have hmono : Monotone Aₙ := by
    intro n m hnm ω hω
    exact ⟨hω.1, hω.2.trans (Nat.cast_le.mpr hnm)⟩
  have hUnion : (⋃ n, Aₙ n) = A := by
    ext ω
    simp only [mem_iUnion]
    constructor
    · rintro ⟨n, hω⟩
      exact hω.1
    · intro hω
      obtain ⟨n, hn⟩ := exists_nat_ge (τ ω)
      exact ⟨n, hω, hn⟩
  have hlocal n (S : Set (ℝ≥0 → ℝ)) (hS : MeasurableSet S) :
      P (Aₙ n ∩ V ⁻¹' S) = P (Aₙ n) * (P.map (fun ω t => B t ω)) S := by
    let τₙ : Ω → ℝ≥0 := fun ω => min (τ ω) n
    have hτn : IsStoppingTime 𝓕 (fun ω => (τₙ ω : WithTop ℝ≥0)) := by
      simpa only [τₙ, WithTop.coe_min] using hτ.min_const (n : ℝ≥0)
    have hAn : MeasurableSet[hτn.measurableSpace] (Aₙ n) := by
      simpa only [Aₙ, WithTop.coe_le_coe] using
        (hτ.measurableSet_inter_le_const_iff A (n : ℝ≥0)).mp
          (hA.inter (hτ.measurableSet_le' (n : ℝ≥0)))
    have he := congrArg (fun μ : Measure (ℝ≥0 → ℝ) => μ S)
      (brownian_bounded_stopped_process_restrict_map hB hm hBm τₙ hτn n
        (fun _ => min_le_right _ _) (Aₙ n) hAn)
    have hVn : Measurable (fun ω t => B (τₙ ω + t) ω - B (τₙ ω) ω) :=
      Measurable.of_eval fun t => measurable_brownian_random_increment B hBm τₙ
        (measurable_finite_brownian_stoppingTime _ τₙ hτn) t
    rw [Measure.map_apply hVn hS, Measure.restrict_apply (hS.preimage hVn),
      Measure.smul_apply] at he
    have hsets : (fun ω t => B (τₙ ω + t) ω - B (τₙ ω) ω) ⁻¹' S ∩ Aₙ n =
        Aₙ n ∩ V ⁻¹' S := by
      ext ω
      by_cases ha : ω ∈ Aₙ n
      · have ht : τₙ ω = τ ω := min_eq_left ha.2
        simp only [mem_inter_iff, mem_preimage, ha, true_and, and_true, ht, V]
      · simp only [mem_inter_iff, ha, and_false, false_and]
    rwa [hsets] at he
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply hV hS, Measure.restrict_apply (hS.preimage hV),
    Measure.smul_apply, inter_comm]
  have hu : (⋃ n, Aₙ n ∩ V ⁻¹' S) = A ∩ V ⁻¹' S := by
    rw [← iUnion_inter, hUnion]
  have hd : Monotone (fun n => Aₙ n ∩ V ⁻¹' S) := fun n m hnm =>
    inter_subset_inter_left _ (hmono hnm)
  rw [← hu, hd.measure_iUnion, ← hUnion, hmono.measure_iUnion, smul_eq_mul,
    ENNReal.iSup_mul]
  exact iSup_congr fun n => hlocal n S hS

/-- Restart identifies the literal continuous future path on each stopped event. -/
theorem lateralUnitBlock_stopped_path_restrict_map {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : Ω → BrownianPath)
    (hBm : ∀ t, Measurable fun ω => B ω t)
    (hB : IsBrownianReal (fun t ω => B ω t) P)
    (τ : Ω → ℝ≥0) (hτ : IsBrownianStoppingTime B τ)
    (G : Set Ω) (hG : G ∈ brownianStoppedEvents B τ) :
    (P.restrict G).map (fun ω => brownianShiftPath (τ ω) (B ω)) = P G • P.map B := by
  have hmB : Measurable B := ContinuousMap.measurable_iff_eval.mpr hBm
  have hmτ : Measurable τ :=
    (lateralUnitBlock_stoppingTime_measurable_pathSigma B τ hτ).mono hmB.comap_le le_rfl
  have hmU : Measurable (fun ω => brownianShiftPath (τ ω) (B ω)) :=
    continuous_brownianShiftPath.measurable.comp (hmτ.prodMk hmB)
  have heval : Measurable (fun p : BrownianPath => fun t => p t) :=
    Measurable.of_eval fun t => ContinuousMap.measurable_eval t
  apply brownianPath_measure_eq_of_process_map_eq
  rw [Measure.map_map heval hmU, Measure.map_smul _ heval.aemeasurable,
    Measure.map_map heval hmB]
  have hj : Measurable (fun p : ℝ≥0 × Ω => B p.2 p.1) :=
    continuous_eval.measurable.comp ((hmB.comp measurable_snd).prodMk measurable_fst)
  exact lateralUnitBlock_stopped_process_restrict_map hB hBm hj τ (lateralUnitBlock_isStoppingTime B hBm τ hτ)
    G (lateralUnitBlock_stoppedEvent_measurableSpace B hBm τ hτ G hG)

/-- The future continuous path has the original path law at every finite raw stopping time. -/
theorem lateralUnitBlock_stopped_path_map {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : Ω → BrownianPath)
    (hBm : ∀ t, Measurable fun ω => B ω t)
    (hB : IsBrownianReal (fun t ω => B ω t) P)
    (τ : Ω → ℝ≥0) (hτ : IsBrownianStoppingTime B τ) :
    P.map (fun ω => brownianShiftPath (τ ω) (B ω)) = P.map B := by
  let _ := (hB.hasLaw_eval 0).isProbabilityMeasure
  simpa only [Measure.restrict_univ, measure_univ, one_smul] using
    lateralUnitBlock_stopped_path_restrict_map P B hBm hB τ hτ univ
      (fun _ => MeasurableSet.univ.inter (hτ _))

/-- The stopping time is measurable in its own raw stopped sigma algebra. -/
theorem lateralUnitBlock_stoppingTime_measurable_stopped {Ω : Type*} [MeasurableSpace Ω]
    (B : Ω → BrownianPath) (hBm : ∀ t, Measurable fun ω => B ω t)
    (τ : Ω → ℝ≥0) (hτ : IsBrownianStoppingTime B τ) :
    Measurable[(lateralUnitBlock_isStoppingTime B hBm τ hτ).measurableSpace] τ := by
  apply measurable_of_Iic
  intro t
  simpa only [Set.preimage, mem_Iic, WithTop.coe_le_coe] using
    (lateralUnitBlock_isStoppingTime B hBm τ hτ).measurableSet_le' t

/-- The raw stopped sigma algebra is contained in the sigma algebra of the original path. -/
theorem lateralUnitBlock_stoppedSigma_le_pathSigma {Ω : Type*} [MeasurableSpace Ω]
    (B : Ω → BrownianPath) (hBm : ∀ t, Measurable fun ω => B ω t)
    (τ : Ω → ℝ≥0) (hτ : IsBrownianStoppingTime B τ) :
    (lateralUnitBlock_isStoppingTime B hBm τ hτ).measurableSpace ≤
      MeasurableSpace.comap B inferInstance := by
  intro A hA
  apply lateralUnitBlock_stoppedEvent_measurable_pathSigma B τ A
  intro t
  have ha := hA.2 t
  change MeasurableSet[brownianNaturalSigma B t]
    (A ∩ {ω | (τ ω : WithTop ℝ≥0) ≤ t}) at ha
  simpa only [WithTop.coe_le_coe] using ha

/-- The literal future continuous path is independent of the raw stopped sigma algebra. -/
theorem lateralUnitBlock_stopped_path_indep {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (B : Ω → BrownianPath)
    (hBm : ∀ t, Measurable fun ω => B ω t)
    (hB : IsBrownianReal (fun t ω => B ω t) P)
    (τ : Ω → ℝ≥0) (hτ : IsBrownianStoppingTime B τ) :
    Indep (lateralUnitBlock_isStoppingTime B hBm τ hτ).measurableSpace
      (MeasurableSpace.comap (fun ω => brownianShiftPath (τ ω) (B ω)) inferInstance) P := by
  have hmB : Measurable B := ContinuousMap.measurable_iff_eval.mpr hBm
  have hmτ : Measurable τ :=
    (lateralUnitBlock_stoppingTime_measurable_pathSigma B τ hτ).mono hmB.comap_le le_rfl
  let U : Ω → BrownianPath := fun ω => brownianShiftPath (τ ω) (B ω)
  have hmU : Measurable U :=
    continuous_brownianShiftPath.measurable.comp (hmτ.prodMk hmB)
  apply (Indep_iff _ _ P).mpr
  intro A E hA hE
  obtain ⟨S, hS, rfl⟩ := hE
  have hAf : A ∈ brownianStoppedEvents B τ := by
    intro t
    have ha := hA.2 t
    change MeasurableSet[brownianNaturalSigma B t]
      (A ∩ {ω | (τ ω : WithTop ℝ≥0) ≤ t}) at ha
    simpa only [WithTop.coe_le_coe] using ha
  have he := congrArg (fun μ : Measure BrownianPath => μ S)
    (lateralUnitBlock_stopped_path_restrict_map P B hBm hB τ hτ A hAf)
  rw [Measure.map_apply hmU hS, Measure.restrict_apply (hS.preimage hmU),
    Measure.smul_apply, smul_eq_mul, inter_comm] at he
  change P (A ∩ U ⁻¹' S) = P A * P (U ⁻¹' S)
  rw [← Measure.map_apply hmU hS, lateralUnitBlock_stopped_path_map P B hBm hB τ hτ]
  exact he

end DOZZ.Proofs

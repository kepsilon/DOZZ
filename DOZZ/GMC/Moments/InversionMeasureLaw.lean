/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.GMC.Moments.InversionOpenMassLaw
public import DOZZ.GMC.EquatorGFFChaosTransportLaw
@[expose] public section
open Filter MeasureTheory Set
open scoped Topology Distributions ENNReal
namespace DOZZ.Proofs

private abbrev InversionFiniteMeasure := {μ : Measure ℂ // IsFiniteMeasure μ}
private abbrev InversionOpen := {U : Set ℂ // IsOpen U}
private def inversionMeasureCode (μ : InversionFiniteMeasure) : InversionOpen → ℝ≥0∞ :=
  fun U => μ.1 U.1

/-- Finite random measure laws are determined by their finite vectors of open masses. -/
theorem finite_random_measure_law_of_open_fdd
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (M N : Ω → Measure ℂ) (hM : Measurable M) (hN : Measurable N)
    (hMf : ∀ ω, IsFiniteMeasure (M ω)) (hNf : ∀ ω, IsFiniteMeasure (N ω))
    (hfdd : ∀ (ι : Type) [Fintype ι] (U : ι → Set ℂ), (∀ j, IsOpen (U j)) →
      P.map (fun ω j => M ω (U j)) = P.map (fun ω j => N ω (U j)))
    (H : Measure ℂ → ℝ≥0∞) (hH : Measurable H) :
    ∫⁻ ω, H (M ω) ∂P = ∫⁻ ω, H (N ω) ∂P := by
  classical
  let C := measurableCylinders (fun _ : InversionOpen => ℝ≥0∞)
  let mOutput : MeasurableSpace InversionFiniteMeasure :=
    MeasurableSpace.pi.comap inversionMeasureCode
  let : MeasurableSpace InversionFiniteMeasure := mOutput
  let outM : Ω → InversionFiniteMeasure := fun ω => ⟨M ω, hMf ω⟩
  let outN : Ω → InversionFiniteMeasure := fun ω => ⟨N ω, hNf ω⟩
  let Cout := Set.preimage inversionMeasureCode '' C
  have hgen : mOutput = MeasurableSpace.generateFrom Cout := by
    dsimp [mOutput, Cout, C]
    rw [← generateFrom_measurableCylinders, MeasurableSpace.comap_generateFrom]
  have hpi : IsPiSystem Cout := by
    intro A hA B hB hAB
    rcases hA with ⟨A', hA', rfl⟩
    rcases hB with ⟨B', hB', rfl⟩
    refine ⟨A' ∩ B', isPiSystem_measurableCylinders A' hA' B' hB' ?_, ?_⟩
    · rcases hAB with ⟨q, hq⟩
      exact ⟨inversionMeasureCode q, ⟨hq.1, hq.2⟩⟩
    · rw [← Set.preimage_inter]
  have hcode : Measurable inversionMeasureCode := Measurable.of_comap_le le_rfl
  have hcm : Measurable (inversionMeasureCode ∘ outM) :=
    measurable_pi_iff.mpr fun U => (Measure.measurable_coe U.2.measurableSet).comp hM
  have hcn : Measurable (inversionMeasureCode ∘ outN) :=
    measurable_pi_iff.mpr fun U => (Measure.measurable_coe U.2.measurableSet).comp hN
  have hom : Measurable outM := by
    rw [measurable_iff_comap_le]
    change mOutput.comap outM ≤ ‹MeasurableSpace Ω›
    rw [show mOutput = MeasurableSpace.pi.comap inversionMeasureCode by rfl,
      MeasurableSpace.comap_comp]
    exact hcm.comap_le
  have hon : Measurable outN := by
    rw [measurable_iff_comap_le]
    change mOutput.comap outN ≤ ‹MeasurableSpace Ω›
    rw [show mOutput = MeasurableSpace.pi.comap inversionMeasureCode by rfl,
      MeasurableSpace.comap_comp]
    exact hcn.comap_le
  have hOpenGen : (inferInstance : MeasurableSpace ℂ) =
      MeasurableSpace.generateFrom {s : Set ℂ | IsOpen s} := by
    calc
      (inferInstance : MeasurableSpace ℂ) = borel ℂ := BorelSpace.measurable_eq
      _ = _ := borel_eq_generateFrom_of_subbasis
        (TopologicalSpace.generateFrom_setOfPred_isOpen (inferInstance : TopologicalSpace ℂ)).symm
  have hforget : Measurable (fun q : InversionFiniteMeasure => q.1) := by
    let : ∀ q : InversionFiniteMeasure, IsFiniteMeasure q.1 := fun q => q.2
    apply Measurable.measure_of_isPiSystem hOpenGen isPiSystem_isOpen
    · intro s hs
      exact (measurable_pi_iff.mp hcode) ⟨s, hs⟩
    · exact (measurable_pi_iff.mp hcode) ⟨univ, isOpen_univ⟩
  have hLaw : P.map outM = P.map outN := by
    apply MeasureTheory.ext_of_generate_finite Cout hgen hpi
    · intro S hS
      rcases hS with ⟨A, hA, rfl⟩
      rcases (mem_measurableCylinders A).1 hA with ⟨s, As, hAs, rfl⟩
      let vm := fun ω (j : s) => M ω j.1.1
      let vn := fun ω (j : s) => N ω j.1.1
      have hm : Measurable vm := measurable_pi_iff.mpr fun j =>
        (Measure.measurable_coe j.1.2.measurableSet).comp hM
      have hn : Measurable vn := measurable_pi_iff.mpr fun j =>
        (Measure.measurable_coe j.1.2.measurableSet).comp hN
      have hv := hfdd s (fun j => j.1.1) (fun j => j.1.2)
      have hp : P (vm ⁻¹' As) = P (vn ⁻¹' As) := by
        have h := congrArg (fun μ => μ As) hv
        rw [Measure.map_apply hm hAs, Measure.map_apply hn hAs] at h
        exact h
      have hs : MeasurableSet (inversionMeasureCode ⁻¹' cylinder s As) := by
        apply hcode
        rw [← generateFrom_measurableCylinders]
        exact MeasurableSpace.measurableSet_generateFrom
          (cylinder_mem_measurableCylinders (α := fun _ : InversionOpen => ℝ≥0∞) s As hAs)
      rw [Measure.map_apply hom hs, Measure.map_apply hon hs]
      exact hp
    · simp only [Measure.map_apply hom MeasurableSet.univ,
        Measure.map_apply hon MeasurableSet.univ, preimage_univ]
  have hh := hH.comp hforget
  calc
    ∫⁻ ω, H (M ω) ∂P = ∫⁻ q, H q.1 ∂P.map outM := (lintegral_map hh hom).symm
    _ = ∫⁻ q, H q.1 ∂P.map outN := by rw [hLaw]
    _ = ∫⁻ ω, H (N ω) ∂P := lintegral_map hh hon
end DOZZ.Proofs

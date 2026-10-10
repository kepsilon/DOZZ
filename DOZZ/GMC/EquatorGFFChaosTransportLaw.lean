/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.EquatorGFFChaosTransport
public import DOZZ.GMC.Construction.GMCMeasurableVersion
public import DOZZ.GMC.Construction.FiniteMeasureTotalize
public import DOZZ.GMC.Moments.ChaosLawFDD

/-! Measurable-law transport for the equator field and its GMC. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

private abbrev GMCOpen := {U : Set ℂ // IsOpen U}
private abbrev FiniteComplexMeasure := {μ : Measure ℂ // IsFiniteMeasure μ}
private abbrev GMCTransportOutput := (TestFn → ℝ) × FiniteComplexMeasure

private def gmcOutputCode (q : GMCTransportOutput) :
    (TestFn → ℝ) × (GMCOpen → ℝ≥0∞) :=
  (q.1, fun U => q.2.1 U.1)

/-- Open-set masses of a finite chaos are measurable, by approximation with bounded continuous
distance cutoffs. -/
theorem gmc_open_mass_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (U : Set ℂ) (hU : IsOpen U) :
    AEMeasurable (fun ω => M ω U) P := by
  classical
  rcases hM with ⟨hfinite, Xc, hXc, hconv⟩
  let f : ℕ → BoundedContinuousFunction ℂ ℝ := fun n => gmcOpenApprox U hU n
  have hf : ∀ n, AEMeasurable (fun ω => ∫ x, f n x ∂M ω) P := by
    intro n
    exact gmc_test_integral_aemeasurable_of_IsGMCOf P X hX γ M ⟨hfinite, Xc, hXc, hconv⟩ (f n)
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => ∫ x, f n x ∂M ω) atTop
      (𝓝 ((M ω U).toReal)) := by
    filter_upwards [] with ω
    let : IsFiniteMeasure (M ω) := hfinite ω
    exact gmcOpenApprox_integral_tendsto (M ω) U hU
  have hreal : AEMeasurable (fun ω => (M ω U).toReal) P := by
    simpa [f] using aemeasurable_of_tendsto_metrizable_ae atTop hf hlim
  have hfiniteU : ∀ ω, M ω U ≠ ∞ := fun ω => measure_ne_top (M ω) U
  have hEq : (fun ω => M ω U) = fun ω => ENNReal.ofReal (M ω U).toReal := by
    funext ω
    exact (ENNReal.ofReal_toReal (hfiniteU ω)).symm
  rw [hEq]
  exact ENNReal.measurable_ofReal.aemeasurable.comp_aemeasurable hreal

/-- The open-mass finite-dimensional law extends from `Fin` to arbitrary finite index types. -/
theorem equatorGFF_GMC_open_mass_test_fintype_law
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (P' : Measure Ω') (X' : Ω' → Distr) (hX' : IsEquatorGFF P' X')
    (γ : ℝ) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (M' : Ω' → Measure ℂ) (hM' : IsGMCOf P' X' γ M')
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (tests : ι → TestFn) (U : κ → Set ℂ) (hU : ∀ j, IsOpen (U j)) :
    Measure.map (fun ω => (fun i => X ω (tests i), fun j => M ω (U j))) P =
      Measure.map (fun ω => (fun i => X' ω (tests i), fun j => M' ω (U j))) P' := by
  classical
  let eι : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let eκ : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  let baseX : Ω → (Fin (Fintype.card ι) → ℝ) × (Fin (Fintype.card κ) → ℝ) := fun ω =>
    (fun i => X ω (tests (eι i)), fun j => (M ω (U (eκ j))).toReal)
  let baseY : Ω' → (Fin (Fintype.card ι) → ℝ) × (Fin (Fintype.card κ) → ℝ) := fun ω =>
    (fun i => X' ω (tests (eι i)), fun j => (M' ω (U (eκ j))).toReal)
  let reindex : ((Fin (Fintype.card ι) → ℝ) × (Fin (Fintype.card κ) → ℝ)) →
      (ι → ℝ) × (κ → ℝ≥0∞) := fun q =>
        (fun i => q.1 (eι.symm i), fun j => ENNReal.ofReal (q.2 (eκ.symm j)))
  have hbase : Measure.map baseX P = Measure.map baseY P' := by
    have h := equatorGFF_GMC_open_mass_test_vector_law P X hX P' X' hX' γ M hM M' hM'
      (fun i => tests (eι i)) (fun j => U (eκ j)) (fun j => hU (eκ j))
    let toReal : ((Fin (Fintype.card ι) → ℝ) ×
        (Fin (Fintype.card κ) → ℝ≥0∞)) →
        (Fin (Fintype.card ι) → ℝ) × (Fin (Fintype.card κ) → ℝ) := fun q =>
          (q.1, fun j => (q.2 j).toReal)
    have htoReal : Measurable toReal := by fun_prop
    let rawX : Ω → (Fin (Fintype.card ι) → ℝ) ×
        (Fin (Fintype.card κ) → ℝ≥0∞) := fun ω =>
          (fun i => X ω (tests (eι i)), fun j => M ω (U (eκ j)))
    let rawY : Ω' → (Fin (Fintype.card ι) → ℝ) ×
        (Fin (Fintype.card κ) → ℝ≥0∞) := fun ω =>
          (fun i => X' ω (tests (eι i)), fun j => M' ω (U (eκ j)))
    have hrawX : AEMeasurable rawX P := by
      apply (measurable_pi_iff.mpr fun i => (hX.2 (tests (eι i))).1).aemeasurable.prodMk
      apply AEMeasurable.of_eval
      intro j
      exact gmc_open_mass_aemeasurable P X hX γ M hM (U (eκ j)) (hU (eκ j))
    have hrawY : AEMeasurable rawY P' := by
      apply (measurable_pi_iff.mpr fun i => (hX'.2 (tests (eι i))).1).aemeasurable.prodMk
      apply AEMeasurable.of_eval
      intro j
      exact gmc_open_mass_aemeasurable P' X' hX' γ M' hM' (U (eκ j)) (hU (eκ j))
    calc
      Measure.map baseX P = (Measure.map rawX P).map toReal := by
        change Measure.map (toReal ∘ rawX) P = _
        exact (AEMeasurable.map_map_of_aemeasurable htoReal.aemeasurable hrawX).symm
      _ = (Measure.map rawY P').map toReal :=
        congrArg (Measure.map toReal) h
      _ = Measure.map baseY P' := by
        change _ = Measure.map (toReal ∘ rawY) P'
        exact AEMeasurable.map_map_of_aemeasurable htoReal.aemeasurable hrawY
  have hmassX : ∀ ω j, ENNReal.ofReal (M ω (U j)).toReal = M ω (U j) := by
    intro ω j
    let : IsFiniteMeasure (M ω) := hM.1 ω
    exact ENNReal.ofReal_toReal (measure_ne_top (M ω) (U j))
  have hmassY : ∀ ω j, ENNReal.ofReal (M' ω (U j)).toReal = M' ω (U j) := by
    intro ω j
    let : IsFiniteMeasure (M' ω) := hM'.1 ω
    exact ENNReal.ofReal_toReal (measure_ne_top (M' ω) (U j))
  have hbaseXmeas : AEMeasurable baseX P := by
    apply (measurable_pi_iff.mpr fun i => (hX.2 (tests (eι i))).1).aemeasurable.prodMk
    apply AEMeasurable.of_eval
    intro j
    exact ENNReal.measurable_toReal.comp_aemeasurable
      (gmc_open_mass_aemeasurable P X hX γ M hM (U (eκ j)) (hU (eκ j)))
  have hbaseYmeas : AEMeasurable baseY P' := by
    apply (measurable_pi_iff.mpr fun i => (hX'.2 (tests (eι i))).1).aemeasurable.prodMk
    apply AEMeasurable.of_eval
    intro j
    exact ENNReal.measurable_toReal.comp_aemeasurable
      (gmc_open_mass_aemeasurable P' X' hX' γ M' hM' (U (eκ j)) (hU (eκ j)))
  have hpost : Measurable reindex := by fun_prop
  have hmapX : Measure.map (fun ω => (fun i => X ω (tests i), fun j => M ω (U j))) P =
      (Measure.map baseX P).map reindex := by
    have hEq : (fun ω => (fun i => X ω (tests i), fun j => M ω (U j))) = reindex ∘ baseX := by
      funext ω
      apply Prod.ext
      · funext i
        simp [reindex, baseX]
      · funext j
        simp only [reindex, baseX, Function.comp_apply, Equiv.apply_symm_apply]
        exact (hmassX ω j).symm
    rw [hEq]
    exact (AEMeasurable.map_map_of_aemeasurable hpost.aemeasurable hbaseXmeas).symm
  have hmapY : Measure.map (fun ω => (fun i => X' ω (tests i), fun j => M' ω (U j))) P' =
      (Measure.map baseY P').map reindex := by
    have hEq : (fun ω => (fun i => X' ω (tests i), fun j => M' ω (U j))) = reindex ∘ baseY := by
      funext ω
      apply Prod.ext
      · funext i
        simp [reindex, baseY]
      · funext j
        simp only [reindex, baseY, Function.comp_apply, Equiv.apply_symm_apply]
        exact (hmassY ω j).symm
    rw [hEq]
    exact (AEMeasurable.map_map_of_aemeasurable hpost.aemeasurable hbaseYmeas).symm
  rw [hmapX, hbase, hmapY]

/-- The joint law of the distribution-valued field and its finite GMC is determined by the
finite-dimensional laws of test evaluations and open-set masses. -/
theorem equatorGFF_GMC_law_transport
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (P' : Measure Ω') (X' : Ω' → Distr) (hX' : IsEquatorGFF P' X')
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (M' : Ω' → Measure ℂ) (hM' : IsGMCOf P' X' γ M')
    (H : (TestFn → ℝ) → Measure ℂ → ℝ≥0∞)
    (hH : Measurable (fun q : (TestFn → ℝ) × Measure ℂ => H q.1 q.2)) :
    ∫⁻ ω, H (fun f => X ω f) (M ω) ∂P =
      ∫⁻ ω', H (fun f => X' ω' f) (M' ω') ∂P' := by
  classical
  rcases equatorGFF_GMC_measurable_version P X hX γ hγ hγ2 M hM with
    ⟨N, hNmeas, hNfinite, hNM⟩
  rcases equatorGFF_GMC_measurable_version P' X' hX' γ hγ hγ2 M' hM' with
    ⟨N', hN'meas, hN'finite, hN'M'⟩
  have hN : IsGMCOf P X γ N := by
    rcases hM with ⟨_, Xc, hXc, hconv⟩
    refine ⟨hNfinite, Xc, hXc, fun f => ?_⟩
    have hNM' : ∀ᵐ ω ∂P, N ω = M ω := hNM.mono fun _ h => h.symm
    exact tendstoInMeasure_integral_after_ae_measure_change
      (fun r ω => ∫ x, f x ∂regularizedGMC P Xc γ r ω) M N f hNM' (hconv f)
  have hN' : IsGMCOf P' X' γ N' := by
    rcases hM' with ⟨_, Xc, hXc, hconv⟩
    refine ⟨hN'finite, Xc, hXc, fun f => ?_⟩
    have hN'M'' : ∀ᵐ ω ∂P', N' ω = M' ω := hN'M'.mono fun _ h => h.symm
    exact tendstoInMeasure_integral_after_ae_measure_change
      (fun r ω => ∫ x, f x ∂regularizedGMC P' Xc γ r ω) M' N' f hN'M'' (hconv f)
  let Cfield : Set (Set (TestFn → ℝ)) :=
    measurableCylinders (fun _ : TestFn => ℝ)
  let Cmass : Set (Set (GMCOpen → ℝ≥0∞)) :=
    measurableCylinders (fun _ : GMCOpen => ℝ≥0∞)
  let Crect : Set (Set ((TestFn → ℝ) × (GMCOpen → ℝ≥0∞))) :=
    Set.image2 (· ×ˢ ·) Cfield Cmass
  let mTarget : MeasurableSpace ((TestFn → ℝ) × (GMCOpen → ℝ≥0∞)) :=
    MeasurableSpace.pi.prod MeasurableSpace.pi
  let mOutput : MeasurableSpace GMCTransportOutput :=
    mTarget.comap gmcOutputCode
  let : MeasurableSpace GMCTransportOutput := mOutput
  let outX : Ω → GMCTransportOutput := fun ω =>
    (fun f => X ω f, ⟨N ω, hNfinite ω⟩)
  let outY : Ω' → GMCTransportOutput := fun ω =>
    (fun f => X' ω f, ⟨N' ω, hN'finite ω⟩)
  have hCfield : MeasurableSpace.generateFrom Cfield = MeasurableSpace.pi := by
    exact generateFrom_measurableCylinders
  have hCmass : MeasurableSpace.generateFrom Cmass = MeasurableSpace.pi := by
    exact generateFrom_measurableCylinders
  have hCfieldSpan : IsCountablySpanning Cfield := by
    refine ⟨fun _ => Set.univ, ?_, ?_⟩
    · intro n
      change Set.univ ∈ measurableCylinders _
      exact univ_mem_measurableCylinders _
    · ext x
      simp
  have hCmassSpan : IsCountablySpanning Cmass := by
    refine ⟨fun _ => Set.univ, ?_, ?_⟩
    · intro n
      change Set.univ ∈ measurableCylinders _
      exact univ_mem_measurableCylinders _
    · ext x
      simp
  have hCrectGen : MeasurableSpace.generateFrom Crect = mTarget := by
    change MeasurableSpace.generateFrom (Set.image2 (· ×ˢ ·) Cfield Cmass) =
      MeasurableSpace.pi.prod MeasurableSpace.pi
    exact generateFrom_eq_prod hCfield hCmass hCfieldSpan hCmassSpan
  have hCrectPi : IsPiSystem Crect := by
    change IsPiSystem (Set.image2 (· ×ˢ ·) Cfield Cmass)
    exact isPiSystem_measurableCylinders.prod isPiSystem_measurableCylinders
  let Coutput : Set (Set GMCTransportOutput) :=
    Set.preimage gmcOutputCode '' Crect
  have hOutputGen : mOutput = MeasurableSpace.generateFrom Coutput := by
    dsimp [mOutput, Coutput]
    rw [← hCrectGen, MeasurableSpace.comap_generateFrom]
  have hOutputPi : IsPiSystem Coutput := by
    change IsPiSystem (Set.preimage gmcOutputCode '' Crect)
    intro A hA B hB hAB
    rcases hA with ⟨A', hA', rfl⟩
    rcases hB with ⟨B', hB', rfl⟩
    refine ⟨A' ∩ B', hCrectPi A' hA' B' hB' ?_, ?_⟩
    · rcases hAB with ⟨q, hq⟩
      exact ⟨gmcOutputCode q, by simpa [Set.preimage_inter] using hq⟩
    · rw [← Set.preimage_inter]
  have hcode : Measurable gmcOutputCode := Measurable.of_comap_le le_rfl
  have hcodeX : Measurable (gmcOutputCode ∘ outX) := by
    apply Measurable.prodMk
    · exact measurable_pi_iff.mpr fun f => (hX.2 f).1
    · apply measurable_pi_iff.mpr
      intro U
      exact (Measure.measurable_coe U.2.measurableSet).comp hNmeas
  have hcodeY : Measurable (gmcOutputCode ∘ outY) := by
    apply Measurable.prodMk
    · exact measurable_pi_iff.mpr fun f => (hX'.2 f).1
    · apply measurable_pi_iff.mpr
      intro U
      exact (Measure.measurable_coe U.2.measurableSet).comp hN'meas
  have houtX : Measurable outX := by
    rw [measurable_iff_comap_le]
    change mOutput.comap outX ≤ ‹MeasurableSpace Ω›
    rw [show mOutput = mTarget.comap gmcOutputCode by rfl,
      MeasurableSpace.comap_comp]
    exact hcodeX.comap_le
  have houtY : Measurable outY := by
    rw [measurable_iff_comap_le]
    change mOutput.comap outY ≤ ‹MeasurableSpace Ω'›
    rw [show mOutput = mTarget.comap gmcOutputCode by rfl,
      MeasurableSpace.comap_comp]
    exact hcodeY.comap_le
  let forget : GMCTransportOutput → (TestFn → ℝ) × Measure ℂ :=
    fun q => (q.1, q.2.1)
  have hOpenGen : (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom
      {s : Set ℂ | IsOpen s} := by
    calc
      (inferInstance : MeasurableSpace ℂ) = borel ℂ := BorelSpace.measurable_eq
      _ = MeasurableSpace.generateFrom {s : Set ℂ | IsOpen s} :=
        borel_eq_generateFrom_of_subbasis
          (TopologicalSpace.generateFrom_setOfPred_isOpen (inferInstance : TopologicalSpace ℂ)).symm
  have hforgetMeasure : Measurable (fun q : GMCTransportOutput => (q.2.1 : Measure ℂ)) := by
    let : ∀ q : GMCTransportOutput, IsFiniteMeasure q.2.1 := fun q => q.2.2
    apply Measurable.measure_of_isPiSystem hOpenGen isPiSystem_isOpen
    · intro s hs
      have heval : Measurable (fun q : GMCTransportOutput =>
          (gmcOutputCode q).2 ⟨s, hs⟩) := by
        have h := (measurable_pi_iff.mp (measurable_snd.comp hcode)) ⟨s, hs⟩
        exact h
      simpa [gmcOutputCode] using heval
    · have heval : Measurable (fun q : GMCTransportOutput =>
          (gmcOutputCode q).2 ⟨Set.univ, isOpen_univ⟩) := by
        have h := (measurable_pi_iff.mp (measurable_snd.comp hcode))
          ⟨Set.univ, isOpen_univ⟩
        exact h
      simpa [gmcOutputCode] using heval
  have hforget : Measurable forget := by
    apply Measurable.prodMk
    · change Measurable (fun q : GMCTransportOutput => (gmcOutputCode q).1)
      exact measurable_fst.comp hcode
    · exact hforgetMeasure
  have hHout : Measurable (fun q : GMCTransportOutput => H q.1 q.2.1) := by
    exact hH.comp hforget
  have hLaw : Measure.map outX P = Measure.map outY P' := by
    let : IsProbabilityMeasure P := hX.1
    let : IsProbabilityMeasure P' := hX'.1
    apply MeasureTheory.ext_of_generate_finite Coutput hOutputGen hOutputPi
    · intro S hS
      rcases hS with ⟨R, hR, rfl⟩
      rcases hR with ⟨A, hA, B, hB, rfl⟩
      rcases (mem_measurableCylinders A).1 hA with ⟨s, As, hAs, rfl⟩
      rcases (mem_measurableCylinders B).1 hB with ⟨t, Bs, hBs, rfl⟩
      let vX : Ω → (s → ℝ) × (t → ℝ≥0∞) := fun ω =>
        (fun i => X ω i.1, fun j => N ω j.1.1)
      let vY : Ω' → (s → ℝ) × (t → ℝ≥0∞) := fun ω =>
        (fun i => X' ω i.1, fun j => N' ω j.1.1)
      have hv : Measure.map vX P = Measure.map vY P' :=
        equatorGFF_GMC_open_mass_test_fintype_law P X hX P' X' hX' γ N hN N' hN'
          (fun i : s => i.1) (fun j : t => j.1.1) (fun j => j.1.2)
      have hvXmeas : AEMeasurable vX P := by
        change AEMeasurable (fun ω =>
          (fun i : s => X ω (i : TestFn), fun j : t => N ω j.1.1)) P
        apply (measurable_pi_iff.mpr fun i : s => (hX.2 (i : TestFn)).1).aemeasurable.prodMk
        apply AEMeasurable.of_eval
        intro j
        exact gmc_open_mass_aemeasurable P X hX γ N hN j.1.1 j.1.2
      have hvYmeas : AEMeasurable vY P' := by
        change AEMeasurable (fun ω =>
          (fun i : s => X' ω (i : TestFn), fun j : t => N' ω j.1.1)) P'
        apply (measurable_pi_iff.mpr fun i : s => (hX'.2 (i : TestFn)).1).aemeasurable.prodMk
        apply AEMeasurable.of_eval
        intro j
        exact gmc_open_mass_aemeasurable P' X' hX' γ N' hN' j.1.1 j.1.2
      have hAB : MeasurableSet (As ×ˢ Bs) := hAs.prod hBs
      have hprob : P (vX ⁻¹' (As ×ˢ Bs)) = P' (vY ⁻¹' (As ×ˢ Bs)) := by
        have h := congrArg (fun μ : Measure ((s → ℝ) × (t → ℝ≥0∞)) => μ (As ×ˢ Bs)) hv
        rw [Measure.map_apply_of_aemeasurable hvXmeas hAB,
          Measure.map_apply_of_aemeasurable hvYmeas hAB] at h
        exact h
      have hSmeas : @MeasurableSet GMCTransportOutput mOutput
          (gmcOutputCode ⁻¹' (cylinder s As ×ˢ cylinder t Bs)) := by
        have hCA : cylinder s As ∈ Cfield := by
          change cylinder s As ∈ measurableCylinders (fun _ : TestFn => ℝ)
          exact cylinder_mem_measurableCylinders
            (α := fun _ : TestFn => ℝ) s As hAs
        have hCB : cylinder t Bs ∈ Cmass := by
          change cylinder t Bs ∈ measurableCylinders (fun _ : GMCOpen => ℝ≥0∞)
          exact cylinder_mem_measurableCylinders
            (α := fun _ : GMCOpen => ℝ≥0∞) t Bs hBs
        have hSmem : gmcOutputCode ⁻¹' (cylinder s As ×ˢ cylinder t Bs) ∈ Coutput :=
          ⟨cylinder s As ×ˢ cylinder t Bs,
            Set.mem_image2_of_mem hCA hCB, rfl⟩
        rw [hOutputGen]
        exact MeasurableSpace.measurableSet_generateFrom hSmem
      have hpreX : outX ⁻¹' (gmcOutputCode ⁻¹'
          (cylinder s As ×ˢ cylinder t Bs)) = vX ⁻¹' (As ×ˢ Bs) := by
        ext ω
        have hsrestrict : s.restrict (fun f => X ω f) = fun i : s => X ω i.1 := by
          funext i
          rfl
        have htrestrict : t.restrict (fun U : GMCOpen => N ω U.1) =
            fun j : t => N ω j.1.1 := by
          funext j
          rfl
        simp [outX, gmcOutputCode, vX, cylinder, hsrestrict, htrestrict]
      have hpreY : outY ⁻¹' (gmcOutputCode ⁻¹'
          (cylinder s As ×ˢ cylinder t Bs)) = vY ⁻¹' (As ×ˢ Bs) := by
        ext ω
        have hsrestrict : s.restrict (fun f => X' ω f) = fun i : s => X' ω i.1 := by
          funext i
          rfl
        have htrestrict : t.restrict (fun U : GMCOpen => N' ω U.1) =
            fun j : t => N' ω j.1.1 := by
          funext j
          rfl
        simp [outY, gmcOutputCode, vY, cylinder, hsrestrict, htrestrict]
      calc
        (Measure.map outX P) (gmcOutputCode ⁻¹'
            (cylinder s As ×ˢ cylinder t Bs)) = P (vX ⁻¹' (As ×ˢ Bs)) := by
          rw [Measure.map_apply houtX hSmeas, hpreX]
        _ = P' (vY ⁻¹' (As ×ˢ Bs)) := hprob
        _ = (Measure.map outY P') (gmcOutputCode ⁻¹'
            (cylinder s As ×ˢ cylinder t Bs)) := by
          rw [Measure.map_apply houtY hSmeas, hpreY]
    · simp [Measure.map_apply houtX MeasurableSet.univ,
        Measure.map_apply houtY MeasurableSet.univ, hX.1.measure_univ,
        hX'.1.measure_univ]
  calc
    ∫⁻ ω, H (fun f => X ω f) (M ω) ∂P =
        ∫⁻ ω, H (fun f => X ω f) (N ω) ∂P := by
          apply lintegral_congr_ae
          filter_upwards [hNM] with ω hω
          rw [hω]
    _ = ∫⁻ q, H q.1 q.2.1 ∂(Measure.map outX P) := by
      symm
      rw [lintegral_map hHout houtX]
    _ = ∫⁻ q, H q.1 q.2.1 ∂(Measure.map outY P') := by rw [hLaw]
    _ = ∫⁻ ω', H (fun f => X' ω' f) (N' ω') ∂P' := by
      rw [lintegral_map hHout houtY]
    _ = ∫⁻ ω', H (fun f => X' ω' f) (M' ω') ∂P' := by
      apply lintegral_congr_ae
      filter_upwards [hN'M'] with ω hω
      rw [hω]


end DOZZ.Proofs

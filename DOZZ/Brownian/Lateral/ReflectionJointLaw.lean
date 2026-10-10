/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Brownian.Lateral.ConcentricInversion
public import DOZZ.Brownian.Lateral.LawUniqueness
public import DOZZ.GMC.Moments.InversionAnnularTestLaw
@[expose] public section
open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology Distributions ENNReal NNReal
namespace DOZZ.Proofs

/-- Annular inversion of the actual GMC retains its joint law with the reversed
concentric source coordinates. -/
theorem gmc_inversion_annular_joint_test_vector_law
    {Ω : Type*} [MeasurableSpace Ω] {k l : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (U : Set ℂ) (hUopen : IsOpen U) {m R : ℝ} (hm : 0 < m) (hR : 0 ≤ R)
    (hU : ∀ x ∈ U, 2 * m ≤ ‖x‖ ∧ ‖x‖ ≤ R)
    (s : Fin l → ℝ) (f : Fin k → BoundedContinuousFunction ℂ ℝ)
    (hfc : ∀ j, HasCompactSupport (f j : ℂ → ℝ))
    (hfU : ∀ j, tsupport (f j : ℂ → ℝ) ⊆ U) :
    P.map (fun ω => (fun i => Xc ω 0 (-s i), fun j => ∫ x, f j x ∂(M ω).map
      (fun z : ℂ => z⁻¹))) =
      P.map (fun ω => (fun i => Xc ω 0 (s i), fun j => ∫ x, f j x ∂M ω)) := by
  let : IsProbabilityMeasure P := hX.1
  obtain ⟨g, hg, Z, N, hgap, hmem, hlim, hZ, hN, hNae⟩ :=
    isGMCOf_inversion_annular_version P X hX γ hγ hγ2 M hM Xc hc U hUopen hm hR hU
  obtain ⟨A, hA, _hAfin, hAae⟩ :=
    isGMCOf_restrict_admissible_version P X hX γ hγ hγ2 M hM Xc hc U hUopen
  have hY := isCircleAverage_admissible P X hX Xc hc U hUopen
  let : IsFiniteMeasure gmcReferenceMeasure := ⟨lt_top_iff_ne_top.mpr gmcReferenceMeasure_univ_ne_top⟩
  have href : logRegularizationReference U (fun x => normPlus x ^ (-4 : ℝ)) =
      gmcReferenceMeasure.restrict U := by
    rw [logRegularizationReference_restrict_of_subset univ U
      (fun x => normPlus x ^ (-4 : ℝ)) hUopen.measurableSet (subset_univ _)]
    simp only [logRegularizationReference, Measure.restrict_univ, gmcReferenceMeasure]
  let : IsFiniteMeasure (logRegularizationReference U (fun x => normPlus x ^ (-4 : ℝ))) := by
    rw [href]; infer_instance
  let V := fun ω i => Xc ω 0 (-s i)
  let V' := fun ω i => Xc ω 0 (s i)
  have hV : Measurable V := measurable_pi_iff.mpr fun i =>
    (hc.1 (-s i)).comp (measurable_id.prodMk measurable_const)
  have hV' : Measurable V' := measurable_pi_iff.mpr fun i =>
    (hc.1 (s i)).comp (measurable_id.prodMk measurable_const)
  have hfdd ε (_hε : 0 < ε) (_hεb : ε ≤ min (min (m / 2) 1) 1) n (xs : Fin n → ℂ) :
      P.map (fun ω => (V ω, fun i => Z ω (xs i) (Real.log (1 / ε)))) =
      P.map (fun ω => (V' ω, fun i => Xc ω (xs i) (Real.log (1 / ε)))) :=
    inversionCircle_radial_joint_fdd_law P X Xc hX hc Z g hg hgap hmem hlim
      s (fun i => (xs i, Real.log (1 / ε)))
  have hlaw := admissibleLogChaos_limit_joint_vector_law_of_fdd P P U
    (fun x => normPlus x ^ (-4 : ℝ)) (min (m / 2) 1) 1
    (fun ω ε x => Z ω x (Real.log (1 / ε)))
    (fun ω ε x => Xc ω x (Real.log (1 / ε))) hZ hY γ N A hN hA V V' hV hV' hfdd f hfc hfU
  have heq (μ : Measure ℂ) (j : Fin k) : ∫ x, f j x ∂μ.restrict U = ∫ x, f j x ∂μ :=
    integral_restrict_eq_integral_of_zero_on_compl μ U hUopen.measurableSet (f j)
      (boundedContinuousFunction_eq_zero_off_tsupport_subset (f j) U (hfU j))
  have hleft : (fun ω => (V ω, fun j => ∫ x, f j x ∂N ω)) =ᵐ[P]
      fun ω => (V ω, fun j => ∫ x, f j x ∂(M ω).map (fun z : ℂ => z⁻¹)) := by
    filter_upwards [hNae] with ω hω
    apply Prod.ext
    · rfl
    · funext j
      change (∫ x, f j x ∂N ω) = ∫ x, f j x ∂(M ω).map (fun z : ℂ => z⁻¹)
      rw [hω, heq]
  have hright : (fun ω => (V' ω, fun j => ∫ x, f j x ∂A ω)) =ᵐ[P]
      fun ω => (V' ω, fun j => ∫ x, f j x ∂M ω) := by
    filter_upwards [hAae] with ω hω
    apply Prod.ext
    · rfl
    · funext j
      change (∫ x, f j x ∂A ω) = ∫ x, f j x ∂M ω
      rw [← hω, heq]
  exact (Measure.map_congr hleft).symm.trans (hlaw.trans (Measure.map_congr hright))

/-- Full bounded test-vector inversion law jointly with the reversed radial coordinates.
Compact annular cutoffs exhaust the plane outside its zero atom. -/
theorem gmc_inversion_joint_test_vector_law
    {Ω : Type*} [MeasurableSpace Ω] {k l : ℕ}
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (s : Fin l → ℝ) (f : Fin k → BoundedContinuousFunction ℂ ℝ) :
    P.map (fun ω => (fun i => Xc ω 0 (-s i), fun j => ∫ x, f j x ∂(M ω).map
      (fun z : ℂ => z⁻¹))) =
      P.map (fun ω => (fun i => Xc ω 0 (s i), fun j => ∫ x, f j x ∂M ω)) := by
  let : IsProbabilityMeasure P := hX.1
  let N := fun ω => (M ω).map (fun z : ℂ => z⁻¹)
  have hMm := equatorGFF_GMC_aemeasurable P X hX γ hγ hγ2 M hM
  have hNm : AEMeasurable N P := (Measure.measurable_map _ measurable_inv).comp_aemeasurable hMm
  have hNfin : ∀ ω, IsFiniteMeasure (N ω) := fun ω => by let := hM.1 ω; infer_instance
  let q := fun n j => f j * gmcInversionCutoff n
  have hqm n j := finiteMeasure_bcf_integral_aemeasurable P M hMm hM.1 (q n j)
  have hqn n j := finiteMeasure_bcf_integral_aemeasurable P N hNm hNfin (q n j)
  have hzero := gmc_atomless_at_zero_of_isGMCOf P X hX γ hγ hγ2 M hM
  have hNzero : ∀ᵐ ω ∂P, N ω {0} = 0 := by
    filter_upwards [hzero] with ω hω
    change (M ω).map (fun z : ℂ => z⁻¹) {0} = 0
    rw [Measure.map_apply measurable_inv (measurableSet_singleton 0)]
    simpa only [preimage, mem_singleton_iff, inv_eq_zero, ofPred_eq_eq_singleton] using hω
  have hV : AEMeasurable (fun ω i => Xc ω 0 (-s i)) P :=
    AEMeasurable.of_eval fun _ => (hc.2.1 _ _).aemeasurable
  have hV' : AEMeasurable (fun ω i => Xc ω 0 (s i)) P :=
    AEMeasurable.of_eval fun _ => (hc.2.1 _ _).aemeasurable
  apply gmc_limit_joint_test_vector_law _ _ hV hV'
    (fun n ω j => ∫ x, q n j x ∂N ω) (fun n ω j => ∫ x, q n j x ∂M ω)
    (fun ω j => ∫ x, f j x ∂N ω) (fun ω j => ∫ x, f j x ∂M ω)
  · exact fun n => AEMeasurable.of_eval (hqn n)
  · exact fun n => AEMeasurable.of_eval (hqm n)
  · exact AEMeasurable.of_eval fun j => finiteMeasure_bcf_integral_aemeasurable P N hNm hNfin (f j)
  · exact AEMeasurable.of_eval fun j => finiteMeasure_bcf_integral_aemeasurable P M hMm hM.1 (f j)
  · intro n
    let U := {x : ℂ | 1 / (2 * ((n : ℝ) + 2)) < ‖x‖ ∧ ‖x‖ < (n : ℝ) + 3}
    apply gmc_inversion_annular_joint_test_vector_law P X hX Xc hc γ hγ hγ2 M hM U
      (isOpen_lt continuous_const continuous_norm |>.inter
        (isOpen_lt continuous_norm continuous_const))
      (m := 1 / (4 * ((n : ℝ) + 2))) (R := (n : ℝ) + 3)
      (by positivity) (by positivity)
    · intro x hx
      constructor
      · have he : 2 * (1 / (4 * ((n : ℝ) + 2))) = 1 / (2 * ((n : ℝ) + 2)) := by
          field_simp; norm_num
        rw [he]; exact hx.1.le
      · exact hx.2.le
    · exact fun j => (gmcInversionCutoff_test_annular n (f j)).1
    · exact fun j => (gmcInversionCutoff_test_annular n (f j)).2
  · intro j
    apply tendstoInMeasure_of_tendsto_ae (fun n => (hqn n j).aestronglyMeasurable)
    filter_upwards [hNzero] with ω hω
    let := hNfin ω
    exact inversion_cutoff_integral_tendsto (N ω) hω (f j)
  · intro j
    apply tendstoInMeasure_of_tendsto_ae (fun n => (hqm n j).aestronglyMeasurable)
    filter_upwards [hzero] with ω hω
    let := hM.1 ω
    exact inversion_cutoff_integral_tendsto (M ω) hω (f j)

private abbrev RadialReflectionOpen := {U : Set ℂ // IsOpen U}
private abbrev RadialReflectionOutput := TwoSidedPath × FiniteMeasure ℂ
private noncomputable def radialReflectionOutputCode (q : RadialReflectionOutput) :
    (ℚ → ℝ) × (RadialReflectionOpen → ℝ≥0∞) :=
  (radialRationalCode q.1, fun U => (q.2 : Measure ℂ) U.1)

/-- Finite radial evaluations and open masses determine the joint law of an ENTIRE
continuous radial path and finite random measure. Null-event measurability suffices. -/
theorem finite_random_radial_measure_law_of_open_fdd
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A B : Ω → TwoSidedPath) (hA : AEMeasurable A P) (hB : AEMeasurable B P)
    (M N : Ω → Measure ℂ) (hM : AEMeasurable M P) (hN : AEMeasurable N P)
    (hMf : ∀ ω, IsFiniteMeasure (M ω)) (hNf : ∀ ω, IsFiniteMeasure (N ω))
    (hfdd : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (s : ι → ℚ)
      (U : κ → Set ℂ), (∀ j, IsOpen (U j)) →
      P.map (fun ω => (fun i => A ω (s i : ℝ), fun j => M ω (U j))) =
      P.map (fun ω => (fun i => B ω (s i : ℝ), fun j => N ω (U j)))) :
    P.map (β := TwoSidedPath × FiniteMeasure ℂ) (fun ω => (A ω, (⟨M ω, hMf ω⟩ : FiniteMeasure ℂ))) =
      P.map (β := TwoSidedPath × FiniteMeasure ℂ) (fun ω => (B ω, (⟨N ω, hNf ω⟩ : FiniteMeasure ℂ))) := by
  classical
  let outM : Ω → RadialReflectionOutput := fun ω => (A ω, ⟨M ω, hMf ω⟩)
  let outN : Ω → RadialReflectionOutput := fun ω => (B ω, ⟨N ω, hNf ω⟩)
  let mStd : MeasurableSpace RadialReflectionOutput := inferInstance
  have homStd : AEMeasurable outM P := hA.prodMk
    (@AEMeasurable.subtype_mk Ω (Measure ℂ) _ _ M P hM _ hMf)
  have honStd : AEMeasurable outN P := hB.prodMk
    (@AEMeasurable.subtype_mk Ω (Measure ℂ) _ _ N P hN _ hNf)
  have hcodeStd : Measurable radialReflectionOutputCode :=
    (measurable_radialRationalCode.comp measurable_fst).prodMk
      (measurable_pi_iff.mpr fun U => (Measure.measurable_coe U.2.measurableSet).comp
        (measurable_subtype_coe.comp measurable_snd))
  let mTarget : MeasurableSpace ((ℚ → ℝ) × (RadialReflectionOpen → ℝ≥0∞)) := inferInstance
  let mOutput := mTarget.comap radialReflectionOutputCode
  let : MeasurableSpace RadialReflectionOutput := mOutput
  have hto : @Measurable RadialReflectionOutput RadialReflectionOutput mStd mOutput id := by
    rw [measurable_iff_comap_le, MeasurableSpace.comap_id]
    exact hcodeStd.comap_le
  have hom : AEMeasurable outM P := @Measurable.comp_aemeasurable Ω
    RadialReflectionOutput RadialReflectionOutput _ mOutput P mStd outM id hto homStd
  have hon : AEMeasurable outN P := @Measurable.comp_aemeasurable Ω
    RadialReflectionOutput RadialReflectionOutput _ mOutput P mStd outN id hto honStd
  let Cr := measurableCylinders (fun _ : ℚ => ℝ)
  let Cm := measurableCylinders (fun _ : RadialReflectionOpen => ℝ≥0∞)
  let Crect := Set.image2 (· ×ˢ ·) Cr Cm
  have hrgen : MeasurableSpace.generateFrom Cr = MeasurableSpace.pi := generateFrom_measurableCylinders
  have hmgen : MeasurableSpace.generateFrom Cm = MeasurableSpace.pi := generateFrom_measurableCylinders
  have hrspan : IsCountablySpanning Cr := by
    refine ⟨fun _ => univ, fun _ => univ_mem_measurableCylinders _, ?_⟩
    ext x; simp
  have hmspan : IsCountablySpanning Cm := by
    refine ⟨fun _ => univ, fun _ => univ_mem_measurableCylinders _, ?_⟩
    ext x; simp
  have hrectgen : MeasurableSpace.generateFrom Crect = mTarget :=
    generateFrom_eq_prod hrgen hmgen hrspan hmspan
  have hrectpi : IsPiSystem Crect := isPiSystem_measurableCylinders.prod isPiSystem_measurableCylinders
  let Cout := Set.preimage radialReflectionOutputCode '' Crect
  have hgen : mOutput = MeasurableSpace.generateFrom Cout := by
    dsimp only [mOutput, Cout]
    rw [← hrectgen, MeasurableSpace.comap_generateFrom]
  have hpi : IsPiSystem Cout := by
    intro S hS T hT hST
    rcases hS with ⟨S', hS', rfl⟩
    rcases hT with ⟨T', hT', rfl⟩
    refine ⟨S' ∩ T', hrectpi S' hS' T' hT' ?_, ?_⟩
    · rcases hST with ⟨q, hq⟩
      exact ⟨radialReflectionOutputCode q, hq⟩
    · rw [← Set.preimage_inter]
  have hcode : Measurable radialReflectionOutputCode := Measurable.of_comap_le le_rfl
  have hOpenGen : (inferInstance : MeasurableSpace ℂ) =
      MeasurableSpace.generateFrom {S : Set ℂ | IsOpen S} := by
    calc
      (inferInstance : MeasurableSpace ℂ) = borel ℂ := BorelSpace.measurable_eq
      _ = _ := borel_eq_generateFrom_of_subbasis
        (TopologicalSpace.generateFrom_setOfPred_isOpen (inferInstance : TopologicalSpace ℂ)).symm
  have hforgetM : Measurable (fun q : RadialReflectionOutput => (q.2 : Measure ℂ)) := by
    let : ∀ q : RadialReflectionOutput, IsFiniteMeasure (q.2 : Measure ℂ) := fun q => q.2.2
    apply Measurable.measure_of_isPiSystem hOpenGen isPiSystem_isOpen
    · intro S hS
      change IsOpen S at hS
      simpa only [Function.comp_apply, radialReflectionOutputCode] using
        (measurable_pi_iff.mp (measurable_snd.comp hcode)) ⟨S, hS⟩
    · simpa only [Function.comp_apply, radialReflectionOutputCode] using
        (measurable_pi_iff.mp (measurable_snd.comp hcode)) ⟨univ, isOpen_univ⟩
  have hforgetA : Measurable (fun q : RadialReflectionOutput => q.1) := by
    have h := measurable_radialPathFromRationalCode.comp (measurable_fst.comp hcode)
    change Measurable (fun q : RadialReflectionOutput =>
      radialPathFromRationalCode (radialRationalCode q.1)) at h
    simpa only [radialPathFromRationalCode_code] using h
  have hforget : @Measurable RadialReflectionOutput RadialReflectionOutput mOutput mStd id :=
    hforgetA.prodMk hforgetM.subtype_mk
  have hLaw : P.map outM = P.map outN := by
    apply MeasureTheory.ext_of_generate_finite Cout hgen hpi
    · intro S hS
      rcases hS with ⟨R, hR, rfl⟩
      rcases hR with ⟨Ar, hAr, Am, hAm, rfl⟩
      rcases (mem_measurableCylinders Ar).mp hAr with ⟨sr, Br, hBr, rfl⟩
      rcases (mem_measurableCylinders Am).mp hAm with ⟨sm, Bm, hBm, rfl⟩
      let vm := fun ω => (fun i : sr => A ω (i.1 : ℝ), fun j : sm => M ω j.1.1)
      let vn := fun ω => (fun i : sr => B ω (i.1 : ℝ), fun j : sm => N ω j.1.1)
      have hm : AEMeasurable vm P :=
        (AEMeasurable.of_eval fun i => (ContinuousMap.measurable_eval _).comp_aemeasurable hA).prodMk
          (AEMeasurable.of_eval fun j =>
            (Measure.measurable_coe j.1.2.measurableSet).comp_aemeasurable hM)
      have hn : AEMeasurable vn P :=
        (AEMeasurable.of_eval fun i => (ContinuousMap.measurable_eval _).comp_aemeasurable hB).prodMk
          (AEMeasurable.of_eval fun j =>
            (Measure.measurable_coe j.1.2.measurableSet).comp_aemeasurable hN)
      have hv := hfdd sr sm (fun i => i.1) (fun j => j.1.1) (fun j => j.1.2)
      have hp : P (vm ⁻¹' (Br ×ˢ Bm)) = P (vn ⁻¹' (Br ×ˢ Bm)) := by
        have h := congrArg (fun μ => μ (Br ×ˢ Bm)) hv
        rw [Measure.map_apply_of_aemeasurable hm (hBr.prod hBm),
          Measure.map_apply_of_aemeasurable hn (hBr.prod hBm)] at h
        exact h
      have hs : MeasurableSet (radialReflectionOutputCode ⁻¹'
          (cylinder sr Br ×ˢ cylinder sm Bm)) := by
        apply hcode
        rw [← hrectgen]
        apply MeasurableSpace.measurableSet_generateFrom
        exact Set.mem_image2_of_mem
          (cylinder_mem_measurableCylinders (α := fun _ : ℚ => ℝ) sr Br hBr)
          (cylinder_mem_measurableCylinders (α := fun _ : RadialReflectionOpen => ℝ≥0∞) sm Bm hBm)
      rw [Measure.map_apply_of_aemeasurable hom hs, Measure.map_apply_of_aemeasurable hon hs]
      exact hp
    · simp only [Measure.map_apply_of_aemeasurable hom MeasurableSet.univ,
        Measure.map_apply_of_aemeasurable hon MeasurableSet.univ, preimage_univ]
  have h := congrArg (fun μ => @Measure.map RadialReflectionOutput RadialReflectionOutput
    mOutput mStd id μ) hLaw
  have hfm := @Measurable.aemeasurable RadialReflectionOutput RadialReflectionOutput
    mOutput mStd id (P.map outM) hforget
  have hfn := @Measurable.aemeasurable RadialReflectionOutput RadialReflectionOutput
    mOutput mStd id (P.map outN) hforget
  have heM := @AEMeasurable.map_map_of_aemeasurable Ω RadialReflectionOutput
    RadialReflectionOutput _ mOutput mStd P id outM hfm hom
  have heN := @AEMeasurable.map_map_of_aemeasurable Ω RadialReflectionOutput
    RadialReflectionOutput _ mOutput mStd P id outN hfn hon
  rw [heM, heN] at h
  simpa only [Function.comp_def, id, outM, outN] using h

/-- Inversion preserves finite vectors of open masses jointly with reversed radial
coordinates, on the original probability space. -/
theorem gmc_inversion_joint_open_mass_fintype_law
    {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype κ]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (s : ι → ℝ) (U : κ → Set ℂ) (hU : ∀ j, IsOpen (U j)) :
    P.map (fun ω => (fun i => Xc ω 0 (-s i), fun j => (M ω).map
      (fun z : ℂ => z⁻¹) (U j))) =
      P.map (fun ω => (fun i => Xc ω 0 (s i), fun j => M ω (U j))) := by
  classical
  let : IsProbabilityMeasure P := hX.1
  let eι : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let eκ : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  let N := fun ω => (M ω).map (fun z : ℂ => z⁻¹)
  have hMm := equatorGFF_GMC_aemeasurable P X hX γ hγ hγ2 M hM
  have hNm : AEMeasurable N P := (Measure.measurable_map _ measurable_inv).comp_aemeasurable hMm
  have hNfin : ∀ ω, IsFiniteMeasure (N ω) := fun ω => by let := hM.1 ω; infer_instance
  let V := fun ω i => Xc ω 0 (-s (eι i))
  let V' := fun ω i => Xc ω 0 (s (eι i))
  have hV : AEMeasurable V P := AEMeasurable.of_eval fun _ => (hc.2.1 _ _).aemeasurable
  have hV' : AEMeasurable V' P := AEMeasurable.of_eval fun _ => (hc.2.1 _ _).aemeasurable
  let q := fun n j => gmcOpenApprox (U (eκ j)) (hU (eκ j)) n
  let A := fun ω (j : Fin (Fintype.card κ)) => (N ω (U (eκ j))).toReal
  let B := fun ω (j : Fin (Fintype.card κ)) => (M ω (U (eκ j))).toReal
  have hA : AEMeasurable A P := AEMeasurable.of_eval fun j =>
    ((Measure.measurable_coe (hU (eκ j)).measurableSet).comp_aemeasurable hNm).ennreal_toReal
  have hB : AEMeasurable B P := AEMeasurable.of_eval fun j =>
    ((Measure.measurable_coe (hU (eκ j)).measurableSet).comp_aemeasurable hMm).ennreal_toReal
  have hqn n j := finiteMeasure_bcf_integral_aemeasurable P N hNm hNfin (q n j)
  have hqm n j := finiteMeasure_bcf_integral_aemeasurable P M hMm hM.1 (q n j)
  have hlaw : P.map (fun ω => (V ω, A ω)) = P.map (fun ω => (V' ω, B ω)) := by
    apply gmc_limit_joint_test_vector_law V V' hV hV'
      (fun n ω j => ∫ x, q n j x ∂N ω) (fun n ω j => ∫ x, q n j x ∂M ω) A B
    · exact fun n => AEMeasurable.of_eval (hqn n)
    · exact fun n => AEMeasurable.of_eval (hqm n)
    · exact hA
    · exact hB
    · intro n
      exact gmc_inversion_joint_test_vector_law P X hX Xc hc γ hγ hγ2 M hM (s ∘ eι) (q n)
    · intro j
      apply tendstoInMeasure_of_tendsto_ae (fun n => (hqn n j).aestronglyMeasurable)
      exact ae_of_all _ fun ω => by
        let := hNfin ω
        exact gmcOpenApprox_integral_tendsto (N ω) (U (eκ j)) (hU (eκ j))
    · intro j
      apply tendstoInMeasure_of_tendsto_ae (fun n => (hqm n j).aestronglyMeasurable)
      exact ae_of_all _ fun ω => by
        let := hM.1 ω
        exact gmcOpenApprox_integral_tendsto (M ω) (U (eκ j)) (hU (eκ j))
  let post := fun v : (Fin (Fintype.card ι) → ℝ) × (Fin (Fintype.card κ) → ℝ) =>
    (fun i : ι => v.1 (eι.symm i), fun j : κ => ENNReal.ofReal (v.2 (eκ.symm j)))
  have hp : Measurable post := by fun_prop
  have heA : post ∘ (fun ω => (V ω, A ω)) =
      fun ω => (fun i => Xc ω 0 (-s i), fun j => N ω (U j)) := by
    funext ω
    apply Prod.ext
    · funext i; simp only [post, V, Function.comp_apply, Equiv.apply_symm_apply]
    · funext j
      simp only [post, A, Function.comp_apply, Equiv.apply_symm_apply]
      let := hNfin ω
      exact ENNReal.ofReal_toReal (measure_ne_top _ _)
  have heB : post ∘ (fun ω => (V' ω, B ω)) =
      fun ω => (fun i => Xc ω 0 (s i), fun j => M ω (U j)) := by
    funext ω
    apply Prod.ext
    · funext i; simp only [post, V', Function.comp_apply, Equiv.apply_symm_apply]
    · funext j
      simp only [post, B, Function.comp_apply, Equiv.apply_symm_apply]
      let := hM.1 ω
      exact ENNReal.ofReal_toReal (measure_ne_top _ _)
  calc
    _ = (P.map (fun ω => (V ω, A ω))).map post := by
      rw [AEMeasurable.map_map_of_aemeasurable hp.aemeasurable (hV.prodMk hA), heA]
    _ = (P.map (fun ω => (V' ω, B ω))).map post := congrArg (Measure.map post) hlaw
    _ = _ := by
      rw [AEMeasurable.map_map_of_aemeasurable hp.aemeasurable (hV'.prodMk hB), heB]

/-- The entire radial path and the actual finite GMC have the simultaneous
radial-reversal/complex-inversion joint law. -/
theorem originRadialGMC_inversion_joint_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) :
    P.map (β := TwoSidedPath × FiniteMeasure ℂ) (fun ω => (originReversedRadialPath (originRadialPath Xc ω),
      FiniteMeasure.map (⟨M ω, hM.1 ω⟩ : FiniteMeasure ℂ) (fun x : ℂ => x⁻¹))) =
    P.map (β := TwoSidedPath × FiniteMeasure ℂ) (fun ω => (originRadialPath Xc ω, (⟨M ω, hM.1 ω⟩ : FiniteMeasure ℂ))) := by
  let : IsProbabilityMeasure P := hX.1
  let A := originRadialPath Xc
  let N := fun ω => (M ω).map (fun x : ℂ => x⁻¹)
  have hMm := equatorGFF_GMC_aemeasurable P X hX γ hγ hγ2 M hM
  have hNm : AEMeasurable N P := (Measure.measurable_map _ measurable_inv).comp_aemeasurable hMm
  have hNf : ∀ ω, IsFiniteMeasure (N ω) := fun ω =>
    (FiniteMeasure.map (⟨M ω, hM.1 ω⟩ : FiniteMeasure ℂ) (fun x : ℂ => x⁻¹)).2
  have hA := originRadialPath_aemeasurable P X Xc hc hcont
  have hAr := originReversedRadialPath_aemeasurable P A hA
  apply finite_random_radial_measure_law_of_open_fdd P
    (fun ω => originReversedRadialPath (A ω)) A hAr hA N M hNm hMm hNf hM.1
  intro ι κ _ _ s U hU
  have hlaw := gmc_inversion_joint_open_mass_fintype_law P X hX Xc hc γ hγ hγ2 M hM
    (fun i => (s i : ℝ)) U hU
  calc
    _ = P.map (fun ω => (fun i => Xc ω 0 (-(s i : ℝ)), fun j => N ω (U j))) := by
      apply Measure.map_congr
      filter_upwards [originRadialPath_eval_ae hcont] with ω hω
      apply Prod.ext
      · funext i
        exact hω (-(s i : ℝ))
      · rfl
    _ = P.map (fun ω => (fun i => Xc ω 0 (s i : ℝ), fun j => M ω (U j))) := hlaw
    _ = _ := by
      apply Measure.map_congr
      filter_upwards [originRadialPath_eval_ae hcont] with ω hω
      apply Prod.ext
      · funext i
        exact (hω (s i : ℝ)).symm
      · rfl

/-- Reflection preserves the law of the ENTIRE actual polar projection
`DOZZ.lateralProjectedGMC`. Its proof uses simultaneous radial/GMC inversion,
retaining their source coupling. -/
theorem lateralProjectedGMC_reflection_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) :
    P.map (fun ω => (lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)).map
      (fun s : ℝ => -s)) =
    P.map (fun ω => lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)) := by
  let T : TwoSidedPath × FiniteMeasure ℂ → Measure ℝ := fun q =>
    lateralProjectedGMC γ q.1 (q.2 : Measure ℂ)
  have harg : Measurable (fun q : TwoSidedPath × FiniteMeasure ℂ => ((γ, q.1), q.2)) :=
    (measurable_const.prodMk measurable_fst).prodMk measurable_snd
  have hT : Measurable T := by
    change Measurable ((fun p : (ℝ × TwoSidedPath) × FiniteMeasure ℂ =>
      lateralProjectedGMC p.1.1 p.1.2 (p.2 : Measure ℂ)) ∘
      fun q : TwoSidedPath × FiniteMeasure ℂ => ((γ, q.1), q.2))
    exact measurable_lateralProjectedGMC_finite.comp harg
  have hMm := equatorGFF_GMC_aemeasurable P X hX γ hγ hγ2 M hM
  have hA := originRadialPath_aemeasurable P X Xc hc hcont
  have hMF : AEMeasurable (fun ω => (⟨M ω, hM.1 ω⟩ : FiniteMeasure ℂ)) P :=
    @AEMeasurable.subtype_mk Ω (Measure ℂ) _ _ M P hMm _ hM.1
  have hNf : ∀ ω, IsFiniteMeasure ((M ω).map (fun x : ℂ => x⁻¹)) := fun ω =>
    (FiniteMeasure.map (⟨M ω, hM.1 ω⟩ : FiniteMeasure ℂ) (fun x : ℂ => x⁻¹)).2
  have hNm : AEMeasurable (fun ω => (M ω).map (fun x : ℂ => x⁻¹)) P :=
    (Measure.measurable_map _ measurable_inv).comp_aemeasurable hMm
  have hNF : AEMeasurable (fun ω => FiniteMeasure.map (⟨M ω, hM.1 ω⟩ : FiniteMeasure ℂ)
      (fun x : ℂ => x⁻¹)) P :=
    @AEMeasurable.subtype_mk Ω (Measure ℂ) _ _ _ P hNm _ hNf
  have hL : AEMeasurable (fun ω => (originReversedRadialPath (originRadialPath Xc ω),
      FiniteMeasure.map (⟨M ω, hM.1 ω⟩ : FiniteMeasure ℂ) (fun x : ℂ => x⁻¹))) P :=
    (originReversedRadialPath_aemeasurable P _ hA).prodMk hNF
  have hR : AEMeasurable (fun ω => (originRadialPath Xc ω,
      (⟨M ω, hM.1 ω⟩ : FiniteMeasure ℂ))) P := hA.prodMk hMF
  have hj := originRadialGMC_inversion_joint_law P X Xc hX hc hcont γ hγ hγ2 M hM
  have h := (AEMeasurable.map_map_of_aemeasurable hT.aemeasurable hL).symm.trans
    ((congrArg (fun μ => μ.map T) hj).trans
      (AEMeasurable.map_map_of_aemeasurable hT.aemeasurable hR))
  change P.map (fun ω => lateralProjectedGMC γ (originReversedRadialPath (originRadialPath Xc ω))
    ((M ω).map (fun x : ℂ => x⁻¹))) =
    P.map (fun ω => lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)) at h
  simpa only [lateralProjectedGMC_reversed_inversion] using h

/-- The actual equator GMC has its complete two-sided radial/lateral
decomposition, including whole-measure stationarity and reflection. -/
theorem equatorGFF_lateral_GMC_decomposition
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (M : Ω → Measure ℂ) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∃ A : Ω → TwoSidedPath,
      (∃ Xc : Ω → ℂ → ℝ → ℝ, IsCircleAverage P X Xc ∧
        ∀ s : ℝ, ∀ᵐ ω ∂P, A ω s = Xc ω 0 s) ∧
      AEMeasurable A P ∧ (∀ᵐ ω ∂P, A ω 0 = 0) ∧
        ProbabilityTheory.IsBrownianReal (fun t ω => A ω (t : ℝ)) P ∧
        ProbabilityTheory.IsBrownianReal (fun t ω => A ω (-(t : ℝ))) P ∧
        IndepFun (fun ω => fun t : ℝ≥0 => A ω (t : ℝ))
          (fun ω => fun t : ℝ≥0 => A ω (-(t : ℝ))) P ∧
        AEMeasurable (fun ω => lateralProjectedGMC γ (A ω) (M ω)) P ∧
        IndepFun (fun ω => A ω) (fun ω => lateralProjectedGMC γ (A ω) (M ω)) P ∧
        IsLateralGMCOf P γ (fun ω =>
          lateralProjectedGMC γ (A ω) (M ω)) := by
  obtain ⟨Xc, hc, hm, hcont, hSource, hfin⟩ :=
    equatorGFF_exists_sourceLateralProjection P X hX γ hγ hγ2 M hM
  let A := originRadialPath Xc
  have hA := originRadialPath_aemeasurable P X Xc hc hcont
  have hB := originRadialPath_isBrownian P X Xc hX hc hcont
  have hZ := lateralProjectedGMC_aemeasurable P γ A hA M
    (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ2 M hM) hM.1
  have hi := lateralProjectedGMC_indep P X Xc hX hc hm hcont γ hγ hγ2 M hM
  refine ⟨A, ⟨Xc, hc, ?_⟩, hA, originRadialPath_zero_ae P X Xc hc hcont,
    hB.1, hB.2, originRadialPath_halves_indep P X Xc hX hc hcont, hZ, hi, ?_⟩
  · intro s
    exact (originRadialPath_eval_ae hcont).mono (fun ω hω => hω s)
  · refine ⟨hγ, hγ2, hX.1, hZ, hfin, ?_, ?_, ?_, ⟨X, M, hSource⟩⟩
    · exact fun t => lateralProjectedGMC_translation_law P X Xc hX hc hm hcont
        γ hγ hγ2 M hM t
    · exact lateralProjectedGMC_reflection_law P X Xc hX hc hcont γ hγ hγ2 M hM
    · exact fun a b _hab => lateralProjectedGMC_interval_intensity P X Xc hX hc hm hcont
        γ hγ hγ2 M hM a b

end DOZZ.Proofs

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Brownian.Lateral.DilationLaw
public import DOZZ.GMC.Moments.InversionMeasureLaw
public import DOZZ.Brownian.LateralLocalFiniteness
@[expose] public section
open Filter MeasureTheory Set
open scoped Topology Distributions ENNReal
namespace DOZZ.Proofs

/-- A bounded open annulus used to exhaust the punctured plane. -/
def lateralLawAnnulus (n : ℕ) : Set ℂ :=
  {x | 1 / ((n : ℝ) + 2) < ‖x‖ ∧ ‖x‖ < (n : ℝ) + 2}

/-- The annular exhaustion consists of open sets. -/
theorem isOpen_lateralLawAnnulus (n : ℕ) : IsOpen (lateralLawAnnulus n) :=
  (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt continuous_norm continuous_const)

/-- Its closure is compact and stays away from the origin. -/
theorem lateralLawAnnulus_closure (n : ℕ) :
    IsCompact (closure (lateralLawAnnulus n)) ∧ (0 : ℂ) ∉ closure (lateralLawAnnulus n) := by
  have hs : closure (lateralLawAnnulus n) ⊆
      {x : ℂ | 1 / ((n : ℝ) + 2) ≤ ‖x‖ ∧ ‖x‖ ≤ (n : ℝ) + 2} := by
    apply closure_minimal
    · exact fun _ hx => ⟨hx.1.le, hx.2.le⟩
    · exact (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
  constructor
  · apply (isCompact_closedBall (0 : ℂ) ((n : ℝ) + 2)).of_isClosed_subset isClosed_closure
    intro x hx
    simpa only [Metric.mem_closedBall, dist_zero_right] using (hs hx).2
  · intro h
    have hn : 0 < 1 / ((n : ℝ) + 2) := by positivity
    exact (not_le_of_gt hn) (by simpa only [norm_zero] using (hs h).1)

/-- The annuli increase. -/
theorem lateralLawAnnulus_monotone : Monotone lateralLawAnnulus := by
  intro n k hnk x hx
  have hnk' : (n : ℝ) + 2 ≤ (k : ℝ) + 2 := by exact_mod_cast Nat.add_le_add_right hnk 2
  exact ⟨lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) hnk') hx.1,
    hx.2.trans_le hnk'⟩

/-- Every nonzero point is in some annulus. -/
theorem lateralLawAnnulus_exhaustion :
    (⋃ n, lateralLawAnnulus n) = ({0} : Set ℂ)ᶜ := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    have hpos : 0 < ‖x‖ := lt_trans (by positivity) hn.1
    simpa only [mem_compl_iff, mem_singleton_iff] using norm_pos_iff.mp hpos
  · intro hx
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
    obtain ⟨n, hn⟩ := exists_nat_gt (max ‖x‖ (1 / ‖x‖))
    apply mem_iUnion.mpr
    refine ⟨n, ?_, ?_⟩
    · have ht : 1 / ‖x‖ < (n : ℝ) + 2 := (le_max_right _ _).trans_lt hn |>.trans (by linarith)
      exact (div_lt_iff₀ (by positivity)).mpr
        (by simpa only [one_mul, mul_comm] using (div_lt_iff₀ hxpos).mp ht)
    · exact (le_max_left _ _).trans_lt hn |>.trans (by linarith)

private abbrev LateralAnnularOpen :=
  {U : Set ℂ // IsOpen U ∧ IsCompact (closure U) ∧ (0 : ℂ) ∉ closure U}
private abbrev LateralLocallyFiniteMeasure :=
  {μ : Measure ℂ // μ {0} = 0 ∧ ∀ K : Set ℂ,
    IsCompact K → (0 : ℂ) ∉ K → μ K < ⊤}
private def lateralAnnularMeasureCode (μ : LateralLocallyFiniteMeasure) :
    LateralAnnularOpen → ℝ≥0∞ := fun U => μ.1 U.1

/-- The law of a locally finite punctured-plane random measure is determined by finite
vectors of relatively compact open masses. Measurability up to a null event suffices. -/
theorem lateral_random_measure_law_of_annular_open_fdd
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (M N : Ω → Measure ℂ) (hM : AEMeasurable M P) (hN : AEMeasurable N P)
    (hMf : ∀ ω, M ω {0} = 0 ∧ ∀ K : Set ℂ,
      IsCompact K → (0 : ℂ) ∉ K → M ω K < ⊤)
    (hNf : ∀ ω, N ω {0} = 0 ∧ ∀ K : Set ℂ,
      IsCompact K → (0 : ℂ) ∉ K → N ω K < ⊤)
    (hfdd : ∀ (ι : Type) [Fintype ι] (U : ι → Set ℂ),
      (∀ j, IsOpen (U j) ∧ IsCompact (closure (U j)) ∧ (0 : ℂ) ∉ closure (U j)) →
      P.map (fun ω j => M ω (U j)) = P.map (fun ω j => N ω (U j))) :
    P.map M = P.map N := by
  classical
  let C := measurableCylinders (fun _ : LateralAnnularOpen => ℝ≥0∞)
  let mOutput : MeasurableSpace LateralLocallyFiniteMeasure :=
    MeasurableSpace.pi.comap lateralAnnularMeasureCode
  let : MeasurableSpace LateralLocallyFiniteMeasure := mOutput
  let outM : Ω → LateralLocallyFiniteMeasure := fun ω => ⟨M ω, hMf ω⟩
  let outN : Ω → LateralLocallyFiniteMeasure := fun ω => ⟨N ω, hNf ω⟩
  let Cout := Set.preimage lateralAnnularMeasureCode '' C
  have hgen : mOutput = MeasurableSpace.generateFrom Cout := by
    dsimp [mOutput, Cout, C]
    rw [← generateFrom_measurableCylinders, MeasurableSpace.comap_generateFrom]
  have hpi : IsPiSystem Cout := by
    intro A hA B hB hAB
    rcases hA with ⟨A', hA', rfl⟩
    rcases hB with ⟨B', hB', rfl⟩
    refine ⟨A' ∩ B', isPiSystem_measurableCylinders A' hA' B' hB' ?_, ?_⟩
    · rcases hAB with ⟨q, hq⟩
      exact ⟨lateralAnnularMeasureCode q, hq⟩
    · rw [← Set.preimage_inter]
  have hcode : Measurable lateralAnnularMeasureCode := Measurable.of_comap_le le_rfl
  have hto : @Measurable LateralLocallyFiniteMeasure LateralLocallyFiniteMeasure
      (Subtype.instMeasurableSpace) mOutput id := by
    rw [measurable_iff_comap_le]
    rw [MeasurableSpace.comap_id]
    let : MeasurableSpace LateralLocallyFiniteMeasure := Subtype.instMeasurableSpace
    have hcstd : Measurable lateralAnnularMeasureCode := measurable_pi_iff.mpr fun U =>
      (Measure.measurable_coe U.2.1.measurableSet).comp measurable_subtype_coe
    exact hcstd.comap_le
  have hom : AEMeasurable outM P :=
    @Measurable.comp_aemeasurable Ω LateralLocallyFiniteMeasure LateralLocallyFiniteMeasure
      _ mOutput P Subtype.instMeasurableSpace outM id hto
      (@AEMeasurable.subtype_mk Ω (Measure ℂ) _ _ M P hM _ hMf)
  have hon : AEMeasurable outN P :=
    @Measurable.comp_aemeasurable Ω LateralLocallyFiniteMeasure LateralLocallyFiniteMeasure
      _ mOutput P Subtype.instMeasurableSpace outN id hto
      (@AEMeasurable.subtype_mk Ω (Measure ℂ) _ _ N P hN _ hNf)
  have hOpenGen : (inferInstance : MeasurableSpace ℂ) =
      MeasurableSpace.generateFrom {s : Set ℂ | IsOpen s} := by
    calc
      (inferInstance : MeasurableSpace ℂ) = borel ℂ := BorelSpace.measurable_eq
      _ = _ := borel_eq_generateFrom_of_subbasis
        (TopologicalSpace.generateFrom_setOfPred_isOpen (inferInstance : TopologicalSpace ℂ)).symm
  have hrestrict (n : ℕ) : Measurable
      (fun q : LateralLocallyFiniteMeasure => q.1.restrict (lateralLawAnnulus n)) := by
    let : ∀ q : LateralLocallyFiniteMeasure,
        IsFiniteMeasure (q.1.restrict (lateralLawAnnulus n)) := fun q => ⟨by
      rw [Measure.restrict_apply_univ]
      exact lt_of_le_of_lt (measure_mono subset_closure)
        (q.2.2 _ (lateralLawAnnulus_closure n).1 (lateralLawAnnulus_closure n).2)⟩
    apply Measurable.measure_of_isPiSystem hOpenGen isPiSystem_isOpen
    · intro S hS
      change IsOpen S at hS
      have hcs : closure (S ∩ lateralLawAnnulus n) ⊆ closure (lateralLawAnnulus n) :=
        closure_mono inter_subset_right
      have hu : IsOpen (S ∩ lateralLawAnnulus n) ∧
          IsCompact (closure (S ∩ lateralLawAnnulus n)) ∧
          (0 : ℂ) ∉ closure (S ∩ lateralLawAnnulus n) :=
        ⟨hS.inter (isOpen_lateralLawAnnulus n),
          (lateralLawAnnulus_closure n).1.of_isClosed_subset isClosed_closure hcs,
          fun h => (lateralLawAnnulus_closure n).2 (hcs h)⟩
      simpa only [lateralAnnularMeasureCode, Measure.restrict_apply hS.measurableSet] using
        (measurable_pi_iff.mp hcode) ⟨S ∩ lateralLawAnnulus n, hu⟩
    · simpa only [lateralAnnularMeasureCode, Measure.restrict_apply_univ] using
        (measurable_pi_iff.mp hcode) ⟨lateralLawAnnulus n,
          isOpen_lateralLawAnnulus n, lateralLawAnnulus_closure n⟩
  have hforget : Measurable (fun q : LateralLocallyFiniteMeasure => q.1) := by
    apply Measure.measurable_of_measurable_coe
    intro S hS
    have heq : (fun q : LateralLocallyFiniteMeasure => q.1 S) =
        fun q => ⨆ n, q.1.restrict (lateralLawAnnulus n) S := by
      funext q
      have hsupport : q.1.restrict (⋃ n, lateralLawAnnulus n) = q.1 := by
        rw [lateralLawAnnulus_exhaustion]
        exact Measure.restrict_eq_self_of_ae_mem (by
          rw [ae_iff]; simpa only [not_not, mem_compl_iff, ofPred_mem_eq] using q.2.1)
      calc q.1 S = q.1.restrict (⋃ n, lateralLawAnnulus n) S :=
        congrArg (fun μ : Measure ℂ => μ S) hsupport.symm
      _ = _ := Measure.restrict_iUnion_apply_eq_iSup lateralLawAnnulus_monotone.directed_le hS
    rw [heq]
    exact Measurable.iSup fun n => (Measure.measurable_coe hS).comp (hrestrict n)
  have hLaw : P.map outM = P.map outN := by
    apply MeasureTheory.ext_of_generate_finite Cout hgen hpi
    · intro S hS
      rcases hS with ⟨A, hA, rfl⟩
      rcases (mem_measurableCylinders A).1 hA with ⟨s, As, hAs, rfl⟩
      let vm := fun ω (j : s) => M ω j.1.1
      let vn := fun ω (j : s) => N ω j.1.1
      have hm : AEMeasurable vm P := AEMeasurable.of_eval fun j =>
        (Measure.measurable_coe j.1.2.1.measurableSet).comp_aemeasurable hM
      have hn : AEMeasurable vn P := AEMeasurable.of_eval fun j =>
        (Measure.measurable_coe j.1.2.1.measurableSet).comp_aemeasurable hN
      have hv := hfdd s (fun j => j.1.1) (fun j => j.1.2)
      have hp : P (vm ⁻¹' As) = P (vn ⁻¹' As) := by
        have h := congrArg (fun μ => μ As) hv
        rw [Measure.map_apply_of_aemeasurable hm hAs,
          Measure.map_apply_of_aemeasurable hn hAs] at h
        exact h
      have hs : MeasurableSet (lateralAnnularMeasureCode ⁻¹' cylinder s As) := by
        apply hcode
        rw [← generateFrom_measurableCylinders]
        exact MeasurableSpace.measurableSet_generateFrom
          (cylinder_mem_measurableCylinders (α := fun _ : LateralAnnularOpen => ℝ≥0∞) s As hAs)
      rw [Measure.map_apply_of_aemeasurable hom hs, Measure.map_apply_of_aemeasurable hon hs]
      exact hp
    · simp only [Measure.map_apply_of_aemeasurable hom MeasurableSet.univ,
        Measure.map_apply_of_aemeasurable hon MeasurableSet.univ, preimage_univ]
  have he := congrArg (fun μ => μ.map (fun q : LateralLocallyFiniteMeasure => q.1)) hLaw
  simpa only [AEMeasurable.map_map_of_aemeasurable hforget.aemeasurable hom,
    AEMeasurable.map_map_of_aemeasurable hforget.aemeasurable hon, Function.comp_def] using he

/-- Removing the radial factor preserves finiteness on every compact subset of the
punctured plane. Its logarithmic radii lie in a compact interval. -/
theorem originRadialRemovedGMC_compact_lt_top
    (γ : ℝ) (A : TwoSidedPath) (M : Measure ℂ) [IsFiniteMeasure M]
    (K : Set ℂ) (hK : IsCompact K) (hzero : (0 : ℂ) ∉ K) :
    M.withDensity (lateralRadialWeight γ A) K < ⊤ := by
  let r : ℂ → ℝ := fun x => -Real.log ‖x‖
  have hr : ContinuousOn r K :=
    (continuous_norm.continuousOn.log (fun x hx =>
      norm_ne_zero_iff.mpr (fun h => hzero (h ▸ hx)))).neg
  obtain ⟨a, ha⟩ := (hK.image_of_continuousOn hr).bddBelow
  obtain ⟨b, hb⟩ := (hK.image_of_continuousOn hr).bddAbove
  have hsub : K ⊆ r ⁻¹' Icc a b := fun x hx =>
    ⟨ha ⟨x, hx, rfl⟩, hb ⟨x, hx, rfl⟩⟩
  have hrm : Measurable r := measurable_neg.comp (Real.measurable_log.comp measurable_norm)
  calc
    M.withDensity (lateralRadialWeight γ A) K ≤
        M.withDensity (lateralRadialWeight γ A) (r ⁻¹' Icc a b) := measure_mono hsub
    _ = lateralProjectedGMC γ A M (Icc a b) :=
      (Measure.map_apply hrm measurableSet_Icc).symm
    _ < ⊤ := lateralProjectedGMC_Icc_ne_top γ A M a b

/-- Bounded continuous integrals of finite random measures are measurable up to null sets. -/
theorem finiteMeasure_bcf_integral_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : Ω → Measure ℂ) (hM : AEMeasurable M P)
    (hfin : ∀ ω, IsFiniteMeasure (M ω)) (f : BoundedContinuousFunction ℂ ℝ) :
    AEMeasurable (fun ω => ∫ x, f x ∂M ω) P := by
  let : ∀ ω, IsFiniteMeasure (M ω) := hfin
  have hp := (Measure.measurable_lintegral
    (BoundedContinuousFunction.measurable_coe_ennreal_comp f.nnrealPart)).comp_aemeasurable hM
  have hn := (Measure.measurable_lintegral
    (BoundedContinuousFunction.measurable_coe_ennreal_comp (-f).nnrealPart)).comp_aemeasurable hM
  have h : AEMeasurable (fun ω =>
      (∫⁻ x, (f.nnrealPart x : ℝ≥0∞) ∂M ω).toReal -
      (∫⁻ x, ((-f).nnrealPart x : ℝ≥0∞) ∂M ω).toReal) P :=
    hp.ennreal_toReal.sub hn.ennreal_toReal
  simpa only [BoundedContinuousFunction.integral_eq_integral_nnrealPart_sub,
    BoundedContinuousFunction.toReal_lintegral_coe_eq_integral, Function.comp_def, Pi.sub_apply] using h

/-- A test vanishing outside a measurable set has the same integral against its restriction. -/
theorem lateral_integral_restrict_of_zero_outside
    (μ : Measure ℂ) (K : Set ℂ) (hK : MeasurableSet K) (f : ℂ → ℝ)
    (hf : ∀ x, x ∉ K → f x = 0) :
    ∫ x, f x ∂μ.restrict K = ∫ x, f x ∂μ := by
  rw [← integral_indicator hK]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    by_cases hx : x ∈ K
    · exact indicator_of_mem hx f
    · simp only [indicator_of_notMem hx, hf x hx]

/-- Compactly supported test integrals of a punctured locally finite random measure
are measurable up to a null event. -/
theorem lateral_compact_test_integral_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : Ω → Measure ℂ) (hM : AEMeasurable M P)
    (f : BoundedContinuousFunction ℂ ℝ) (hfc : HasCompactSupport (f : ℂ → ℝ))
    (hzero : (0 : ℂ) ∉ tsupport (f : ℂ → ℝ))
    (hfin : ∀ ω K, IsCompact K → (0 : ℂ) ∉ K → M ω K < ⊤) :
    AEMeasurable (fun ω => ∫ x, f x ∂M ω) P := by
  let K := tsupport (f : ℂ → ℝ)
  have hK : MeasurableSet K := (isClosed_tsupport _).measurableSet
  have hr := (measurable_measure_restrict K hK).comp_aemeasurable hM
  change AEMeasurable (fun ω => (M ω).restrict K) P at hr
  have hrf : ∀ ω, IsFiniteMeasure ((M ω).restrict K) := fun ω => ⟨by
    rw [Measure.restrict_apply_univ]; exact hfin ω K hfc hzero⟩
  have he ω : (∫ x, f x ∂(M ω).restrict K) = ∫ x, f x ∂M ω :=
    lateral_integral_restrict_of_zero_outside _ K hK f
      (fun x hx => image_eq_zero_of_notMem_tsupport hx)
  simpa only [he] using finiteMeasure_bcf_integral_aemeasurable P _ hr hrf f

/-- Open-set distance approximations vanish outside the open set. -/
theorem gmcOpenApprox_zero_outside (U : Set ℂ) (hU : IsOpen U) (n : ℕ)
    (x : ℂ) (hx : x ∉ U) : gmcOpenApprox U hU n x = 0 := by
  classical
  have h : U ≠ univ := fun h => hx (h ▸ mem_univ x)
  simp [gmcOpenApprox, h, Metric.infDist_zero_of_mem (show x ∈ Uᶜ from hx)]

/-- Every distance approximation has support in the closure of the approximated open set. -/
theorem gmcOpenApprox_tsupport_subset (U : Set ℂ) (hU : IsOpen U) (n : ℕ) :
    tsupport (gmcOpenApprox U hU n : ℂ → ℝ) ⊆ closure U := by
  apply closure_mono
  intro x hx
  by_contra h
  exact hx (gmcOpenApprox_zero_outside U hU n x h)

/-- Distance approximations recover the mass of a relatively compact open set under
any measure finite on its closure. -/
theorem lateral_openApprox_integral_tendsto
    (μ : Measure ℂ) (U : Set ℂ) (hU : IsOpen U) (hfin : μ (closure U) < ⊤) :
    Tendsto (fun n => ∫ x, gmcOpenApprox U hU n x ∂μ) atTop (𝓝 ((μ U).toReal)) := by
  let : IsFiniteMeasure (μ.restrict (closure U)) := ⟨by
    rw [Measure.restrict_apply_univ]; exact hfin⟩
  have he n : (∫ x, gmcOpenApprox U hU n x ∂μ.restrict (closure U)) =
      ∫ x, gmcOpenApprox U hU n x ∂μ :=
    lateral_integral_restrict_of_zero_outside μ (closure U) isClosed_closure.measurableSet _
      (fun x hx => image_eq_zero_of_notMem_tsupport
        (fun h => hx (gmcOpenApprox_tsupport_subset U hU n h)))
  have hmass : μ.restrict (closure U) U = μ U := by
    rw [Measure.restrict_apply hU.measurableSet, inter_eq_left.mpr subset_closure]
  simpa only [he, hmass] using gmcOpenApprox_integral_tendsto (μ.restrict (closure U)) U hU

/-- Equality of finite vectors of compact test integrals determines finite vectors of
relatively compact open-set masses, even for measures with infinite total mass. -/
theorem lateral_open_mass_fdd_of_compact_test_fdd
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M N : Ω → Measure ℂ) (hM : AEMeasurable M P) (hN : AEMeasurable N P)
    (hMf : ∀ ω K, IsCompact K → (0 : ℂ) ∉ K → M ω K < ⊤)
    (hNf : ∀ ω K, IsCompact K → (0 : ℂ) ∉ K → N ω K < ⊤)
    (htest : ∀ {m : ℕ} (f : Fin m → BoundedContinuousFunction ℂ ℝ),
      (∀ j, HasCompactSupport (f j : ℂ → ℝ)) →
      (∀ j, (0 : ℂ) ∉ tsupport (f j : ℂ → ℝ)) →
      P.map (fun ω j => ∫ x, f j x ∂M ω) = P.map (fun ω j => ∫ x, f j x ∂N ω))
    (ι : Type) [Fintype ι] (U : ι → Set ℂ)
    (hU : ∀ j, IsOpen (U j) ∧ IsCompact (closure (U j)) ∧ (0 : ℂ) ∉ closure (U j)) :
    P.map (fun ω j => M ω (U j)) = P.map (fun ω j => N ω (U j)) := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let q := fun n j => gmcOpenApprox (U (e j)) (hU (e j)).1 n
  have hqc n j : HasCompactSupport (q n j : ℂ → ℝ) :=
    (hU (e j)).2.1.of_isClosed_subset (isClosed_tsupport _)
      (gmcOpenApprox_tsupport_subset _ _ n)
  have hqzero n j : (0 : ℂ) ∉ tsupport (q n j : ℂ → ℝ) :=
    fun h => (hU (e j)).2.2 (gmcOpenApprox_tsupport_subset _ _ n h)
  let A := fun ω (j : Fin (Fintype.card ι)) => (M ω (U (e j))).toReal
  let B := fun ω (j : Fin (Fintype.card ι)) => (N ω (U (e j))).toReal
  have hA : AEMeasurable A P := AEMeasurable.of_eval fun j =>
    ((Measure.measurable_coe (hU (e j)).1.measurableSet).comp_aemeasurable hM).ennreal_toReal
  have hB : AEMeasurable B P := AEMeasurable.of_eval fun j =>
    ((Measure.measurable_coe (hU (e j)).1.measurableSet).comp_aemeasurable hN).ennreal_toReal
  have hqm n j := lateral_compact_test_integral_aemeasurable P M hM (q n j)
    (hqc n j) (hqzero n j) hMf
  have hqn n j := lateral_compact_test_integral_aemeasurable P N hN (q n j)
    (hqc n j) (hqzero n j) hNf
  have hlaw : P.map A = P.map B := by
    apply gmc_limit_test_vector_law
      (fun n ω j => ∫ x, q n j x ∂M ω) (fun n ω j => ∫ x, q n j x ∂N ω) A B
    · intro n; exact AEMeasurable.of_eval (hqm n)
    · intro n; exact AEMeasurable.of_eval (hqn n)
    · exact hA
    · exact hB
    · intro n; exact htest (q n) (hqc n) (hqzero n)
    · intro j
      apply tendstoInMeasure_of_tendsto_ae (fun n => (hqm n j).aestronglyMeasurable)
      exact ae_of_all _ fun ω => lateral_openApprox_integral_tendsto _ _ (hU (e j)).1
        (hMf ω _ (hU (e j)).2.1 (hU (e j)).2.2)
    · intro j
      apply tendstoInMeasure_of_tendsto_ae (fun n => (hqn n j).aestronglyMeasurable)
      exact ae_of_all _ fun ω => lateral_openApprox_integral_tendsto _ _ (hU (e j)).1
        (hNf ω _ (hU (e j)).2.1 (hU (e j)).2.2)
  let post := fun v : Fin (Fintype.card ι) → ℝ =>
    fun j : ι => ENNReal.ofReal (v (e.symm j))
  have hp : Measurable post := by fun_prop
  have heA : post ∘ A = fun ω j => M ω (U j) := by
    funext ω j
    simp only [post, A, Function.comp_apply, Equiv.apply_symm_apply]
    exact ENNReal.ofReal_toReal (lt_of_le_of_lt (measure_mono subset_closure)
      (hMf ω _ (hU j).2.1 (hU j).2.2)).ne
  have heB : post ∘ B = fun ω j => N ω (U j) := by
    funext ω j
    simp only [post, B, Function.comp_apply, Equiv.apply_symm_apply]
    exact ENNReal.ofReal_toReal (lt_of_le_of_lt (measure_mono subset_closure)
      (hNf ω _ (hU j).2.1 (hU j).2.2)).ne
  calc
    P.map (fun ω j => M ω (U j)) = (P.map A).map post := by
      rw [AEMeasurable.map_map_of_aemeasurable hp.aemeasurable hA, heA]
    _ = (P.map B).map post := congrArg (Measure.map post) hlaw
    _ = P.map (fun ω j => N ω (U j)) := by
      rw [AEMeasurable.map_map_of_aemeasurable hp.aemeasurable hB, heB]

/-- Compact test-vector laws determine entire punctured locally finite measure laws. -/
theorem lateral_random_measure_law_of_compact_test_fdd
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M N : Ω → Measure ℂ) (hM : AEMeasurable M P) (hN : AEMeasurable N P)
    (hMf : ∀ ω, M ω {0} = 0 ∧ ∀ K : Set ℂ,
      IsCompact K → (0 : ℂ) ∉ K → M ω K < ⊤)
    (hNf : ∀ ω, N ω {0} = 0 ∧ ∀ K : Set ℂ,
      IsCompact K → (0 : ℂ) ∉ K → N ω K < ⊤)
    (htest : ∀ {m : ℕ} (f : Fin m → BoundedContinuousFunction ℂ ℝ),
      (∀ j, HasCompactSupport (f j : ℂ → ℝ)) →
      (∀ j, (0 : ℂ) ∉ tsupport (f j : ℂ → ℝ)) →
      P.map (fun ω j => ∫ x, f j x ∂M ω) = P.map (fun ω j => ∫ x, f j x ∂N ω)) :
    P.map M = P.map N :=
  lateral_random_measure_law_of_annular_open_fdd P M N hM hN hMf hNf
    (lateral_open_mass_fdd_of_compact_test_fdd P M N hM hN
      (fun ω => (hMf ω).2) (fun ω => (hNf ω).2) htest)

/-- Every compact subset of the punctured plane fits in a positive lateral chart. -/
theorem exists_originLateralChart_of_compact
    (K : Set ℂ) (hK : IsCompact K) (hzero : (0 : ℂ) ∉ K) :
    ∃ ρ : ℝ, 0 < ρ ∧ K ⊆ originLateralChart ρ := by
  by_cases hn : K.Nonempty
  · obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn hn continuous_norm.continuousOn
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr (fun h => hzero (h ▸ hx))
    refine ⟨‖x‖ / 4, by positivity, ?_⟩
    intro y hy
    have hxy : ‖x‖ ≤ ‖y‖ := (isMinOn_iff.mp hmin) y hy
    change 2 * (‖x‖ / 4) < ‖y‖
    linarith
  · exact ⟨1, zero_lt_one, (not_nonempty_iff_eq_empty.mp hn) ▸ empty_subset _⟩

/-- Nonzero dilation preserves zero origin mass and local finiteness on punctured compacts. -/
theorem lateral_locally_finite_map_dilation
    (μ : Measure ℂ) (hzero : μ {0} = 0)
    (hfin : ∀ K, IsCompact K → (0 : ℂ) ∉ K → μ K < ⊤)
    (c : ℝ) (hc : 0 < c) :
    (μ.map (fun x : ℂ => (c : ℂ) * x)) {0} = 0 ∧
      ∀ K, IsCompact K → (0 : ℂ) ∉ K →
        (μ.map (fun x : ℂ => (c : ℂ) * x)) K < ⊤ := by
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hm : Measurable (fun x : ℂ => (c : ℂ) * x) := by fun_prop
  constructor
  · rw [Measure.map_apply hm (measurableSet_singleton 0)]
    simpa only [preimage, mem_singleton_iff, mul_eq_zero, hc0, false_or,
      ofPred_eq_eq_singleton] using hzero
  · intro K hK hz
    rw [Measure.map_apply hm hK.measurableSet]
    exact hfin _ ((Homeomorph.mulLeft₀ (c : ℂ) hc0).isCompact_preimage.mpr hK)
      (by simpa only [mem_preimage, mul_zero] using hz)

/-- Dilation invariance of compact-test vectors with only their intrinsic support
conditions; the common chart and pullback support are constructed here. -/
theorem originRadialRemovedGMC_dilation_annular_test_vector_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (c γ : ℝ) (hcpos : 0 < c) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    {m : ℕ} (f : Fin m → BoundedContinuousFunction ℂ ℝ)
    (hfc : ∀ j, HasCompactSupport (f j : ℂ → ℝ))
    (hfzero : ∀ j, (0 : ℂ) ∉ tsupport (f j : ℂ → ℝ)) :
    P.map (fun ω j => ∫ x, f j x
      ∂(M ω).withDensity (lateralRadialWeight γ (originRadialPath Xc ω))) =
    P.map (fun ω j => ∫ x, f j (c * x)
      ∂(M ω).withDensity (lateralRadialWeight γ (originRadialPath Xc ω))) := by
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hcpos.ne'
  let e := Homeomorph.mulLeft₀ (c : ℂ) hc0
  let T := ⋃ j, tsupport (f j : ℂ → ℝ)
  have hT : IsCompact T := isCompact_iUnion hfc
  have hTzero : (0 : ℂ) ∉ T := by
    intro h; obtain ⟨j, hj⟩ := mem_iUnion.mp h; exact hfzero j hj
  let K := e ⁻¹' T
  have hK : IsCompact K := e.isCompact_preimage.mpr hT
  have hKzero : (0 : ℂ) ∉ K := by simpa only [K, mem_preimage, e,
    Homeomorph.coe_mulLeft₀, mul_zero] using hTzero
  obtain ⟨ρ, hρ, hKU⟩ := exists_originLateralChart_of_compact K hK hKzero
  have hgK j : tsupport (fun x : ℂ => f j (c * x)) ⊆ K :=
    (tsupport_comp_subset_preimage (f j : ℂ → ℝ) e.continuous).trans
      (preimage_mono (subset_iUnion (fun j => tsupport (f j : ℂ → ℝ)) j))
  have hgc j : HasCompactSupport (fun x : ℂ => f j (c * x)) :=
    (hfc j).comp_homeomorph e
  have hgU j : tsupport (fun x : ℂ => f j (c * x)) ⊆ originLateralChart ρ :=
    (hgK j).trans hKU
  have hfV j : tsupport (f j : ℂ → ℝ) ⊆ originLateralChart (c * ρ) := by
    intro x hx
    have hpre : e.symm x ∈ K := by
      change e (e.symm x) ∈ T
      rw [e.apply_symm_apply]
      exact mem_iUnion.mpr ⟨j, hx⟩
    have h := (originLateralChart_dilation_mem ρ c hcpos (e.symm x)).mpr (hKU hpre)
    change e (e.symm x) ∈ originLateralChart (c * ρ) at h
    simpa only [e.apply_symm_apply] using h
  exact originRadialRemovedGMC_dilation_test_vector_law P X Xc hX hc hm hcont
    ρ c γ hρ hcpos hγ hγ2 M hM K hK hKU f hfc hfV
    (fun j x hx => image_eq_zero_of_notMem_tsupport (fun h =>
      hx (show e x ∈ T from mem_iUnion.mpr ⟨j, h⟩))) hgc hgU

/-- Positive dilation preserves the law of the entire actual radial-removed
measure. The measure need only be locally finite on the punctured plane. -/
theorem originRadialRemovedGMC_dilation_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (c γ : ℝ) (hcpos : 0 < c) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) :
    P.map (fun ω => ((M ω).withDensity (lateralRadialWeight γ (originRadialPath Xc ω))).map
      (fun x : ℂ => (c : ℂ) * x)) =
    P.map (fun ω => (M ω).withDensity (lateralRadialWeight γ (originRadialPath Xc ω))) := by
  let : IsProbabilityMeasure P := hX.1
  let F := fun ω => (M ω).withDensity (lateralRadialWeight γ (originRadialPath Xc ω))
  have hA := originRadialPath_aemeasurable P X Xc hc hcont
  have hMm := equatorGFF_GMC_aemeasurable P X hX γ hγ hγ2 M hM
  have hF := originRadialRemovedGMC_aemeasurable P γ _ hA M hMm hM.1
  have hs : Measurable (fun x : ℂ => (c : ℂ) * x) := by fun_prop
  have hN : AEMeasurable (fun ω => (F ω).map (fun x : ℂ => (c : ℂ) * x)) P :=
    (Measure.measurable_map _ hs).comp_aemeasurable hF
  have hfin ω K hK hz := @originRadialRemovedGMC_compact_lt_top γ
    (originRadialPath Xc ω) (M ω) (hM.1 ω) K hK hz
  have hf ω := lateral_locally_finite_map_dilation (F ω)
    (originRadialRemovedGMC_origin γ _ _) (hfin ω) c hcpos
  apply lateral_random_measure_law_of_compact_test_fdd P _ F hN hF hf
    (fun ω => ⟨originRadialRemovedGMC_origin γ _ _, hfin ω⟩)
  intro m f hfc hz
  have he ω j : (∫ x, f j x ∂(F ω).map (fun x : ℂ => (c : ℂ) * x)) =
      ∫ x, f j (c * x) ∂F ω :=
    integral_map hs.aemeasurable (f j).continuous.aestronglyMeasurable
  change P.map (fun ω j => ∫ x, f j x ∂(F ω).map (fun x : ℂ => (c : ℂ) * x)) =
    P.map (fun ω j => ∫ x, f j x ∂F ω)
  simp_rw [he]
  exact (originRadialRemovedGMC_dilation_annular_test_vector_law P X Xc hX hc hm hcont
    c γ hcpos hγ hγ2 M hM f hfc hz).symm

/-- Translation preserves the law of the entire polar lateral projection
`DOZZ.lateralProjectedGMC`. -/
theorem lateralProjectedGMC_translation_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (t : ℝ) :
    P.map (fun ω => (lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)).map
      (fun s : ℝ => s + t)) =
    P.map (fun ω => lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)) := by
  let F := fun ω => (M ω).withDensity (lateralRadialWeight γ (originRadialPath Xc ω))
  let c := Real.exp (-t)
  have hcpos : 0 < c := Real.exp_pos _
  have hs : Measurable (fun x : ℂ => (c : ℂ) * x) := by fun_prop
  have hr : Measurable (fun x : ℂ => -Real.log ‖x‖) := by fun_prop
  have hmap := originRadialRemovedGMC_dilation_law P X Xc hX hc hm hcont
    c γ hcpos hγ hγ2 M hM
  have hF := originRadialRemovedGMC_aemeasurable P γ _
    (originRadialPath_aemeasurable P X Xc hc hcont) M
    (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ2 M hM) hM.1
  have hN : AEMeasurable (fun ω => (F ω).map (fun x : ℂ => (c : ℂ) * x)) P :=
    (Measure.measurable_map _ hs).comp_aemeasurable hF
  have hproj := Measure.measurable_map _ hr
  have h := congrArg (fun μ : Measure (Measure ℂ) => μ.map (fun ν => ν.map
    (fun x : ℂ => -Real.log ‖x‖))) hmap
  rw [AEMeasurable.map_map_of_aemeasurable hproj.aemeasurable hN,
    AEMeasurable.map_map_of_aemeasurable hproj.aemeasurable hF] at h
  have he ω : ((F ω).map (fun x : ℂ => (c : ℂ) * x)).map
      (fun x : ℂ => -Real.log ‖x‖) =
      (lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)).map (fun s : ℝ => s + t) := by
    rw [logRadiusProjection_dilation (F ω) (originRadialRemovedGMC_origin γ _ _) c hcpos]
    change (lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)).map _ = _
    congr 1
    funext s
    simp only [c, Real.log_exp, sub_neg_eq_add]
  change P.map (fun ω => ((F ω).map (fun x : ℂ => (c : ℂ) * x)).map
    (fun x : ℂ => -Real.log ‖x‖)) =
    P.map (fun ω => lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)) at h
  simpa only [he] using h

end DOZZ.Proofs

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.GFFStructure.DirichletGlobal
public import DOZZ.GFF.TorusFourierTestL2
public import DOZZ.GFF.LocalModeSubsequence
/-!
# Fourier distribution versions of bounded disk maps

Normalized Fourier modes of any bounded disk L² map have summable squared
random L² norms. On a measurable full-measure event, their samples define
continuous Fourier functionals. Finite cutoff Fourier approximations identify
these measurable test evaluations with the original map on supported tests.
The original sample space and its sigma algebra are retained.
-/

@[expose] public section
open Filter MeasureTheory ProbabilityTheory Set Metric
open scoped Topology ENNReal NNReal InnerProductSpace lp
namespace DOZZ.Proofs

/-- A disk restriction bounded pointwise by one has norm controlled by the disk area. -/
theorem diskTestRestrictionL2_norm_le_area (c : ℂ) (ρ : ℝ) (f : TestFn)
    (hf : ∀ z, |f z| ≤ 1) :
    ‖diskTestRestrictionL2 c ρ f‖ ≤ Real.sqrt (volume (ball c ρ)).toReal := by
  let μ := volume.restrict (ball c ρ)
  let _ : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hi : Integrable (fun z => (f z)^2) μ :=
    (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport).integrable_sq
  have h := integral_mono_ae hi (integrable_const (1 : ℝ))
    (ae_of_all μ (fun z => (sq_le_one_iff_abs_le_one _).mpr (hf z)))
  have he : (∫ z, (1 : ℝ) ∂μ) = (volume (ball c ρ)).toReal := by
    simp [μ,Measure.real_def,Measure.restrict_apply MeasurableSet.univ]
  rw [he] at h
  rw [← diskTestRestrictionL2_norm_sq] at h
  exact (Real.le_sqrt (norm_nonneg _) ENNReal.toReal_nonneg).mpr h

/-- Square-summable L² norms give square-summable samples almost surely. -/
theorem ae_summable_sq_of_summable_L2_norms {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (P : Measure Ω) (W : ι → Lp ℝ 2 P) (hW : Summable fun i => ‖W i‖^2) :
    ∀ᵐ ω ∂P, Summable fun i => (W i ω)^2 := by
  let eNN : ι → ℝ≥0 := fun i => ‖W i‖₊^2
  have hNN : Summable eNN := NNReal.summable_coe.1 (by simpa [eNN] using hW)
  have hfiniteNN : (∑' i, (eNN i : ℝ≥0∞)) ≠ ∞ :=
    ENNReal.tsum_coe_ne_top_iff_summable_coe.mpr (NNReal.summable_coe.2 hNN)
  have hnorm i : eLpNorm (W i) 2 P = ENNReal.ofReal ‖W i‖ := by
    rw [Lp.norm_def,ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (W i))]
  have hmoment i : eLpNorm (fun ω => (W i ω)^2) 1 P = (eNN i : ℝ≥0∞) := by
    rw [DOZZ.eLpNorm_sq_eq_eLpNorm_two_sq (fun ω => W i ω) (Lp.aestronglyMeasurable (W i)),hnorm]
    simp [eNN,enorm_eq_nnnorm]
  exact ae_summable_sq_of_tsum_eLpNorm_sq_ne_top (fun i ω => W i ω)
    (by simpa only [hmoment] using hfiniteNN)

/-- The actual normalized cosine coordinates of a completed disk map. -/
noncomputable def diskFourierCosL2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (c : ℂ) (ρ R L : ℝ) (hR : 0 < R)
    (T : Lp ℝ 2 (volume.restrict (ball c ρ)) →L[ℝ] Lp ℝ 2 P) (k : Fin 2 → ℤ) : Lp ℝ 2 P :=
  (DOZZ.torusSobolevWeight k)⁻¹ • T (diskTestRestrictionL2 c ρ (DOZZ.localTorusCosTest R L hR k))

/-- The actual normalized sine coordinates of a completed disk map. -/
noncomputable def diskFourierSinL2 {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (c : ℂ) (ρ R L : ℝ) (hR : 0 < R)
    (T : Lp ℝ 2 (volume.restrict (ball c ρ)) →L[ℝ] Lp ℝ 2 P) (k : Fin 2 → ℤ) : Lp ℝ 2 P :=
  (DOZZ.torusSobolevWeight k)⁻¹ • T (diskTestRestrictionL2 c ρ (DOZZ.localTorusSinTest R L hR k))

/-- Cosine coordinate norm bounds are uniform in the frequency. -/
theorem diskFourierCosL2_norm_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (c : ℂ) (ρ R L : ℝ) (hR : 0 < R)
    (T : Lp ℝ 2 (volume.restrict (ball c ρ)) →L[ℝ] Lp ℝ 2 P) (k : Fin 2 → ℤ) :
    ‖diskFourierCosL2 P c ρ R L hR T k‖ ≤ (DOZZ.torusSobolevWeight k)⁻¹*
      (‖T‖*Real.sqrt (volume (ball c ρ)).toReal) := by
  have hw : 0 ≤ DOZZ.torusSobolevWeight k := by unfold DOZZ.torusSobolevWeight; positivity
  rw [diskFourierCosL2,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hw)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hw)
  exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    (diskTestRestrictionL2_norm_le_area c ρ _ (DOZZ.localTorusCosTest_abs_le_one R L hR k)) (norm_nonneg _))

/-- Sine coordinate norm bounds are uniform in the frequency. -/
theorem diskFourierSinL2_norm_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (c : ℂ) (ρ R L : ℝ) (hR : 0 < R)
    (T : Lp ℝ 2 (volume.restrict (ball c ρ)) →L[ℝ] Lp ℝ 2 P) (k : Fin 2 → ℤ) :
    ‖diskFourierSinL2 P c ρ R L hR T k‖ ≤ (DOZZ.torusSobolevWeight k)⁻¹*
      (‖T‖*Real.sqrt (volume (ball c ρ)).toReal) := by
  have hw : 0 ≤ DOZZ.torusSobolevWeight k := by unfold DOZZ.torusSobolevWeight; positivity
  rw [diskFourierSinL2,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr hw)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hw)
  exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    (diskTestRestrictionL2_norm_le_area c ρ _ (DOZZ.localTorusSinTest_abs_le_one R L hR k)) (norm_nonneg _))

/-- Normalized cosine coordinates have summable squared L² norms. -/
theorem summable_diskFourierCosL2_norm_sq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (c : ℂ) (ρ R L : ℝ) (hR : 0 < R)
    (T : Lp ℝ 2 (volume.restrict (ball c ρ)) →L[ℝ] Lp ℝ 2 P) :
    Summable fun k => ‖diskFourierCosL2 P c ρ R L hR T k‖^2 := by
  let C := ‖T‖*Real.sqrt (volume (ball c ρ)).toReal
  apply Summable.of_nonneg_of_le (fun k => sq_nonneg _)
    (f := fun k => (DOZZ.torusSobolevWeight k)⁻¹^2*C^2)
  · intro k
    rw [← mul_pow]
    apply (sq_le_sq₀ (norm_nonneg _) _).mpr
    exact diskFourierCosL2_norm_le P c ρ R L hR T k
    dsimp only [C,DOZZ.torusSobolevWeight]
    positivity
  · exact DOZZ.summable_torusSobolevWeight_inv_sq.mul_right _

/-- Normalized sine coordinates have summable squared L² norms. -/
theorem summable_diskFourierSinL2_norm_sq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (c : ℂ) (ρ R L : ℝ) (hR : 0 < R)
    (T : Lp ℝ 2 (volume.restrict (ball c ρ)) →L[ℝ] Lp ℝ 2 P) :
    Summable fun k => ‖diskFourierSinL2 P c ρ R L hR T k‖^2 := by
  let C := ‖T‖*Real.sqrt (volume (ball c ρ)).toReal
  apply Summable.of_nonneg_of_le (fun k => sq_nonneg _)
    (f := fun k => (DOZZ.torusSobolevWeight k)⁻¹^2*C^2)
  · intro k
    rw [← mul_pow]
    apply (sq_le_sq₀ (norm_nonneg _) _).mpr
    exact diskFourierSinL2_norm_le P c ρ R L hR T k
    dsimp only [C,DOZZ.torusSobolevWeight]
    positivity
  · exact DOZZ.summable_torusSobolevWeight_inv_sq.mul_right _

section FourierVersion
variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) (c : ℂ) (ρ R L : ℝ) (hR : 0 < R)
variable (T : Lp ℝ 2 (volume.restrict (ball c ρ)) →L[ℝ] Lp ℝ 2 P)

/-- Measurable cosine coordinate representatives on the original sample space. -/
noncomputable def diskFourierCosEval (k : Fin 2 → ℤ) : Ω → ℝ :=
  (Lp.aestronglyMeasurable (diskFourierCosL2 P c ρ R L hR T k)).mk _

/-- Measurable sine coordinate representatives on the original sample space. -/
noncomputable def diskFourierSinEval (k : Fin 2 → ℤ) : Ω → ℝ :=
  (Lp.aestronglyMeasurable (diskFourierSinL2 P c ρ R L hR T k)).mk _

/-- The chosen cosine representatives are measurable. -/
theorem measurable_diskFourierCosEval (k : Fin 2 → ℤ) :
    Measurable (diskFourierCosEval P c ρ R L hR T k) :=
  AEStronglyMeasurable.measurable_mk _

/-- The chosen sine representatives are measurable. -/
theorem measurable_diskFourierSinEval (k : Fin 2 → ℤ) :
    Measurable (diskFourierSinEval P c ρ R L hR T k) :=
  AEStronglyMeasurable.measurable_mk _

/-- Measurable cosine representatives retain the actual L² coordinates. -/
theorem diskFourierCosEval_ae_eq (k : Fin 2 → ℤ) :
    diskFourierCosEval P c ρ R L hR T k =ᵐ[P] ⇑(diskFourierCosL2 P c ρ R L hR T k) :=
  (AEStronglyMeasurable.ae_eq_mk _).symm

/-- Measurable sine representatives retain the actual L² coordinates. -/
theorem diskFourierSinEval_ae_eq (k : Fin 2 → ℤ) :
    diskFourierSinEval P c ρ R L hR T k =ᵐ[P] ⇑(diskFourierSinL2 P c ρ R L hR T k) :=
  (AEStronglyMeasurable.ae_eq_mk _).symm

/-- The cosine sample coordinates are square summable almost surely. -/
theorem ae_summable_diskFourierCosEval_sq :
    ∀ᵐ ω ∂P, Summable fun k => (diskFourierCosEval P c ρ R L hR T k ω)^2 := by
  filter_upwards [ae_summable_sq_of_summable_L2_norms P (diskFourierCosL2 P c ρ R L hR T)
    (summable_diskFourierCosL2_norm_sq P c ρ R L hR T),
    ae_all_iff.mpr (diskFourierCosEval_ae_eq P c ρ R L hR T)] with ω hs he
  simpa only [he] using hs

/-- The sine sample coordinates are square summable almost surely. -/
theorem ae_summable_diskFourierSinEval_sq :
    ∀ᵐ ω ∂P, Summable fun k => (diskFourierSinEval P c ρ R L hR T k ω)^2 := by
  filter_upwards [ae_summable_sq_of_summable_L2_norms P (diskFourierSinL2 P c ρ R L hR T)
    (summable_diskFourierSinL2_norm_sq P c ρ R L hR T),
    ae_all_iff.mpr (diskFourierSinEval_ae_eq P c ρ R L hR T)] with ω hs he
  simpa only [he] using hs

/-- The measurable extended-real cosine square sum. -/
noncomputable def diskFourierCosEnergy (ω : Ω) : ℝ≥0∞ :=
  ∑' k : Fin 2 → ℤ, ENNReal.ofReal ((diskFourierCosEval P c ρ R L hR T k ω)^2)

/-- The measurable extended-real sine square sum. -/
noncomputable def diskFourierSinEnergy (ω : Ω) : ℝ≥0∞ :=
  ∑' k : Fin 2 → ℤ, ENNReal.ofReal ((diskFourierSinEval P c ρ R L hR T k ω)^2)

/-- A measurable full-measure square-summability event for this disk map. -/
def diskFourierGood (ω : Ω) : Prop :=
  diskFourierCosEnergy P c ρ R L hR T ω ≠ ∞ ∧ diskFourierSinEnergy P c ρ R L hR T ω ≠ ∞

/-- The cosine energy sum is measurable. -/
theorem measurable_diskFourierCosEnergy : Measurable (diskFourierCosEnergy P c ρ R L hR T) :=
  Measurable.tsum (fun k => ENNReal.measurable_ofReal.comp ((measurable_diskFourierCosEval P c ρ R L hR T k).pow_const 2))

/-- The sine energy sum is measurable. -/
theorem measurable_diskFourierSinEnergy : Measurable (diskFourierSinEnergy P c ρ R L hR T) :=
  Measurable.tsum (fun k => ENNReal.measurable_ofReal.comp ((measurable_diskFourierSinEval P c ρ R L hR T k).pow_const 2))

/-- The good event is measurable in the original sigma algebra. -/
theorem measurableSet_diskFourierGood : MeasurableSet {ω | diskFourierGood P c ρ R L hR T ω} :=
  (MeasurableSet.preimage ((measurableSet_singleton ∞).compl)
    (measurable_diskFourierCosEnergy P c ρ R L hR T)).inter
    (MeasurableSet.preimage ((measurableSet_singleton ∞).compl)
      (measurable_diskFourierSinEnergy P c ρ R L hR T))

/-- The good event has full probability without changing the sample space. -/
theorem ae_diskFourierGood : ∀ᵐ ω ∂P, diskFourierGood P c ρ R L hR T ω := by
  filter_upwards [ae_summable_diskFourierCosEval_sq P c ρ R L hR T,
    ae_summable_diskFourierSinEval_sq P c ρ R L hR T] with ω hc hs
  exact ⟨hc.tsum_ofReal_ne_top,hs.tsum_ofReal_ne_top⟩

/-- On the good event, the cosine coordinates belong to ℓ². -/
theorem diskFourierCosEval_summable_of_good (ω : Ω) (hω : diskFourierGood P c ρ R L hR T ω) :
    Summable fun k => (diskFourierCosEval P c ρ R L hR T k ω)^2 := by
  have h := ENNReal.summable_toReal hω.1
  simpa only [diskFourierCosEnergy,ENNReal.toReal_ofReal (sq_nonneg _)] using h

/-- On the good event, the sine coordinates belong to ℓ². -/
theorem diskFourierSinEval_summable_of_good (ω : Ω) (hω : diskFourierGood P c ρ R L hR T ω) :
    Summable fun k => (diskFourierSinEval P c ρ R L hR T k ω)^2 := by
  have h := ENNReal.summable_toReal hω.2
  simpa only [diskFourierSinEnergy,ENNReal.toReal_ofReal (sq_nonneg _)] using h

/-- The actual sample's square-summable complex Fourier coordinate vector. -/
noncomputable def diskFourierComplexLp (ω : Ω) (hω : diskFourierGood P c ρ R L hR T ω) :
    lp (fun _ : Fin 2 → ℤ => ℂ) (2 : ℝ≥0∞) := by
  let b : (Fin 2 → ℤ) → ℂ := fun k =>
    (diskFourierCosEval P c ρ R L hR T k ω : ℂ)-Complex.I*(diskFourierSinEval P c ρ R L hR T k ω : ℂ)
  have hpoint k : ‖b k‖^2 = (diskFourierCosEval P c ρ R L hR T k ω)^2+
      (diskFourierSinEval P c ρ R L hR T k ω)^2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [b,Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
    ring
  exact DOZZ.gffComplexLpOfSummableNormSquares b
    (((diskFourierCosEval_summable_of_good P c ρ R L hR T ω hω).add
      (diskFourierSinEval_summable_of_good P c ρ R L hR T ω hω)).congr (fun k => (hpoint k).symm))

/-- Pair the sample coordinates with a complex ℓ² sequence and take the real component. -/
noncomputable def diskFourierPairingCLM (ω : Ω) (hω : diskFourierGood P c ρ R L hR T ω) :
    lp (fun _ : Fin 2 → ℤ => ℂ) (2 : ℝ≥0∞) →L[ℝ] ℝ :=
  Complex.reCLM.comp (ContinuousLinearMap.restrictScalars ℝ
    (innerSL ℂ (diskFourierComplexLp P c ρ R L hR T ω hω)))

/-- The smooth-test Fourier functional on the original sample space. -/
noncomputable def diskFourierDistributionCLM (ω : Ω) (hω : diskFourierGood P c ρ R L hR T ω) :
    TestFn →L[ℝ] ℝ :=
  (diskFourierPairingCLM P c ρ R L hR T ω hω).comp (DOZZ.torusH2WeightedFourierCoeffCLM L)

/-- Finite scalar Fourier pairings are defined for every sample. -/
noncomputable def diskFourierPartialEval (f : TestFn) (s : Finset (Fin 2 → ℤ)) (ω : Ω) : ℝ :=
  s.sum fun k => (DOZZ.torusH2WeightedFourierCoeffCLM L f k).re*diskFourierCosEval P c ρ R L hR T k ω-
    (DOZZ.torusH2WeightedFourierCoeffCLM L f k).im*diskFourierSinEval P c ρ R L hR T k ω

/-- The scalar Fourier limit used to prove evaluation measurability. -/
noncomputable def diskFourierEval (f : TestFn) (ω : Ω) : ℝ :=
  limUnder atTop (fun s => diskFourierPartialEval P c ρ R L hR T f s ω)

/-- Every finite Fourier pairing is measurable. -/
theorem measurable_diskFourierPartialEval (f : TestFn) (s : Finset (Fin 2 → ℤ)) :
    Measurable (diskFourierPartialEval P c ρ R L hR T f s) := by
  classical
  exact Finset.measurable_sum s (fun k _ =>
    (measurable_const.mul (measurable_diskFourierCosEval P c ρ R L hR T k)).sub
      (measurable_const.mul (measurable_diskFourierSinEval P c ρ R L hR T k)))

/-- Fourier limits have measurable scalar evaluations. -/
theorem measurable_diskFourierEval (f : TestFn) : Measurable (diskFourierEval P c ρ R L hR T f) := by
  exact (StronglyMeasurable.limUnder (l := atTop)
    (fun s => (measurable_diskFourierPartialEval P c ρ R L hR T f s).stronglyMeasurable)).measurable

/-- The finite Fourier pairing sums to the continuous sample functional. -/
theorem hasSum_diskFourierPartialEval (f : TestFn) (ω : Ω) (hω : diskFourierGood P c ρ R L hR T ω) :
    HasSum (fun k => (DOZZ.torusH2WeightedFourierCoeffCLM L f k).re*diskFourierCosEval P c ρ R L hR T k ω-
      (DOZZ.torusH2WeightedFourierCoeffCLM L f k).im*diskFourierSinEval P c ρ R L hR T k ω)
      (diskFourierDistributionCLM P c ρ R L hR T ω hω f) := by
  let b := diskFourierComplexLp P c ρ R L hR T ω hω
  let a := DOZZ.torusH2WeightedFourierCoeffCLM L f
  have hh := (lp.hasSum_inner b a).mapL Complex.reCLM
  have he k : (⟪b k,a k⟫_ℂ).re = (DOZZ.torusH2WeightedFourierCoeffCLM L f k).re*diskFourierCosEval P c ρ R L hR T k ω-
      (DOZZ.torusH2WeightedFourierCoeffCLM L f k).im*diskFourierSinEval P c ρ R L hR T k ω := by
    rw [RCLike.inner_apply]
    change (a k*star ((diskFourierCosEval P c ρ R L hR T k ω : ℂ)-
      Complex.I*(diskFourierSinEval P c ρ R L hR T k ω : ℂ))).re = _
    simp [Complex.mul_re,Complex.mul_im]
    ring
  change HasSum (fun k => (⟪b k,a k⟫_ℂ).re) (⟪b,a⟫_ℂ).re at hh
  change HasSum _ (⟪b,a⟫_ℂ).re
  simpa only [he] using hh

/-- On the good event, measurable evaluation equals the continuous Fourier functional. -/
theorem diskFourierEval_eq_distributionCLM_apply (f : TestFn) (ω : Ω)
    (hω : diskFourierGood P c ρ R L hR T ω) : diskFourierEval P c ρ R L hR T f ω =
      diskFourierDistributionCLM P c ρ R L hR T ω hω f := by
  exact (hasSum_diskFourierPartialEval P c ρ R L hR T f ω hω).limUnder_eq

/-- The sample Fourier distribution, set to zero off its measurable full-measure event. -/
noncomputable def diskFourierDistribution (ω : Ω) : TestFn →L[ℝ] ℝ := by
  classical
  exact if hω : diskFourierGood P c ρ R L hR T ω then diskFourierDistributionCLM P c ρ R L hR T ω hω else 0

/-- The selected distribution has measurable evaluations for every global test. -/
theorem measurable_diskFourierDistribution_apply (f : TestFn) :
    Measurable (fun ω => diskFourierDistribution P c ρ R L hR T ω f) := by
  have he : (fun ω => diskFourierDistribution P c ρ R L hR T ω f) =
      {ω | diskFourierGood P c ρ R L hR T ω}.indicator (diskFourierEval P c ρ R L hR T f) := by
    funext ω
    by_cases hω : diskFourierGood P c ρ R L hR T ω
    · rw [diskFourierDistribution,dite_eq_left hω,Set.indicator_of_mem (by exact hω : ω ∈ {ω | diskFourierGood P c ρ R L hR T ω})]
      exact (diskFourierEval_eq_distributionCLM_apply P c ρ R L hR T f ω hω).symm
    · rw [diskFourierDistribution,dite_eq_right hω,Set.indicator_of_notMem (by exact hω : ω ∉ {ω | diskFourierGood P c ρ R L hR T ω})]
      rfl
  rw [he]
  exact (measurable_diskFourierEval P c ρ R L hR T f).indicator (measurableSet_diskFourierGood P c ρ R L hR T)

/-- A finite weighted Fourier evaluation as an actual random L² variable. -/
noncomputable def diskFourierPartialL2 (f : TestFn) (s : Finset (Fin 2 → ℤ)) : Lp ℝ 2 P :=
  s.sum fun k => (DOZZ.torusH2WeightedFourierCoeffCLM L f k).re • diskFourierCosL2 P c ρ R L hR T k-
    (DOZZ.torusH2WeightedFourierCoeffCLM L f k).im • diskFourierSinL2 P c ρ R L hR T k

/-- Finite measurable Fourier evaluations retain their actual L² finite sums. -/
theorem diskFourierPartialEval_ae_eq_partialL2 (f : TestFn) (s : Finset (Fin 2 → ℤ)) :
    diskFourierPartialEval P c ρ R L hR T f s =ᵐ[P] ⇑(diskFourierPartialL2 P c ρ R L hR T f s) := by
  classical
  let a := DOZZ.torusH2WeightedFourierCoeffCLM L f
  let term k : Lp ℝ 2 P := (a k).re • diskFourierCosL2 P c ρ R L hR T k-
    (a k).im • diskFourierSinL2 P c ρ R L hR T k
  have he k : (fun ω => (a k).re*diskFourierCosEval P c ρ R L hR T k ω-
      (a k).im*diskFourierSinEval P c ρ R L hR T k ω) =ᵐ[P] ⇑(term k) := by
    filter_upwards [diskFourierCosEval_ae_eq P c ρ R L hR T k,
      diskFourierSinEval_ae_eq P c ρ R L hR T k,
      Lp.coeFn_smul (a k).re (diskFourierCosL2 P c ρ R L hR T k),
      Lp.coeFn_smul (a k).im (diskFourierSinL2 P c ρ R L hR T k),
      Lp.coeFn_sub ((a k).re • diskFourierCosL2 P c ρ R L hR T k)
        ((a k).im • diskFourierSinL2 P c ρ R L hR T k)] with ω hc hs hre him hsub
    change _ = ((a k).re • diskFourierCosL2 P c ρ R L hR T k-
      (a k).im • diskFourierSinL2 P c ρ R L hR T k) ω
    rw [hsub,Pi.sub_apply,hre,him,Pi.smul_apply,Pi.smul_apply,smul_eq_mul,smul_eq_mul,hc,hs]
  filter_upwards [ae_all_iff.mpr he,Lp.coeFn_fun_finsetSum s term] with ω he hsum
  change (∑ k ∈ s, ((a k).re*diskFourierCosEval P c ρ R L hR T k ω-
      (a k).im*diskFourierSinEval P c ρ R L hR T k ω)) = (∑ k ∈ s,term k) ω
  rw [hsum]
  exact Finset.sum_congr rfl (fun k _ => he k)

/-- Normalized weighted finite coordinates equal the actual cutoff Fourier test evaluations. -/
theorem diskFourierPartialL2_eq_completedPartialTest (hL : 0 < L) (hbox : L/2 = R+2)
    (f : TestFn) (hf : Function.support f ⊆ ball (0 : ℂ) (R-1)) (s : Finset (Fin 2 → ℤ)) :
    diskFourierPartialL2 P c ρ R L hR T f s =
      T (diskTestRestrictionL2 c ρ (DOZZ.equatorLocalFourierPartialTest R L hR f s)) := by
  change (∑ k ∈ s, ((DOZZ.torusH2WeightedFourierCoeffCLM L f k).re • diskFourierCosL2 P c ρ R L hR T k-
      (DOZZ.torusH2WeightedFourierCoeffCLM L f k).im • diskFourierSinL2 P c ρ R L hR T k)) =
      T ((diskTestRestrictionLinearMap c ρ) (DOZZ.equatorLocalFourierPartialTest R L hR f s))
  rw [DOZZ.equatorLocalFourierPartialTest,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [DOZZ.torusH2WeightedFourierCoeffCLM_apply L (R-1) hL (by linarith) f hf k]
  simp only [diskFourierCosL2,diskFourierSinL2,Complex.smul_re,Complex.smul_im,
    smul_eq_mul,smul_smul,map_sub,map_smul]
  have hw : DOZZ.torusSobolevWeight k ≠ 0 := by unfold DOZZ.torusSobolevWeight; positivity
  have hr : DOZZ.torusSobolevWeight k*(UnitAddTorus.mFourierCoeff (DOZZ.torusPeriodizationLp L f) k).re*
      (DOZZ.torusSobolevWeight k)⁻¹ = (UnitAddTorus.mFourierCoeff (DOZZ.torusPeriodizationLp L f) k).re := by
    field_simp
  have hi : DOZZ.torusSobolevWeight k*(UnitAddTorus.mFourierCoeff (DOZZ.torusPeriodizationLp L f) k).im*
      (DOZZ.torusSobolevWeight k)⁻¹ = (UnitAddTorus.mFourierCoeff (DOZZ.torusPeriodizationLp L f) k).im := by
    field_simp
  rw [hr,hi]
  rfl

end FourierVersion


/-- Cutoff Fourier tests approximate every supported test in disk area L². -/
theorem tendsto_diskRestriction_fourierPartialTest (c : ℂ) (ρ R L : ℝ)
    (hR : 0 < R) (hL : 0 < L) (hbox : L/2 = R+2)
    (f : TestFn) (hf : Function.support f ⊆ ball (0 : ℂ) (R-1)) :
    Tendsto (fun s : Finset (Fin 2 → ℤ) => diskTestRestrictionL2 c ρ (DOZZ.equatorLocalFourierPartialTest R L hR f s))
      atTop (𝓝 (diskTestRestrictionL2 c ρ f)) := by
  let err s := DOZZ.torusRealFourierPartialSum L f s-
    DOZZ.torusFourierRealPartCLM (DOZZ.torusPeriodizationLp L f)
  have he : Tendsto err atTop (𝓝 0) := by
    simpa only [sub_self] using (DOZZ.torusRealFourierPartialSum_tendsto L f).sub_const
      (DOZZ.torusFourierRealPartCLM (DOZZ.torusPeriodizationLp L f))
  have hn : Tendsto (fun s => L^2*‖err s‖^2) atTop (𝓝 0) := by
    simpa only [norm_zero,zero_pow (by norm_num : (2 : ℕ) ≠ 0),mul_zero] using
      tendsto_const_nhds.mul (he.norm.pow 2)
  have hb s : ‖diskTestRestrictionL2 c ρ (DOZZ.equatorLocalFourierPartialTest R L hR f s)-
      diskTestRestrictionL2 c ρ f‖^2 ≤ L^2*‖err s‖^2 := by
    rw [← diskTestRestrictionL2_sub,diskTestRestrictionL2_norm_sq]
    let g := DOZZ.equatorLocalFourierPartialTest R L hR f s-f
    have hg : Integrable (fun z : ℂ => (g z)^2) volume :=
      (g.continuous.memLp_of_hasCompactSupport g.hasCompactSupport).integrable_sq
    exact (integral_mono_measure Measure.restrict_le_self (ae_of_all _ (fun z => sq_nonneg (g z))) hg).trans
      (DOZZ.integral_sq_equatorLocalFourierPartialTest_sub_le R L hR hL hbox f s hf)
  have hsq : Tendsto (fun s => ‖diskTestRestrictionL2 c ρ (DOZZ.equatorLocalFourierPartialTest R L hR f s)-
      diskTestRestrictionL2 c ρ f‖^2) atTop (𝓝 0) :=
    squeeze_zero (fun s => sq_nonneg _) hb hn
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hh

/-- Any bounded completed disk map preserves cutoff Fourier approximation. -/
theorem tendsto_completed_disk_fourierPartialTest {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (c : ℂ) (ρ R L : ℝ) (hR : 0 < R) (hL : 0 < L) (hbox : L/2 = R+2)
    (T : Lp ℝ 2 (volume.restrict (ball c ρ)) →L[ℝ] Lp ℝ 2 P)
    (f : TestFn) (hf : Function.support f ⊆ ball (0 : ℂ) (R-1)) :
    Tendsto (fun s : Finset (Fin 2 → ℤ) => T (diskTestRestrictionL2 c ρ (DOZZ.equatorLocalFourierPartialTest R L hR f s)))
      atTop (𝓝 (T (diskTestRestrictionL2 c ρ f))) :=
  T.continuous.tendsto _ |>.comp (tendsto_diskRestriction_fourierPartialTest c ρ R L hR hL hbox f hf)


/-- The selected Fourier distribution represents the actual completed map on supported tests. -/
theorem diskFourierDistribution_apply_ae_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (c : ℂ) (ρ R L : ℝ) (hR : 0 < R) (hL : 0 < L) (hbox : L/2 = R+2)
    (T : Lp ℝ 2 (volume.restrict (ball c ρ)) →L[ℝ] Lp ℝ 2 P)
    (f : TestFn) (hf : Function.support f ⊆ ball (0 : ℂ) (R-1)) :
    (fun ω => diskFourierDistribution P c ρ R L hR T ω f) =ᵐ[P]
      ⇑(T (diskTestRestrictionL2 c ρ f)) := by
  have hLp : Tendsto (diskFourierPartialL2 P c ρ R L hR T f) atTop
      (𝓝 (T (diskTestRestrictionL2 c ρ f))) := by
    change Tendsto (fun s => diskFourierPartialL2 P c ρ R L hR T f s) atTop _
    simp_rw [diskFourierPartialL2_eq_completedPartialTest P c ρ R L hR T hL hbox f hf]
    exact tendsto_completed_disk_fourierPartialTest P c ρ R L hR hL hbox T f hf
  obtain ⟨s,hs,hAE⟩ := (tendstoInMeasure_of_tendsto_Lp hLp).exists_seq_tendsto_ae'
  filter_upwards [hAE,ae_diskFourierGood P c ρ R L hR T,
    ae_all_iff.mpr (fun n => diskFourierPartialEval_ae_eq_partialL2 P c ρ R L hR T f (s n))] with ω hLpω hω he
  have hsum := hasSum_diskFourierPartialEval P c ρ R L hR T f ω hω
  have hsel : diskFourierDistribution P c ρ R L hR T ω f =
      diskFourierDistributionCLM P c ρ R L hR T ω hω f := by
    rw [diskFourierDistribution,dite_eq_left hω]
  rw [hsel]
  have hpoint : Tendsto (fun n => diskFourierPartialEval P c ρ R L hR T f (s n) ω) atTop
      (𝓝 (diskFourierDistributionCLM P c ρ R L hR T ω hω f)) := hsum.comp hs
  exact tendsto_nhds_unique hpoint (hLpω.congr (fun n => (he n).symm))

end DOZZ.Proofs

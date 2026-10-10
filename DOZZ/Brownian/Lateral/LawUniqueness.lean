/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Lateral.RadialProjection
public import DOZZ.GMC.EquatorGFFChaosTransportLaw
public import DOZZ.GMC.CircleAverageLimits
public import DOZZ.Statements.Brownian.IsLateralGMCOf
public import Mathlib.Topology.Order.LiminfLimsup

/-!
# Uniqueness of the lateral projection law

A common measurable reconstruction of the radial path uses rational circle averages.
For two given models, successive subsequence extraction makes the same annular test
approximations converge almost surely in both. Their limsup is consequently a common
function of the field evaluations. The joint field/GMC law then transports the literal
polar projection. No inverse chaos moment or change of regularization is used.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Distributions

namespace DOZZ.Proofs

/-- Successive extraction preserves almost sure convergence in both probability spaces. -/
theorem exists_common_subsequence_tendsto_ae
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω')
    (f : ℕ → Ω → ℝ) (g : Ω → ℝ) (f' : ℕ → Ω' → ℝ) (g' : Ω' → ℝ)
    (h : TendstoInMeasure P f atTop g) (h' : TendstoInMeasure P' f' atTop g') :
    ∃ k : ℕ → ℕ, StrictMono k ∧
      (∀ᵐ ω ∂P, Tendsto (fun n => f (k n) ω) atTop (𝓝 (g ω))) ∧
      (∀ᵐ ω ∂P', Tendsto (fun n => f' (k n) ω) atTop (𝓝 (g' ω))) := by
  obtain ⟨i, hi, hia⟩ := h.exists_seq_tendsto_ae
  obtain ⟨j, hj, hja⟩ := (h'.comp hi.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨i ∘ j, hi.comp hj, ?_, hja⟩
  filter_upwards [hia] with ω hω
  exact hω.comp hj.tendsto_atTop

/-- An annular test approximation converges in measure to any authored circle witness. -/
theorem circle_test_approximation_tendstoInMeasure
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hc : IsCircleAverage P X Xc) (x : ℂ) (r : ℝ)
    (f : ℕ → TestFn) (hf : Tendsto (fun n => circleEnergyGap x r (f n)) atTop (𝓝 0)) :
    TendstoInMeasure P (fun n ω => X ω (f n)) atTop (fun ω => Xc ω x r) := by
  apply tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  change Tendsto (fun n => eLpNorm (fun ω => X ω (f n) - Xc ω x r) 2 P) atTop (𝓝 0)
  have hcomm n : eLpNorm (fun ω => X ω (f n) - Xc ω x r) 2 P =
      eLpNorm (fun ω => Xc ω x r - X ω (f n)) 2 P := eLpNorm_sub_comm _ _ _ _
  simpa only [hcomm] using hc.2.2 x r f hf

/-- One circle coordinate is the same measurable function of field evaluations in both models.
The reconstruction function may depend on the pair of models, but is shared between them. -/
theorem exists_common_circle_field_proxy
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hc : IsCircleAverage P X Xc)
    (P' : Measure Ω') (X' : Ω' → Distr) (Xc' : Ω' → ℂ → ℝ → ℝ)
    (hc' : IsCircleAverage P' X' Xc') (x : ℂ) (r : ℝ) :
    ∃ G : (TestFn → ℝ) → ℝ, Measurable G ∧
      (fun ω => G (fun f => X ω f)) =ᵐ[P] (fun ω => Xc ω x r) ∧
      (fun ω => G (fun f => X' ω f)) =ᵐ[P'] (fun ω => Xc' ω x r) := by
  obtain ⟨f, _, _, hf⟩ := exists_testFn_circleEnergyGap_tendsto_zero x r
  obtain ⟨k, -, hk, hk'⟩ := exists_common_subsequence_tendsto_ae P P'
    (fun n ω => X ω (f n)) (fun ω => Xc ω x r)
    (fun n ω => X' ω (f n)) (fun ω => Xc' ω x r)
    (circle_test_approximation_tendstoInMeasure P X Xc hc x r f hf)
    (circle_test_approximation_tendstoInMeasure P' X' Xc' hc' x r f hf)
  let G : (TestFn → ℝ) → ℝ := fun e => limsup (fun n => e (f (k n))) atTop
  refine ⟨G, Measurable.limsup (fun n => measurable_pi_apply _), ?_, ?_⟩
  · filter_upwards [hk] with ω hω
    exact hω.limsup_eq
  · filter_upwards [hk'] with ω hω
    exact hω.limsup_eq

/-- Rational evaluations determine a full continuous radial path. -/
def radialRationalCode (A : TwoSidedPath) : ℚ → ℝ := fun q => A (q : ℝ)

/-- Encoding a path by its rational evaluations is measurable. -/
theorem measurable_radialRationalCode : Measurable radialRationalCode :=
  Measurable.of_eval fun q => ContinuousMap.measurable_eval (q : ℝ)

/-- Equality on the dense rational set is equality of continuous paths. -/
theorem radialRationalCode_injective : Function.Injective radialRationalCode := by
  intro A A' h
  apply ContinuousMap.ext
  exact congrFun (Rat.denseRange_cast.equalizer A.continuous A'.continuous h)

/-- The path code has a measurable inverse on its image. -/
theorem radialRationalCode_measurableEmbedding : MeasurableEmbedding radialRationalCode :=
  measurable_radialRationalCode.measurableEmbedding radialRationalCode_injective

/-- Reconstruct a continuous path from its rational code, with a measurable default off the image. -/
noncomputable def radialPathFromRationalCode : (ℚ → ℝ) → TwoSidedPath :=
  radialRationalCode_measurableEmbedding.invFun

/-- Reconstruction is measurable, including on codes which do not extend continuously. -/
theorem measurable_radialPathFromRationalCode : Measurable radialPathFromRationalCode :=
  radialRationalCode_measurableEmbedding.measurable_invFun

/-- Every actual continuous path is reconstructed exactly. -/
theorem radialPathFromRationalCode_code (A : TwoSidedPath) :
    radialPathFromRationalCode (radialRationalCode A) = A :=
  radialRationalCode_measurableEmbedding.leftInverse_invFun A

/-- The two radial witnesses admit a shared measurable reconstruction from their fields.
Only countably many null sets are joined; continuity then identifies the entire paths. -/
theorem exists_common_radial_field_proxy
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (X : Ω → Distr) (A : Ω → TwoSidedPath)
    (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (hA : ∀ s : ℝ, ∀ᵐ ω ∂P, A ω s = Xc ω 0 s)
    (P' : Measure Ω') (X' : Ω' → Distr) (A' : Ω' → TwoSidedPath)
    (Xc' : Ω' → ℂ → ℝ → ℝ) (hc' : IsCircleAverage P' X' Xc')
    (hA' : ∀ s : ℝ, ∀ᵐ ω ∂P', A' ω s = Xc' ω 0 s) :
    ∃ G : (TestFn → ℝ) → TwoSidedPath, Measurable G ∧
      (fun ω => G (fun f => X ω f)) =ᵐ[P] A ∧
      (fun ω => G (fun f => X' ω f)) =ᵐ[P'] A' := by
  classical
  have hproxy := fun q : ℚ =>
    exists_common_circle_field_proxy P X Xc hc P' X' Xc' hc' 0 (q : ℝ)
  choose g hg he he' using hproxy
  let G : (TestFn → ℝ) → TwoSidedPath := fun e =>
    radialPathFromRationalCode (fun q => g q e)
  have hG : Measurable G := measurable_radialPathFromRationalCode.comp
    (Measurable.of_eval hg)
  have hcode : ∀ᵐ ω ∂P, (fun q : ℚ => g q (fun f => X ω f)) = radialRationalCode (A ω) := by
    have heall := ae_all_iff.mpr he
    have hAall := ae_all_iff.mpr (fun q : ℚ => hA (q : ℝ))
    filter_upwards [heall, hAall] with ω hω ha
    funext q
    exact (hω q).trans (ha q).symm
  have hcode' : ∀ᵐ ω ∂P', (fun q : ℚ => g q (fun f => X' ω f)) = radialRationalCode (A' ω) := by
    have heall := ae_all_iff.mpr he'
    have hAall := ae_all_iff.mpr (fun q : ℚ => hA' (q : ℝ))
    filter_upwards [heall, hAall] with ω hω ha
    funext q
    exact (hω q).trans (ha q).symm
  refine ⟨G, hG, ?_, ?_⟩
  · filter_upwards [hcode] with ω hω
    exact (congrArg radialPathFromRationalCode hω).trans (radialPathFromRationalCode_code _)
  · filter_upwards [hcode'] with ω hω
    exact (congrArg radialPathFromRationalCode hω).trans (radialPathFromRationalCode_code _)

/-- A radial witness tied to a circle average is determined by the field up to null sets.
This is joint measurability on the original probability space, rather than an assertion
about only individual radial coordinates. -/
theorem radial_circle_witness_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (A : Ω → TwoSidedPath)
    (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (hA : ∀ s : ℝ, ∀ᵐ ω ∂P, A ω s = Xc ω 0 s) : AEMeasurable A P := by
  apply aemeasurable_twoSidedPath_of_eval
  intro s
  exact (hc.2.1 0 s).aemeasurable.congr ((hA s).mono fun ω hω => hω.symm)

/-- The field-and-radial-path input to transport is almost everywhere measurable. -/
theorem radial_GMC_pair_aemeasurable
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) (A : Ω → TwoSidedPath)
    (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (hA : ∀ s : ℝ, ∀ᵐ ω ∂P, A ω s = Xc ω 0 s) :
    AEMeasurable (fun ω => (A ω, M ω)) P := by
  exact (radial_circle_witness_aemeasurable P X A Xc hc hA).prodMk
    (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ2 M hM)

/-- Equality of the joint field/GMC law transports any nonnegative test of the radial path
and chaos. Both witnesses use the same measurable field reconstruction. -/
theorem equatorGFF_radial_GMC_lintegral_law
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (P' : Measure Ω') (X' : Ω' → Distr) (hX' : IsEquatorGFF P' X')
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (M' : Ω' → Measure ℂ) (hM' : IsGMCOf P' X' γ M')
    (A : Ω → TwoSidedPath) (Xc : Ω → ℂ → ℝ → ℝ)
    (hc : IsCircleAverage P X Xc) (hA : ∀ s : ℝ, ∀ᵐ ω ∂P, A ω s = Xc ω 0 s)
    (A' : Ω' → TwoSidedPath) (Xc' : Ω' → ℂ → ℝ → ℝ)
    (hc' : IsCircleAverage P' X' Xc') (hA' : ∀ s : ℝ, ∀ᵐ ω ∂P', A' ω s = Xc' ω 0 s)
    (W : TwoSidedPath → Measure ℂ → ℝ≥0∞)
    (hW : Measurable (fun p : TwoSidedPath × Measure ℂ => W p.1 p.2)) :
    (∫⁻ ω, W (A ω) (M ω) ∂P) = ∫⁻ ω, W (A' ω) (M' ω) ∂P' := by
  obtain ⟨G, hG, he, he'⟩ := exists_common_radial_field_proxy
    P X A Xc hc hA P' X' A' Xc' hc' hA'
  let H : (TestFn → ℝ) → Measure ℂ → ℝ≥0∞ := fun e μ => W (G e) μ
  have hH : Measurable (fun p : (TestFn → ℝ) × Measure ℂ => H p.1 p.2) :=
    hW.comp ((hG.comp measurable_fst).prodMk measurable_snd)
  calc
    _ = ∫⁻ ω, H (fun f => X ω f) (M ω) ∂P := by
      apply lintegral_congr_ae
      filter_upwards [he] with ω hω
      change W (A ω) (M ω) = W (G (fun f => X ω f)) (M ω)
      rw [hω]
    _ = ∫⁻ ω, H (fun f => X' ω f) (M' ω) ∂P' :=
      equatorGFF_GMC_law_transport P X hX P' X' hX' γ hγ hγ2 M hM M' hM' H hH
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [he'] with ω hω
      change W (G (fun f => X' ω f)) (M' ω) = W (A' ω) (M' ω)
      rw [hω]

/-- The entire continuous radial path and chaos have a common joint law. The
path carrier is retained, so every measurable path functional is covered. -/
theorem equatorGFF_radial_GMC_map_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (P' : Measure Ω') (X' : Ω' → Distr) (hX' : IsEquatorGFF P' X')
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (M' : Ω' → Measure ℂ) (hM' : IsGMCOf P' X' γ M')
    (A : Ω → TwoSidedPath) (Xc : Ω → ℂ → ℝ → ℝ)
    (hc : IsCircleAverage P X Xc) (hA : ∀ s : ℝ, ∀ᵐ ω ∂P, A ω s = Xc ω 0 s)
    (A' : Ω' → TwoSidedPath) (Xc' : Ω' → ℂ → ℝ → ℝ)
    (hc' : IsCircleAverage P' X' Xc') (hA' : ∀ s : ℝ, ∀ᵐ ω ∂P', A' ω s = Xc' ω 0 s) :
    P.map (fun ω => (A ω, M ω)) = P'.map (fun ω => (A' ω, M' ω)) := by
  have hm := radial_GMC_pair_aemeasurable P X hX γ hγ hγ2 M hM A Xc hc hA
  have hm' := radial_GMC_pair_aemeasurable P' X' hX' γ hγ hγ2 M' hM' A' Xc' hc' hA'
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply_of_aemeasurable hm hS, Measure.map_apply_of_aemeasurable hm' hS]
  have h := equatorGFF_radial_GMC_lintegral_law P X hX P' X' hX' γ hγ hγ2
    M hM M' hM' A Xc hc hA A' Xc' hc' hA'
    (fun A μ => S.indicator (fun _ => 1) (A, μ))
    (measurable_const.indicator hS)
  have he : (fun ω => S.indicator (fun _ => (1 : ℝ≥0∞)) (A ω, M ω)) =
      ((fun ω => (A ω, M ω)) ⁻¹' S).indicator (fun _ => 1) := by
    funext ω
    by_cases hω : (A ω, M ω) ∈ S <;> simp [hω]
  have he' : (fun ω => S.indicator (fun _ => (1 : ℝ≥0∞)) (A' ω, M' ω)) =
      ((fun ω => (A' ω, M' ω)) ⁻¹' S).indicator (fun _ => 1) := by
    funext ω
    by_cases hω : (A' ω, M' ω) ∈ S <;> simp [hω]
  rw [he, he'] at h
  change (∫⁻ ω, ((fun ω => (A ω, M ω)) ⁻¹' S).indicator 1 ω ∂P) =
    (∫⁻ ω, ((fun ω => (A' ω, M' ω)) ⁻¹' S).indicator 1 ω ∂P') at h
  rw [lintegral_indicator_one₀ (hm.nullMeasurable hS),
    lintegral_indicator_one₀ (hm'.nullMeasurable hS)] at h
  exact h

/-- Extend a finite plane measure to a total measurable operation on all plane measures.
Infinite measures are replaced by zero only outside the finite carrier. -/
noncomputable def finitePlaneMeasureValue (μ : Measure ℂ) : Measure ℂ := by
  classical
  exact if μ univ < ⊤ then μ else 0

/-- Totalization always produces a finite measure. -/
theorem finitePlaneMeasureValue_finite (μ : Measure ℂ) :
    IsFiniteMeasure (finitePlaneMeasureValue μ) := by
  classical
  by_cases h : μ univ < ⊤
  · exact ⟨by simpa only [finitePlaneMeasureValue, ite_eq_left h] using h⟩
  · simp only [finitePlaneMeasureValue, ite_eq_right h]
    infer_instance

/-- Pack the totalized value in the measurable finite-measure carrier. -/
noncomputable def finitePlaneMeasureOrZero (μ : Measure ℂ) : FiniteMeasure ℂ :=
  ⟨finitePlaneMeasureValue μ, finitePlaneMeasureValue_finite μ⟩

/-- The totalized finite measure is measurable in the original measure. -/
theorem measurable_finitePlaneMeasureOrZero : Measurable finitePlaneMeasureOrZero := by
  classical
  have hs : MeasurableSet {μ : Measure ℂ | μ univ < ⊤} :=
    measurableSet_lt (Measure.measurable_coe MeasurableSet.univ) measurable_const
  apply Measurable.subtype_mk
  change Measurable (fun μ : Measure ℂ => if μ univ < ⊤ then μ else 0)
  exact Measurable.ite hs measurable_id measurable_const

/-- Totalization preserves every finite plane measure exactly. -/
theorem finitePlaneMeasureOrZero_eq (μ : Measure ℂ) (hμ : IsFiniteMeasure μ) :
    (finitePlaneMeasureOrZero μ : Measure ℂ) = μ := by
  simp only [finitePlaneMeasureOrZero, finitePlaneMeasureValue,
    ite_eq_left hμ.measure_univ_lt_top, FiniteMeasure.toMeasure_mk]

/-- The actual radial projection has a measurable extension to all path/measure inputs. -/
noncomputable def totalizedLateralProjection (γ : ℝ) (A : TwoSidedPath)
    (μ : Measure ℂ) : Measure ℝ :=
  lateralProjectedGMC γ A (finitePlaneMeasureOrZero μ : Measure ℂ)

/-- Joint measurability of the totalized lateral projection. -/
theorem measurable_totalizedLateralProjection (γ : ℝ) :
    Measurable (fun p : TwoSidedPath × Measure ℂ => totalizedLateralProjection γ p.1 p.2) := by
  have hi : Measurable (fun p : TwoSidedPath × Measure ℂ =>
      ((γ, p.1), finitePlaneMeasureOrZero p.2)) :=
    (measurable_const.prodMk measurable_fst).prodMk
      (measurable_finitePlaneMeasureOrZero.comp measurable_snd)
  change Measurable ((fun p : (ℝ × TwoSidedPath) × FiniteMeasure ℂ =>
    lateralProjectedGMC p.1.1 p.1.2 (p.2 : Measure ℂ)) ∘
    (fun p : TwoSidedPath × Measure ℂ => ((γ, p.1), finitePlaneMeasureOrZero p.2)))
  exact Measurable.comp measurable_lateralProjectedGMC_finite hi

/-- On a finite chaos, the extension is the literal projection `DOZZ.lateralProjectedGMC`. -/
theorem totalizedLateralProjection_eq (γ : ℝ) (A : TwoSidedPath)
    (μ : Measure ℂ) (hμ : IsFiniteMeasure μ) :
    totalizedLateralProjection γ A μ = lateralProjectedGMC γ A μ := by
  unfold totalizedLateralProjection
  rw [finitePlaneMeasureOrZero_eq μ hμ]

/-- Joint radial/GMC law transport identifies the whole projected random measure law.
Finiteness of the underlying GMC suffices even though the projected measure need not be finite. -/
theorem equatorGFF_radial_projection_map_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (P' : Measure Ω') (X' : Ω' → Distr) (hX' : IsEquatorGFF P' X')
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (M' : Ω' → Measure ℂ) (hM' : IsGMCOf P' X' γ M')
    (A : Ω → TwoSidedPath) (Xc : Ω → ℂ → ℝ → ℝ)
    (hc : IsCircleAverage P X Xc) (hA : ∀ s : ℝ, ∀ᵐ ω ∂P, A ω s = Xc ω 0 s)
    (A' : Ω' → TwoSidedPath) (Xc' : Ω' → ℂ → ℝ → ℝ)
    (hc' : IsCircleAverage P' X' Xc') (hA' : ∀ s : ℝ, ∀ᵐ ω ∂P', A' ω s = Xc' ω 0 s) :
    P.map (fun ω => lateralProjectedGMC γ (A ω) (M ω)) =
      P'.map (fun ω => lateralProjectedGMC γ (A' ω) (M' ω)) := by
  let T : TwoSidedPath × Measure ℂ → Measure ℝ := fun p => totalizedLateralProjection γ p.1 p.2
  have hT : Measurable T := measurable_totalizedLateralProjection γ
  have hm := radial_GMC_pair_aemeasurable P X hX γ hγ hγ2 M hM A Xc hc hA
  have hm' := radial_GMC_pair_aemeasurable P' X' hX' γ hγ hγ2 M' hM' A' Xc' hc' hA'
  have hcomp : (fun ω => lateralProjectedGMC γ (A ω) (M ω)) =
      T ∘ (fun ω => (A ω, M ω)) := by
    funext ω
    exact (totalizedLateralProjection_eq γ (A ω) (M ω) (hM.1 ω)).symm
  have hcomp' : (fun ω => lateralProjectedGMC γ (A' ω) (M' ω)) =
      T ∘ (fun ω => (A' ω, M' ω)) := by
    funext ω
    exact (totalizedLateralProjection_eq γ (A' ω) (M' ω) (hM'.1 ω)).symm
  rw [hcomp, hcomp', ← AEMeasurable.map_map_of_aemeasurable hT.aemeasurable hm,
    ← AEMeasurable.map_map_of_aemeasurable hT.aemeasurable hm',
    equatorGFF_radial_GMC_map_eq P X hX P' X' hX' γ hγ hγ2
      M hM M' hM' A Xc hc hA A' Xc' hc' hA']

/-- Any two source lateral projections have the same measure-valued law. The radial witness is fixed
by its circle averages; the GMC input uses its characterization `DOZZ.IsGMCOf`. -/
theorem sourceLateralProjection_map_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (X : Ω → Distr) (M : Ω → Measure ℂ) (Z : Ω → Measure ℝ)
    (X' : Ω' → Distr) (M' : Ω' → Measure ℂ) (Z' : Ω' → Measure ℝ)
    (hZ : IsSourceLateralProjection P X γ M Z)
    (hZ' : IsSourceLateralProjection P' X' γ M' Z') :
    P.map Z = P'.map Z' := by
  rcases hZ with ⟨hX, hM, A, ⟨Xc, hc, hAc⟩, -, -, -, -, -, -, -, he⟩
  rcases hZ' with ⟨hX', hM', A', ⟨Xc', hc', hAc'⟩, -, -, -, -, -, -, -, he'⟩
  rw [Measure.map_congr he, Measure.map_congr he']
  exact equatorGFF_radial_projection_map_eq P X hX P' X' hX' γ hγ hγ2
    M hM M' hM' A Xc hc hAc A' Xc' hc' hAc'

/-- The circle-average lateral projection has the same law across characterized field/GMC
models. See [KRV, §3.1]. -/
theorem isLateralGMCOf_map_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') (γ : ℝ) (Z : Ω → Measure ℝ) (Z' : Ω' → Measure ℝ)
    (hZ : IsLateralGMCOf P γ Z) (hZ' : IsLateralGMCOf P' γ Z') :
    P.map Z = P'.map Z' := by
  obtain ⟨X, M, hS⟩ := hZ.2.2.2.2.2.2.2.2
  obtain ⟨X', M', hS'⟩ := hZ'.2.2.2.2.2.2.2.2
  exact sourceLateralProjection_map_eq P P' γ hZ.1 hZ.2.1 X M Z X' M' Z' hS hS'

/-- Arbitrary nonnegative measurable tests of the lateral measure have a common expectation.
The assertion permits infinite values and therefore also applies to inverse powers before
their finiteness is proved. -/
theorem isLateralGMCOf_lintegral_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (P' : Measure Ω') (γ : ℝ) (Z : Ω → Measure ℝ) (Z' : Ω' → Measure ℝ)
    (hZ : IsLateralGMCOf P γ Z) (hZ' : IsLateralGMCOf P' γ Z')
    (W : Measure ℝ → ℝ≥0∞) (hW : Measurable W) :
    (∫⁻ ω, W (Z ω) ∂P) = ∫⁻ ω, W (Z' ω) ∂P' := by
  rw [← lintegral_map' hW.aemeasurable hZ.2.2.2.1,
    ← lintegral_map' hW.aemeasurable hZ'.2.2.2.1, isLateralGMCOf_map_eq P P' γ Z Z' hZ hZ']



end DOZZ.Proofs

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.GMC.SharpMoments.WeightedLocalSufficiency
public import DOZZ.GMC.Assembly.AdmissibleGMC

/-! # Location transfer of boundedly weighted small-disk moments for limiting chaos

Cutoff integrals of bounded Borel functions with bounded support converge in `L¹`, so boundedly
weighted cutoff masses of a disk converge in probability. Their moments of every positive
subcritical order are uniformly bounded beyond that order, hence converge. The finite-cutoff
location transfer of weighted masses therefore passes to every `IsGMCOf` limit. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Cutoff integrals of a bounded Borel function supported in a closed disk converge in `L¹` to
the integral against any `IsGMCOf` version. -/
theorem regularizedGMC_integral_l1_tendsto
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (f : ℂ → ℝ) (hf : Measurable f) (Lb : ℝ) (hfb : ∀ x, |f x| ≤ Lb) (R : ℝ)
    (hfR : ∀ x ∉ Metric.closedBall (0 : ℂ) R, f x = 0) :
    Tendsto (fun r => ∫⁻ ω, ENNReal.ofReal
      |∫ x, f x ∂regularizedGMC P Xc γ r ω - ∫ x, f x ∂M ω| ∂P) atTop (𝓝 0) := by
  classical
  let I : Set ℝ := {γ}
  let K : Set ℂ := Metric.closedBall (0 : ℂ) R
  have hExists : ∀ η ∈ Set.Ioo (0 : ℝ) 2, ∃ N : Ω → Measure ℂ, IsGMCOf P X η N := by
    intro η hη
    obtain ⟨_, N, _, hN⟩ := equatorGFF_circle_average_GMC_exists P X hX η hη.1 hη.2
    exact ⟨N, hN⟩
  let Mfam : ℝ → Ω → Measure ℂ := fun η =>
    if hη : η ∈ Set.Ioo (0 : ℝ) 2 then Classical.choose (hExists η hη) else 0
  have hI : IsCompact I := by simp [I]
  have hI2 : I ⊆ Set.Ioo (0 : ℝ) 2 := by
    intro η hη
    have hη' : η = γ := by simpa [I] using hη
    simpa [hη'] using ⟨hγ, hγ2⟩
  have hK : IsCompact K := isCompact_closedBall _ _
  have hMfam : ∀ η ∈ Set.Ioo (0 : ℝ) 2, IsGMCOf P X η (Mfam η) := by
    intro η hη
    simp only [Mfam, dite_eq_left hη]
    exact Classical.choose_spec (hExists η hη)
  have hUnique : ∀ᵐ ω ∂P, M ω = Mfam γ ω :=
    equatorGFF_GMC_unique_ae P X hX γ M (Mfam γ) hM (hMfam γ ⟨hγ, hγ2⟩)
  let S : ℝ → ℝ≥0∞ := fun r => ⨆ η ∈ I, ⨆ (g : ℂ → ℝ) (_ : Measurable g)
      (_ : ∀ x, |g x| ≤ Lb) (_ : ∀ x ∉ K, g x = 0),
      ∫⁻ ω, ENNReal.ofReal
        |∫ x, g x ∂regularizedGMC P Xc η r ω - ∫ x, g x ∂Mfam η ω| ∂P
  have hS : Tendsto S atTop (𝓝 0) :=
    equatorGFF_GMC_uniform_L1 P X hX Xc hXc Mfam hMfam I hI hI2 K hK Lb
  have hbound (r : ℝ) :
      ∫⁻ ω, ENNReal.ofReal
        |∫ x, f x ∂regularizedGMC P Xc γ r ω - ∫ x, f x ∂M ω| ∂P ≤ S r := by
    have hEq :
        ∫⁻ ω, ENNReal.ofReal |∫ x, f x ∂regularizedGMC P Xc γ r ω - ∫ x, f x ∂M ω| ∂P =
        ∫⁻ ω, ENNReal.ofReal
          |∫ x, f x ∂regularizedGMC P Xc γ r ω - ∫ x, f x ∂Mfam γ ω| ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hUnique] with ω hω
      rw [hω]
    rw [hEq]
    refine le_iSup_of_le γ ?_
    refine le_iSup_of_le (Set.mem_singleton γ) ?_
    refine le_iSup_of_le f ?_
    refine le_iSup_of_le hf ?_
    refine le_iSup_of_le hfb ?_
    exact le_iSup_of_le hfR le_rfl
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hS
    (fun _ => zero_le) hbound

/-- A boundedly weighted disk mass, as a real number, is the integral of the weighted
indicator. -/
theorem weightedSetLIntegral_toReal_eq_integral (μ : Measure ℂ) (z : ℂ) (ρ : ℝ)
    (w : ℂ → ℝ≥0) (hw : Measurable w) :
    (∫⁻ x in Metric.ball z ρ, (w (x - z) : ℝ≥0∞) ∂μ).toReal =
      ∫ x, (Metric.ball z ρ).indicator (fun x => (w (x - z) : ℝ)) x ∂μ := by
  have hB : MeasurableSet (Metric.ball z ρ) := Metric.isOpen_ball.measurableSet
  have hmeas : Measurable fun x => (Metric.ball z ρ).indicator (fun x => (w (x - z) : ℝ)) x :=
    (measurable_coe_nnreal_real.comp (hw.comp (measurable_id.sub_const z))).indicator hB
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => by
      by_cases hx : x ∈ Metric.ball z ρ <;> simp [hx]) hmeas.aestronglyMeasurable,
    ← lintegral_indicator hB]
  congr 1
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ Metric.ball z ρ <;> simp [hx]

/-- Boundedly weighted cutoff masses of a disk converge in probability along the integer
cutoffs. -/
theorem regularizedGMC_weighted_mass_tendstoInMeasure
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (z : ℂ) (ρ : ℝ) (w : ℂ → ℝ≥0) (hw : Measurable w) (c : ℝ≥0) (hwc : ∀ y, w y ≤ c) :
    TendstoInMeasure P (fun (n : ℕ) ω => (∫⁻ x in Metric.ball z ρ, (w (x - z) : ℝ≥0∞)
        ∂regularizedGMC P Xc γ n ω).toReal) atTop
      (fun ω => (∫⁻ x in Metric.ball z ρ, (w (x - z) : ℝ≥0∞) ∂M ω).toReal) := by
  have hB : MeasurableSet (Metric.ball z ρ) := Metric.isOpen_ball.measurableSet
  set f : ℂ → ℝ := fun x => (Metric.ball z ρ).indicator (fun x => (w (x - z) : ℝ)) x with hfdef
  have hwm : Measurable fun x : ℂ => (w (x - z) : ℝ≥0∞) :=
    measurable_coe_nnreal_ennreal.comp (hw.comp (measurable_id.sub_const z))
  have hfm : Measurable f :=
    (measurable_coe_nnreal_real.comp (hw.comp (measurable_id.sub_const z))).indicator hB
  have hfb : ∀ x, |f x| ≤ c := by
    intro x
    by_cases hx : x ∈ Metric.ball z ρ
    · simp only [hfdef, Set.indicator_of_mem hx, NNReal.abs_eq]
      exact_mod_cast hwc _
    · simp [hfdef, hx]
  have hfR : ∀ x ∉ Metric.closedBall (0 : ℂ) (‖z‖ + ρ), f x = 0 := by
    intro x hx
    have hxB : x ∉ Metric.ball z ρ := fun h => hx (ball_subset_closedBall_norm_add z ρ h)
    simp [hfdef, hxB]
  have hL1 := regularizedGMC_integral_l1_tendsto P X hX γ hγ hγ2 M hM Xc hXc f hfm c hfb
    (‖z‖ + ρ) hfR
  have hF : ∀ n : ℕ, AEStronglyMeasurable (fun ω => (∫⁻ x in Metric.ball z ρ,
      (w (x - z) : ℝ≥0∞) ∂regularizedGMC P Xc γ n ω).toReal) P := by
    intro n
    have hm : Measurable fun ω => ∫⁻ x, (Metric.ball z ρ).indicator
        (fun x => (w (x - z) : ℝ≥0∞)) x ∂regularizedGMC P Xc γ n ω :=
      (Measure.measurable_lintegral (hwm.indicator hB)).comp
        (regularizedGMC_measurable P X hX Xc hXc γ n)
    refine (ENNReal.measurable_toReal.comp hm).aestronglyMeasurable.congr
      (Eventually.of_forall fun ω => ?_)
    simp only [Function.comp_apply, lintegral_indicator hB]
  have hG : AEStronglyMeasurable (fun ω => (∫⁻ x in Metric.ball z ρ,
      (w (x - z) : ℝ≥0∞) ∂M ω).toReal) P :=
    (ENNReal.measurable_toReal.comp_aemeasurable
      (gmc_setLIntegral_aemeasurable P X hX γ hγ hγ2 M hM _ hwm _ hB)).aestronglyMeasurable
  refine DOZZ.Assembly.tendstoInMeasure_of_tendsto_lintegral_ofReal_abs P _ _ hF hG ?_
  have hnat := hL1.comp tendsto_natCast_atTop_atTop
  refine hnat.congr fun n => ?_
  simp only [Function.comp_apply, weightedSetLIntegral_toReal_eq_integral _ z ρ w hw, hfdef]

/-- Boundedly weighted masses are dominated by the bound times the mass of the disk. -/
theorem weightedSetLIntegral_le_const_mul (μ : Measure ℂ) (z : ℂ) (ρ : ℝ) (w : ℂ → ℝ≥0)
    (c : ℝ≥0) (hwc : ∀ y, w y ≤ c) :
    ∫⁻ x in Metric.ball z ρ, (w (x - z) : ℝ≥0∞) ∂μ ≤ (c : ℝ≥0∞) * μ (Metric.ball z ρ) := by
  calc ∫⁻ x in Metric.ball z ρ, (w (x - z) : ℝ≥0∞) ∂μ
      ≤ ∫⁻ _x in Metric.ball z ρ, (c : ℝ≥0∞) ∂μ :=
        lintegral_mono fun x => ENNReal.coe_le_coe.mpr (hwc _)
    _ = (c : ℝ≥0∞) * μ (Metric.ball z ρ) := setLIntegral_const _ _

/-- Moments of every positive subcritical order of a boundedly weighted small-disk mass converge
along the integer cutoffs. -/
theorem gmc_weighted_ball_moment_tendsto
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (z : ℂ) (ρ : ℝ) (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8) (w : ℂ → ℝ≥0) (hw : Measurable w)
    (c : ℝ≥0) (hwc : ∀ y, w y ≤ c) (p : ℝ) (hp : 0 < p) (hp4 : p < 4 / γ ^ 2) :
    Tendsto (fun n : ℕ => ∫⁻ ω, (∫⁻ x in Metric.ball z ρ, (w (x - z) : ℝ≥0∞)
        ∂regularizedGMC P Xc γ n ω) ^ p ∂P) atTop
      (𝓝 (∫⁻ ω, (∫⁻ x in Metric.ball z ρ, (w (x - z) : ℝ≥0∞) ∂M ω) ^ p ∂P)) := by
  let _ : IsProbabilityMeasure P := hX.1
  have hB : MeasurableSet (Metric.ball z ρ) := Metric.isOpen_ball.measurableSet
  have hwm : Measurable fun x : ℂ => (w (x - z) : ℝ≥0∞) :=
    measurable_coe_nnreal_ennreal.comp (hw.comp (measurable_id.sub_const z))
  set p' : ℝ := (p + 4 / γ ^ 2) / 2 with hp'
  have hpp' : p < p' := by rw [hp']; linarith
  have hp'0 : 0 < p' := hp.trans hpp'
  obtain ⟨K, hK, hKb⟩ := regularizedGMC_ball_moment_uniform_any_center P X hX Xc hXc γ hγ hγ2
    z ρ hρ hρ8 p' (by rw [hp']; linarith)
  have hcK : (c : ℝ≥0∞) ^ p' * K ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp'0.le ENNReal.coe_ne_top) hK.ne
  refine lintegral_rpow_tendsto_of_uniform_moment P
    (fun (n : ℕ) ω => ∫⁻ x in Metric.ball z ρ, (w (x - z) : ℝ≥0∞) ∂regularizedGMC P Xc γ n ω)
    (fun ω => ∫⁻ x in Metric.ball z ρ, (w (x - z) : ℝ≥0∞) ∂M ω)
    (fun n => ?_) (gmc_setLIntegral_aemeasurable P X hX γ hγ hγ2 M hM _ hwm _ hB)
    (fun n => ?_) ?_
    (regularizedGMC_weighted_mass_tendstoInMeasure P X hX γ hγ hγ2 M hM Xc hXc z ρ w hw c hwc)
    p p' (Or.inl ⟨hp, hpp'⟩) ((c : ℝ≥0∞) ^ p' * K) hcK (fun n => ?_)
  · have hm : Measurable fun ω => ∫⁻ x, (Metric.ball z ρ).indicator
        (fun x => (w (x - z) : ℝ≥0∞)) x ∂regularizedGMC P Xc γ n ω :=
      (Measure.measurable_lintegral (hwm.indicator hB)).comp
        (regularizedGMC_measurable P X hX Xc hXc γ n)
    refine hm.aemeasurable.congr (Eventually.of_forall fun ω => ?_)
    simp only [lintegral_indicator hB]
  · filter_upwards [regularizedGMC_finite_ae P X hX Xc hXc γ n] with ω hω
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _))
      (weightedSetLIntegral_le_const_mul _ z ρ w c hwc)
  · refine Eventually.of_forall fun ω => ?_
    have := hM.1 ω
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _))
      (weightedSetLIntegral_le_const_mul _ z ρ w c hwc)
  · have hmass : AEMeasurable (fun ω => regularizedGMC P Xc γ n ω (Metric.ball z ρ) ^ p') P :=
      (((Measure.measurable_coe hB).comp
        (regularizedGMC_measurable P X hX Xc hXc γ n)).pow_const p').aemeasurable
    calc ∫⁻ ω, (∫⁻ x in Metric.ball z ρ, (w (x - z) : ℝ≥0∞) ∂regularizedGMC P Xc γ n ω) ^ p' ∂P
        ≤ ∫⁻ ω, ((c : ℝ≥0∞) * regularizedGMC P Xc γ n ω (Metric.ball z ρ)) ^ p' ∂P :=
          lintegral_mono fun ω => ENNReal.rpow_le_rpow
            (weightedSetLIntegral_le_const_mul _ z ρ w c hwc) hp'0.le
      _ = (c : ℝ≥0∞) ^ p' *
            gmcMassMoment P (regularizedGMC P Xc γ n) (Metric.ball z ρ) p' := by
          rw [lintegral_congr fun ω => ENNReal.mul_rpow_of_nonneg _ _ hp'0.le,
            lintegral_const_mul'' _ hmass]
          rfl
      _ ≤ (c : ℝ≥0∞) ^ p' * K := mul_le_mul' le_rfl (hKb n (Nat.cast_nonneg n))

/-- The location transfer of positive subcritical moments of boundedly weighted small-disk
masses, for `IsGMCOf` limits. -/
theorem gmc_weighted_ball_moment_transfer
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (z z₀ : ℂ) (ρ R : ℝ) (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8) (hR : 0 ≤ R) (hzR : ‖z‖ + ρ ≤ R)
    (hz₀R : ‖z₀‖ + ρ ≤ R) (w : ℂ → ℝ≥0) (hw : Measurable w) (c : ℝ≥0) (hwc : ∀ y, w y ≤ c)
    (p : ℝ) (hp : 0 < p) (hp4 : p < 4 / γ ^ 2) :
    ∫⁻ ω, (∫⁻ x in Metric.ball z ρ, (w (x - z) : ℝ≥0∞) ∂M ω) ^ p ∂P ≤
      ENNReal.ofReal (Real.exp (γ ^ 2 * (2 * (Real.log 3 + 2 * Real.log (1 + R))) / 2 *
          |p ^ 2 - p|)) * ENNReal.ofReal ((1 + R) ^ 4) ^ |p| *
        ∫⁻ ω, (∫⁻ x in Metric.ball z₀ ρ, (w (x - z₀) : ℝ≥0∞) ∂M ω) ^ p ∂P := by
  obtain ⟨Xc, hXc, -⟩ := hM.2
  set T : ℝ≥0∞ := ENNReal.ofReal (Real.exp (γ ^ 2 * (2 * (Real.log 3 + 2 * Real.log (1 + R))) /
      2 * |p ^ 2 - p|)) * ENNReal.ofReal ((1 + R) ^ 4) ^ |p| with hT
  have hTtop : T ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (abs_nonneg p) ENNReal.ofReal_ne_top)
  have hcut : ∀ n : ℕ,
      ∫⁻ ω, (∫⁻ x in Metric.ball z ρ, (w (x - z) : ℝ≥0∞) ∂regularizedGMC P Xc γ n ω) ^ p ∂P ≤
        T * ∫⁻ ω, (∫⁻ x in Metric.ball z₀ ρ, (w (x - z₀) : ℝ≥0∞)
          ∂regularizedGMC P Xc γ n ω) ^ p ∂P := fun n =>
    cutoff_translate_moment_le P X hX Xc hXc γ n (Nat.cast_nonneg n) z z₀ ρ R hR hzR hz₀R w hw c
      hwc p
  have h1 := gmc_weighted_ball_moment_tendsto P X hX γ hγ hγ2 M hM Xc hXc z ρ hρ hρ8 w hw c hwc
    p hp hp4
  have h2 := ENNReal.Tendsto.const_mul (gmc_weighted_ball_moment_tendsto P X hX γ hγ hγ2 M hM Xc
    hXc z₀ ρ hρ hρ8 w hw c hwc p hp hp4) (Or.inr hTtop)
  exact le_of_tendsto_of_tendsto' h1 h2 hcut

end DOZZ.Proofs

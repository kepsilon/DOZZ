/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-/
module

public import DOZZ.GMC.Construction.GMCIntensityAdapter
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Bounded marks preserve the L1 limit of the root mass. -/

@[expose] public section

open MeasureTheory Filter Topology
open scoped Distributions ENNReal

namespace DOZZ.Proofs

/-- A fixed bounded measurable mark can multiply an L1-convergent density. -/
theorem integral_bounded_mul_tendsto_of_l1
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → Ω → ℝ) (G φ : Ω → ℝ)
    (hF : ∀ n, Integrable (F n) P) (hG : Integrable G P)
    (hφ : AEStronglyMeasurable φ P) (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ ω, |φ ω| ≤ B)
    (hL1 : Tendsto (fun n => ∫⁻ ω, ENNReal.ofReal |F n ω - G ω| ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, φ ω * F n ω ∂P) atTop
      (𝓝 (∫ ω, φ ω * G ω ∂P)) := by
  have hφnorm : ∀ᵐ ω ∂P, ‖φ ω‖ ≤ B := ae_of_all _ fun ω => by
    simpa only [Real.norm_eq_abs] using hbound ω
  have hFG : Tendsto (fun n => ∫⁻ ω, ‖φ ω * F n ω - φ ω * G ω‖ₑ ∂P)
      atTop (𝓝 0) := by
    have hscale : Tendsto (fun n => ENNReal.ofReal B *
        ∫⁻ ω, ENNReal.ofReal |F n ω - G ω| ∂P) atTop (𝓝 0) := by
      simpa only [mul_zero] using ENNReal.Tendsto.const_mul hL1 (Or.inr ENNReal.ofReal_ne_top)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hscale
      (fun _ => zero_le) (fun n => ?_)
    calc
      _ ≤ ∫⁻ ω, ENNReal.ofReal B * ENNReal.ofReal |F n ω - G ω| ∂P := by
        apply lintegral_mono
        intro ω
        change ‖φ ω * F n ω - φ ω * G ω‖ₑ ≤
          ENNReal.ofReal B * ENNReal.ofReal |F n ω - G ω|
        rw [← mul_sub, Real.enorm_eq_ofReal_abs, abs_mul]
        exact (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (hbound ω) (abs_nonneg _))).trans_eq
            (ENNReal.ofReal_mul hB)
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  exact tendsto_integral_of_L1 (fun ω => φ ω * G ω)
    (hG.bdd_mul hφ hφnorm).1 (Eventually.of_forall fun n => (hF n).bdd_mul hφ hφnorm) hFG

/-- A finite expected nonnegative mass has an integrable real representative. -/
theorem integrable_mass_toReal_of_finite_expectation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (a : Ω → ℝ≥0∞)
    (ha : AEMeasurable a P) (haFinite : ∀ᵐ ω ∂P, a ω ≠ ⊤)
    (hmean : (∫⁻ ω, a ω ∂P) < ⊤) : Integrable (fun ω => (a ω).toReal) P := by
  refine ⟨(ENNReal.measurable_toReal.comp_aemeasurable ha).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => ENNReal.toReal_nonneg)]
  have heq : (fun ω => ENNReal.ofReal (a ω).toReal) =ᵐ[P] a := by
    filter_upwards [haFinite] with ω hω
    exact ENNReal.ofReal_toReal hω
  exact (lintegral_congr_ae heq).trans_lt hmean

/-- Bounded observables of the sample, including any fixed field/chaos cylinder, can multiply
the bounded-set cutoff mass while retaining convergence of its expected value. -/
theorem regularizedGMC_bounded_mass_mark_integral_tendsto
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (A : Set ℂ) (hA : MeasurableSet A) (R : ℝ)
    (hAR : A ⊆ Metric.closedBall (0 : ℂ) R)
    (φ : Ω → ℝ) (hφ : AEStronglyMeasurable φ P)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ ω, |φ ω| ≤ B) :
    Tendsto (fun n : ℕ => ∫ ω, φ ω *
      (regularizedGMC P Xc γ (n : ℝ) ω A).toReal ∂P) atTop
      (𝓝 (∫ ω, φ ω * (M ω A).toReal ∂P)) := by
  have href : gmcReferenceMeasure A < ⊤ :=
    lt_of_le_of_lt (measure_mono (Set.subset_univ A)) gmcReferenceMeasure_univ_ne_top.lt_top
  have hcut (n : ℕ) : Integrable (fun ω =>
      (regularizedGMC P Xc γ (n : ℝ) ω A).toReal) P := by
    apply integrable_mass_toReal_of_finite_expectation
    · exact ((Measure.measurable_coe hA).comp
        (regularizedGMC_measurable P X hX Xc hXc γ (n : ℝ))).aemeasurable
    · filter_upwards [regularizedGMC_finite_ae P X hX Xc hXc γ (n : ℝ)] with ω hω
      exact @measure_ne_top ℂ _ _ hω A
    · rw [regularizedGMC_lintegral_eq_reference P X hX Xc hXc γ (n : ℝ) A hA]
      exact href
  have hlim : Integrable (fun ω => (M ω A).toReal) P := by
    apply integrable_mass_toReal_of_finite_expectation
    · exact gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM A hA
    · exact ae_of_all _ fun ω => @measure_ne_top ℂ _ _ (hM.1 ω) A
    · rw [equatorGFF_GMC_intensity P X hX γ hγ hγ2 M hM A hA]
      exact href
  exact integral_bounded_mul_tendsto_of_l1 P _ _ φ hcut hlim hφ B hB hbound
    ((equatorGFF_GMC_bounded_mass_l1_of_uniform_L1
      P X hX γ hγ hγ2 M hM Xc hXc A hA R hAR).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop))

/-- A bounded nonnegative sample mark preserves convergence of extended expected set masses. -/
theorem regularizedGMC_bounded_mass_mark_lintegral_tendsto
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (A : Set ℂ) (hA : MeasurableSet A) (R : ℝ)
    (hAR : A ⊆ Metric.closedBall (0 : ℂ) R)
    (φ : Ω → ℝ) (hφ : AEStronglyMeasurable φ P)
    (hφpos : ∀ ω, 0 ≤ φ ω) (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ ω, |φ ω| ≤ B) :
    Tendsto (fun n : ℕ => ∫⁻ ω, ENNReal.ofReal (φ ω) *
      regularizedGMC P Xc γ (n : ℝ) ω A ∂P) atTop
      (𝓝 (∫⁻ ω, ENNReal.ofReal (φ ω) * M ω A ∂P)) := by
  have href : gmcReferenceMeasure A < ⊤ :=
    lt_of_le_of_lt (measure_mono (Set.subset_univ A)) gmcReferenceMeasure_univ_ne_top.lt_top
  have hmark (a : Ω → ℝ≥0∞) (ha : AEMeasurable a P)
      (hafin : ∀ᵐ ω ∂P, a ω ≠ ⊤) (hmean : (∫⁻ ω, a ω ∂P) < ⊤) :
      ENNReal.ofReal (∫ ω, φ ω * (a ω).toReal ∂P) =
        ∫⁻ ω, ENNReal.ofReal (φ ω) * a ω ∂P := by
    have hi := integrable_mass_toReal_of_finite_expectation P a ha hafin hmean
    have hprod := hi.bdd_mul hφ (ae_of_all _ fun ω => by
      simpa only [Real.norm_eq_abs] using hbound ω)
    rw [ofReal_integral_eq_lintegral_ofReal hprod
      (ae_of_all _ fun ω => mul_nonneg (hφpos ω) ENNReal.toReal_nonneg)]
    apply lintegral_congr_ae
    filter_upwards [hafin] with ω hω
    rw [ENNReal.ofReal_mul (hφpos ω), ENNReal.ofReal_toReal hω]
  have hcut (n : ℕ) : ENNReal.ofReal (∫ ω, φ ω *
      (regularizedGMC P Xc γ (n : ℝ) ω A).toReal ∂P) =
      ∫⁻ ω, ENNReal.ofReal (φ ω) * regularizedGMC P Xc γ (n : ℝ) ω A ∂P := by
    apply hmark
    · exact ((Measure.measurable_coe hA).comp
        (regularizedGMC_measurable P X hX Xc hXc γ (n : ℝ))).aemeasurable
    · filter_upwards [regularizedGMC_finite_ae P X hX Xc hXc γ (n : ℝ)] with ω hω
      exact @measure_ne_top ℂ _ _ hω A
    · rw [regularizedGMC_lintegral_eq_reference P X hX Xc hXc γ (n : ℝ) A hA]
      exact href
  have hlim : ENNReal.ofReal (∫ ω, φ ω * (M ω A).toReal ∂P) =
      ∫⁻ ω, ENNReal.ofReal (φ ω) * M ω A ∂P := by
    apply hmark
    · exact gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM A hA
    · exact ae_of_all _ fun ω => @measure_ne_top ℂ _ _ (hM.1 ω) A
    · rw [equatorGFF_GMC_intensity P X hX γ hγ hγ2 M hM A hA]
      exact href
  simpa only [Function.comp_def, hcut, hlim] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (regularizedGMC_bounded_mass_mark_integral_tendsto
      P X hX γ hγ hγ2 M hM Xc hXc A hA R hAR φ hφ B hB hbound)

end DOZZ.Proofs

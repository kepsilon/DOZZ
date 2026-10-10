module

public import DOZZ.GMC.WeightedCutoff.CoarseVariance

/-! # Gaussian Jensen bound for cutoff masses with uniformly bounded variance -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace DOZZ.Proofs

theorem regularizedGMC_moment_upper_of_variance_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ r p V : ℝ) (hp : 1 ≤ p)
    (O : Set ℂ) (hO : MeasurableSet O)
    (hvar : ∀ x ∈ O, gaussianVariance P (fun ω => Xc ω x r) ≤ V) :
    gmcMassMoment P (regularizedGMC P Xc γ r) O p ≤
      (gmcReferenceMeasure O) ^ p * ENNReal.ofReal
        (Real.exp (γ ^ 2 * (p ^ 2 - p) / 2 * V)) := by
  let _ := hX.1
  let _ : IsFiniteMeasure gmcReferenceMeasure := ⟨gmcReferenceMeasure_univ_ne_top.lt_top⟩
  have hW := measurable_gmcCircleWickDensity P X Xc hXc γ r
  have hWp : Measurable (fun q : Ω × ℂ => (gmcCircleWickDensity P Xc γ r q.1 q.2) ^ p) :=
    ENNReal.continuous_rpow_const.measurable.comp hW
  have hf (ω : Ω) : AEMeasurable (gmcCircleWickDensity P Xc γ r ω)
      (gmcReferenceMeasure.restrict O) :=
    (hW.comp (measurable_const.prodMk measurable_id)).aemeasurable
  change (∫⁻ ω, (regularizedGMC P Xc γ r ω O) ^ p ∂P) ≤ _
  calc
    _ ≤ ∫⁻ ω, (gmcReferenceMeasure O) ^ (p - 1) *
        ∫⁻ x in O, (gmcCircleWickDensity P Xc γ r ω x) ^ p ∂gmcReferenceMeasure ∂P := by
      apply lintegral_mono
      intro ω
      change (regularizedGMC P Xc γ r ω O) ^ p ≤ (gmcReferenceMeasure O) ^ (p - 1) *
        ∫⁻ x in O, (gmcCircleWickDensity P Xc γ r ω x) ^ p ∂gmcReferenceMeasure
      rw [regularizedGMC_mass_eq_wick_lintegral P X Xc hXc γ r O hO ω]
      have h := ennreal_lintegral_rpow_le_mass_rpow_mul_lintegral_rpow
        (gmcReferenceMeasure.restrict O) (gmcCircleWickDensity P Xc γ r ω) (hf ω) p hp
      simpa only [Measure.restrict_apply_univ] using h
    _ = (gmcReferenceMeasure O) ^ (p - 1) *
        ∫⁻ x in O, ∫⁻ ω, (gmcCircleWickDensity P Xc γ r ω x) ^ p ∂P ∂gmcReferenceMeasure := by
      rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith)
        (measure_ne_top _ _)), lintegral_lintegral_swap hWp.aemeasurable]
    _ ≤ (gmcReferenceMeasure O) ^ (p - 1) * (gmcReferenceMeasure O *
        ENNReal.ofReal (Real.exp (γ ^ 2 * (p ^ 2 - p) / 2 * V))) := by
      apply mul_le_mul' le_rfl
      calc
        _ ≤ ∫⁻ _x in O, ENNReal.ofReal (Real.exp
            (γ ^ 2 * (p ^ 2 - p) / 2 * V)) ∂gmcReferenceMeasure := by
          apply setLIntegral_mono' hO
          intro x hx
          rw [gmcCircleWickDensity_moment P X hX Xc hXc γ r p x]
          apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_exp.mpr
          apply mul_le_mul_of_nonneg_left (hvar x hx)
          exact div_nonneg (mul_nonneg (sq_nonneg γ) (by nlinarith)) (by norm_num)
        _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ, mul_comm]
    _ = _ := by
      have he : (gmcReferenceMeasure O) ^ (p - 1) * gmcReferenceMeasure O =
          (gmcReferenceMeasure O) ^ p := by
        calc
          _ = (gmcReferenceMeasure O) ^ (p - 1) * (gmcReferenceMeasure O) ^ (1 : ℝ) :=
            by rw [ENNReal.rpow_one]
          _ = (gmcReferenceMeasure O) ^ ((p - 1) + 1) :=
            (ENNReal.rpow_add_of_nonneg _ _ (by linarith) (by norm_num)).symm
          _ = _ := by congr 1; ring
      rw [← mul_assoc, he]
end DOZZ.Proofs

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.GMC.IsAdmissibleGMCVersion
import DOZZ.GMC.Construction.CircleCutoffTestMass
import DOZZ.GMC.Construction.FatouInMeasure
import DOZZ.GMC.Construction.RegularizedGMCExpectedMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! Expected test-mass bounds for admissible versions of circle cutoffs. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Distributions ENNReal NNReal

namespace DOZZ.Proofs

/-- A nonnegative compact circle test against any admissible limit has expected mass at most its
reference mass. The proof uses cutoff intensity and Fatou along convergence in measure. -/
theorem admissibleCircleVersion_expected_test_le
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) (γ : ℝ)
    (M : Ω → Measure ℂ)
    (hM : IsAdmissibleGMCVersion P Set.univ (fun x => normPlus x ^ (-4 : ℝ))
      (fun ω ε x => Xc ω x (Real.log (1 / ε))) γ M)
    (f : BoundedContinuousFunction ℂ ℝ)
    (hf : ∀ x, 0 ≤ f x) (hfc : HasCompactSupport (f : ℂ → ℝ)) :
    ∫⁻ ω, ENNReal.ofReal (∫ x, f x ∂M ω) ∂P ≤
      ∫⁻ x, ENNReal.ofReal (f x) ∂gmcReferenceMeasure := by
  classical
  rcases hM with ⟨_, _, _, hMlim⟩
  let φ : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal (f x)
  have hφ : Measurable φ := ENNReal.measurable_ofReal.comp f.continuous.measurable
  let F : ℝ → Ω → ℝ := fun r ω =>
    (∫⁻ x, φ x ∂regularizedGMC P Xc γ r ω).toReal
  let G : Ω → ℝ := fun ω => ∫ x, f x ∂M ω
  have hFmeas : ∀ r, Measurable (F r) := by
    intro r
    change Measurable (fun ω =>
      (∫⁻ x, φ x ∂regularizedGMC P Xc γ r ω).toReal)
    exact ENNReal.measurable_toReal.comp
      ((Measure.measurable_lintegral hφ).comp
        (regularizedGMC_measurable P X hX Xc hXc γ r))
  have hIntegral : ∀ r, ∀ᵐ ω ∂P,
      F r ω = ∫ x, f x ∂regularizedGMC P Xc γ r ω := by
    intro r
    filter_upwards [regularizedGMC_finite_ae P X hX Xc hXc γ r] with ω hfinite
    let μ : Measure ℂ := regularizedGMC P Xc γ r ω
    let _ := hfinite
    have hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖f‖ := ae_of_all _ f.norm_coe_le_norm
    have hmem : MemLp (fun x => f x) (1 : ℝ≥0∞) μ :=
      MemLp.of_bound f.continuous.measurable.aestronglyMeasurable ‖f‖ hbound
    have hint : Integrable (fun x => f x) μ :=
      hmem.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 1)
    have hnonneg : 0 ≤ᵐ[μ] fun x => f x := ae_of_all _ hf
    have hlin := ofReal_integral_eq_lintegral_ofReal hint hnonneg
    change (∫⁻ x, φ x ∂μ).toReal = ∫ x, f x ∂μ
    calc
      (∫⁻ x, φ x ∂μ).toReal = ENNReal.toReal (ENNReal.ofReal (∫ x, f x ∂μ)) := by
        rw [← hlin]
      _ = ∫ x, f x ∂μ := ENNReal.toReal_ofReal (integral_nonneg_of_ae hnonneg)
  have hTbase : TendstoInMeasure P
      (fun r ω => regularizedLogChaosTestMass P Set.univ
        (fun x => normPlus x ^ (-4 : ℝ))
        (fun ω ε x => Xc ω x (Real.log (1 / ε))) γ r ω f) atTop G := by
    exact hMlim f hfc (Set.subset_univ _)
  have hcut : ∀ r : ℝ,
      (fun ω => regularizedLogChaosTestMass P Set.univ
        (fun x => normPlus x ^ (-4 : ℝ))
        (fun ω ε x => Xc ω x (Real.log (1 / ε))) γ r ω f) =ᵐ[P] F r := by
    intro r
    filter_upwards [hIntegral r] with ω hω
    rw [circleCutoff_testMass_eq_regularizedGMC P X hX Xc hXc γ r ω f, ← hω]
  have hT : TendstoInMeasure P F atTop G := by
    apply TendstoInMeasure.congr hcut (Filter.Eventually.of_forall fun _ => rfl) hTbase
  have hOfRealIntegral : ∀ r : ℝ, ∀ᵐ ω ∂P,
      ENNReal.ofReal (∫ x, f x ∂regularizedGMC P Xc γ r ω) =
        ∫⁻ x, φ x ∂regularizedGMC P Xc γ r ω := by
    intro r
    filter_upwards [regularizedGMC_finite_ae P X hX Xc hXc γ r] with ω hfinite
    let μ : Measure ℂ := regularizedGMC P Xc γ r ω
    let _ := hfinite
    have hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖f‖ := ae_of_all _ f.norm_coe_le_norm
    have hmem : MemLp (fun x => f x) (1 : ℝ≥0∞) μ :=
      MemLp.of_bound f.continuous.measurable.aestronglyMeasurable ‖f‖ hbound
    have hint : Integrable (fun x => f x) μ :=
      hmem.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 1)
    exact ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hf)
  have hbound (r : ℝ) : ∫⁻ ω, ENNReal.ofReal (F r ω) ∂P ≤
      ∫⁻ x, φ x ∂gmcReferenceMeasure := by
    calc
      ∫⁻ ω, ENNReal.ofReal (F r ω) ∂P =
          ∫⁻ ω, ∫⁻ x, φ x ∂regularizedGMC P Xc γ r ω ∂P := by
            apply lintegral_congr_ae
            filter_upwards [hIntegral r, hOfRealIntegral r] with ω hω hlin
            rw [hω]
            exact hlin
      _ ≤ ∫⁻ x, φ x ∂gmcReferenceMeasure := by
        exact le_of_eq
          (regularizedGMC_lintegral_test_eq_reference P X hX Xc hXc γ r φ hφ)
  simpa [G, φ] using lintegral_ofReal_limit_le_of_tendstoInMeasure
    P F G (∫⁻ x, φ x ∂gmcReferenceMeasure) hFmeas hT hbound

end DOZZ.Proofs

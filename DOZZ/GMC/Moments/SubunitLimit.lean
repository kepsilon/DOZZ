/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.IsGMCOf
public import DOZZ.GMC.Moments.CutoffSubunit
public import DOZZ.GMC.Moments.LimitFatou
public import DOZZ.GMC.Moments.ReferenceFinite
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-! Subunit total-mass moments for arbitrary `IsGMCOf` limits. -/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

namespace DOZZ.Proofs

/-- Every arbitrary `IsGMCOf` limit has finite subunit moments of its total mass. The proof uses
only the weak test-integral convergence in `IsGMCOf`, finite-cutoff intensity, and Fatou. -/
theorem gmc_total_mass_subunit_moment_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (M : Ω → Measure ℂ)
    (hM : IsGMCOf P X γ M) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∫⁻ ω, ENNReal.rpow (M ω Set.univ) p ∂P ≤ 1 + gmcReferenceMeasure Set.univ := by
  obtain ⟨Xc, hXc, hMlim⟩ := hM.2
  let one : BoundedContinuousFunction ℂ ℝ := 1
  let cutoff : ℕ → Ω → ℝ := (fun r ω => ∫ x, one x ∂regularizedGMC P Xc γ r ω) ∘ Nat.cast
  let limit : Ω → ℝ := fun ω => ∫ x, one x ∂M ω
  have hconvReal := (hMlim one).comp (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hconv : TendstoInMeasure P cutoff atTop limit := by
    simpa [cutoff, limit] using hconvReal
  have href : gmcReferenceMeasure Set.univ ≠ ∞ := gmcReferenceMeasure_univ_ne_top
  have hmass (n : ℕ) : AEMeasurable
      (fun ω => regularizedGMC P Xc γ n ω Set.univ) P :=
    regularizedGMC_mass_aemeasurable P X hX Xc hXc γ n Set.univ MeasurableSet.univ
  have hmean (n : ℕ) :
      ∫⁻ ω, regularizedGMC P Xc γ n ω Set.univ ∂P = gmcReferenceMeasure Set.univ :=
    regularizedGMC_lintegral_eq_reference P X hX Xc hXc γ n Set.univ MeasurableSet.univ
  have hmassFinite (n : ℕ) : ∀ᵐ ω ∂P,
      regularizedGMC P Xc γ n ω Set.univ < ∞ := by
    apply ae_lt_top' (hmass n)
    rw [hmean n]
    exact href
  have hcutoffEq (n : ℕ) : ∀ᵐ ω ∂P,
      ENNReal.ofReal (max (cutoff n ω) 0) = regularizedGMC P Xc γ n ω Set.univ := by
    filter_upwards [hmassFinite n] with ω hω
    have hconst : cutoff n ω = (regularizedGMC P Xc γ n ω Set.univ).toReal := by
      simp [cutoff, one, integral_const, measureReal_def]
    rw [hconst, max_eq_left (ENNReal.toReal_nonneg), ENNReal.ofReal_toReal hω.ne]
  have hcutoffMeas (n : ℕ) : AEMeasurable (cutoff n) P := by
    apply AEMeasurable.congr ((hmass n).ennreal_toReal)
    filter_upwards with ω
    simp [cutoff, one, integral_const, measureReal_def]
  have hpowerMeas (n : ℕ) : AEMeasurable
      (fun ω => ENNReal.rpow (ENNReal.ofReal (max (cutoff n ω) 0)) p) P := by
    have hψ : Continuous (fun t : ℝ =>
        ENNReal.rpow (ENNReal.ofReal (max t 0)) p) := by
      exact ENNReal.continuous_rpow_const.comp
        (ENNReal.continuous_ofReal.comp
          (continuous_max.comp (continuous_id.prodMk continuous_const)))
    exact hψ.measurable.comp_aemeasurable (hcutoffMeas n)
  have hbound (n : ℕ) : ∫⁻ ω,
      ENNReal.rpow (ENNReal.ofReal (max (cutoff n ω) 0)) p ∂P ≤
        1 + gmcReferenceMeasure Set.univ := by
    calc
      ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (max (cutoff n ω) 0)) p ∂P =
          ∫⁻ ω, ENNReal.rpow (regularizedGMC P Xc γ n ω Set.univ) p ∂P := by
            apply lintegral_congr_ae
            filter_upwards [hcutoffEq n] with ω hω
            rw [hω]
      _ ≤ 1 + gmcReferenceMeasure Set.univ :=
        regularizedGMC_subunit_moment_le P X hX Xc hXc γ n Set.univ
          MeasurableSet.univ p hp0 hp1
  have hlimitNonneg : 0 ≤ᵐ[P] limit := by
    filter_upwards with ω
    have hlimitEq : limit ω = (M ω Set.univ).toReal := by
      simp [limit, one, integral_const, measureReal_def]
    rw [hlimitEq]
    positivity
  have hfatou := lintegral_ennreal_rpow_le_of_tendstoInMeasure P cutoff limit p
    (1 + gmcReferenceMeasure Set.univ) hconv hpowerMeas hlimitNonneg hbound
  have htarget (ω : Ω) : ENNReal.ofReal (limit ω) = M ω Set.univ := by
    have hmassTop : M ω Set.univ ≠ ∞ := ne_of_lt (hM.1 ω).measure_univ_lt_top
    have hlimitEq : limit ω = (M ω Set.univ).toReal := by
      simp [limit, one, integral_const, measureReal_def]
    rw [hlimitEq, ENNReal.ofReal_toReal hmassTop]
  calc
    ∫⁻ ω, ENNReal.rpow (M ω Set.univ) p ∂P =
        ∫⁻ ω, ENNReal.rpow (ENNReal.ofReal (limit ω)) p ∂P := by
          apply lintegral_congr
          intro ω
          rw [htarget ω]
    _ ≤ 1 + gmcReferenceMeasure Set.univ := hfatou

end DOZZ.Proofs

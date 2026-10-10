/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Correlations.Symmetry.CorrelatedScalarLimit
public import DOZZ.GMC.Construction.GMCVaryingWeightedTotalMassLimit
@[expose] public section
open MeasureTheory Filter Set
open scoped Distributions ENNReal Topology
namespace DOZZ.Proofs

/-- Bounded continuous densities preserve finiteness. -/
theorem symmetry_bcf_withDensity_finite (μ : Measure ℂ) [IsFiniteMeasure μ]
    (w : BoundedContinuousFunction ℂ ℝ) :
    IsFiniteMeasure (μ.withDensity (fun z => ENNReal.ofReal (w z))) := by
  apply isFiniteMeasure_withDensity
  apply ne_of_lt
  calc
    (∫⁻ z, ENNReal.ofReal (w z) ∂μ) ≤ ∫⁻ z, ENNReal.ofReal ‖w‖ ∂μ :=
      lintegral_mono (fun z => ENNReal.ofReal_le_ofReal
        ((le_abs_self _).trans (w.norm_coe_le_norm z)))
    _ < ∞ := by
      rw [lintegral_const]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ univ)

/-- The real total mass of a nonnegative bounded density is its Bochner integral. -/
theorem symmetry_weighted_total_eq_integral (μ : Measure ℂ) [IsFiniteMeasure μ]
    (w : BoundedContinuousFunction ℂ ℝ) (hw : ∀ z, 0 ≤ w z) :
    ((μ.withDensity (fun z => ENNReal.ofReal (w z))) univ).toReal = ∫ z, w z ∂μ := by
  let := symmetry_bcf_withDensity_finite μ w
  have hm : Measurable (fun z => ENNReal.ofReal (w z)) :=
    ENNReal.measurable_ofReal.comp w.continuous.measurable
  have hf : ∀ᵐ z ∂μ, ENNReal.ofReal (w z) < ∞ := ae_of_all _ (fun _ => ENNReal.ofReal_lt_top)
  have h := integral_withDensity_eq_integral_toReal_smul hm hf (fun _ : ℂ => (1 : ℝ))
  simp only [integral_const, Measure.real_def, smul_eq_mul, mul_one] at h
  rw [h]
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by
    change (ENNReal.ofReal (w z)).toReal = w z
    exact ENNReal.toReal_ofReal (hw z))

/-- Uniformly convergent nonnegative weights give convergence of actual real integrals. -/
theorem regularizedGMC_varying_bcf_integral
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (γ : ℝ) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (u : ℝ → BoundedContinuousFunction ℂ ℝ) (hu : ∀ r x, 0 ≤ u r x)
    (v : BoundedContinuousFunction ℂ ℝ) (hv : ∀ x, 0 ≤ v x)
    (hconv : TendstoUniformly (fun r x => u r x) v atTop) :
    TendstoInMeasure P (fun r ω => ∫ x, u r x ∂regularizedGMC P Xc γ r ω) atTop
      (fun ω => ∫ x, v x ∂M ω) := by
  have h := regularizedGMC_varyingWithDensity_univ_mass_tendstoInMeasure
    P X hX Xc hXc γ M hM u hu v hv hconv
  apply TendstoInMeasure.congr _ _ h
  · intro r
    filter_upwards [regularizedGMC_finite_ae P X hX Xc hXc γ r] with ω hω
    let := hω
    exact symmetry_weighted_total_eq_integral (regularizedGMC P Xc γ r ω) (u r) (hu r)
  · exact ae_of_all _ (fun ω => by
      let := hM.1 ω
      exact symmetry_weighted_total_eq_integral (M ω) v hv)
end DOZZ.Proofs

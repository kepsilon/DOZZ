/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.SpatialComparisonLimit
/-! The spatial exhaustion applies samplewise to the true random radial weights. -/
@[expose] public section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- A compact test supported in a measurable region has the same weighted mass on that
region and on the whole plane, for arbitrary nonnegative weights. -/
theorem reflected_supported_test_lintegral (μ : Measure ℂ) (U : Set ℂ) (hU : MeasurableSet U)
    (f : BoundedContinuousFunction ℂ ℝ) (hfU : tsupport (f : ℂ → ℝ) ⊆ U)
    (w : ℂ → ℝ≥0∞) :
    (∫⁻ x in U, ENNReal.ofReal (f x)*w x ∂μ) = ∫⁻ x, ENNReal.ofReal (f x)*w x ∂μ := by
  rw [← lintegral_indicator hU]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ U
  · rw [indicator_of_mem hx]
  · have hf : f x = 0 := image_eq_zero_of_notMem_tsupport (fun hs => hx (hfU hs))
    simp only [indicator_of_notMem hx, hf, ENNReal.ofReal_zero, zero_mul]

/-- The constructed unweighted spatial convergence transfers to each actual radial path
and lateral sample by changing the measure. No finiteness assumption on the full mass is needed. -/
theorem reflected_global_spatial_mass_limit (γ : ℝ) (a : TwoSidedPath) (μ : Measure ℂ)
    (U : Set ℂ) (hU : MeasurableSet U) (w : ℂ → ℝ) (hw : Measurable w)
    (g : ℕ → BoundedContinuousFunction ℂ ℝ) (hgU : ∀ n, tsupport (g n : ℂ → ℝ) ⊆ U)
    (hlim : ∀ ν : Measure ℂ, Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (g n x) ∂ν) atTop
      (𝓝 (∫⁻ x in U, ENNReal.ofReal (w x) ∂ν))) :
    Tendsto (fun n => ∫⁻ x in U, ENNReal.ofReal (g n x)*
      ENNReal.ofReal (reflected_global_reinsertionWeight γ a x) ∂μ) atTop
      (𝓝 (∫⁻ x in U, ENNReal.ofReal (w x)*
        ENNReal.ofReal (reflected_global_reinsertionWeight γ a x) ∂μ)) := by
  let W : ℂ → ℝ≥0∞ := fun x => ENNReal.ofReal (reflected_global_reinsertionWeight γ a x)
  have hW : Measurable W := ((reflected_global_reinsertionWeight_measurable γ).comp
    (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have he (f : ℂ → ℝ≥0∞) (hf : Measurable f) : (∫⁻ x in U, f x*W x ∂μ) =
      ∫⁻ x in U, f x ∂μ.withDensity W := by
    rw [restrict_withDensity hU]
    have ht := lintegral_withDensity_eq_lintegral_mul (μ.restrict U) hW hf
    simp only [Pi.mul_apply, mul_comm] at ht
    exact ht.symm
  have ht := hlim (μ.withDensity W)
  have hn (n : ℕ) : (∫⁻ x, ENNReal.ofReal (g n x) ∂μ.withDensity W) =
      ∫⁻ x in U, ENNReal.ofReal (g n x)*W x ∂μ := by
    rw [he _ (g n).continuous.measurable.ennreal_ofReal]
    simpa only [mul_one] using (reflected_supported_test_lintegral
      (μ.withDensity W) U hU (g n) (hgU n) (fun _ => 1)).symm
  simpa only [hn, ← he _ hw.ennreal_ofReal] using ht

end DOZZ.Proofs

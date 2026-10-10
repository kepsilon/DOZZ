/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Correlations.Symmetry.RepinnedCircle
public import DOZZ.GMC.CirclePotential
@[expose] public section
open MeasureTheory Filter
open scoped Distributions Topology
namespace DOZZ.Proofs

/-- Reflection's circle pinning error is uniformly at most twice its radius. -/
theorem symmetryReflection_circle_potential_error (x : ℂ) (r : ℝ) :
    |(∫ z, symmetryReflectionPotential z ∂circleMeasure x r) -
      symmetryReflectionPotential x| ≤ 2 * Real.exp (-r) := by
  rw [symmetryReflection_circle_potential]
  unfold symmetryReflectionPotential
  have h (z : ℂ) : |(∫ w, Real.log (normPlus w) ∂circleMeasure z r) -
      Real.log (normPlus z)| ≤ Real.exp (-r) := by
    rw [integral_circleMeasure_eq_circleAverage z r _ continuous_log_normPlus.measurable]
    exact CirclePotential.abs_circleAverage_log_normPlus_sub_le z (Real.exp_pos _)
  calc
    _ = |((∫ w, Real.log (normPlus w) ∂circleMeasure (1 - x) r) -
        Real.log (normPlus (1 - x))) -
      ((∫ w, Real.log (normPlus w) ∂circleMeasure x r) - Real.log (normPlus x))| := by
        congr 1; ring
    _ ≤ _ := abs_sub _ _
    _ ≤ _ := by linarith only [h (1 - x), h x]

/-- The normalization retains its precise correlation with every re-pinned circle. -/
theorem repinned_circle_normalization_covariance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (x : ℂ) (r : ℝ) :
    gaussianCovariance P (fun ω => Xc ω (1 - x) r - Xc ω 1 0)
      (fun ω => Xc ω 1 0) =
      (∫ z, symmetryReflectionPotential z ∂circleMeasure x r) - symmetryReflectionKappa := by
  let : IsProbabilityMeasure P := hX.1
  let := circleMeasure_isProbability (1 - x) r
  let L := fun ω => Xc ω 1 0
  have hAL : Integrable (fun ω => Xc ω (1 - x) r * L ω) P :=
    (hXc.2.1 (1 - x) r).integrable_mul (hXc.2.1 1 0)
  have hLL : Integrable (fun ω => L ω * L ω) P :=
    (hXc.2.1 1 0).integrable_mul (hXc.2.1 1 0)
  have hsub : gaussianCovariance P (fun ω => Xc ω (1 - x) r - L ω) L =
      gaussianCovariance P (fun ω => Xc ω (1 - x) r) L - gaussianVariance P L := by
    unfold gaussianCovariance gaussianVariance
    simp_rw [sub_mul]
    exact integral_sub hAL hLL
  rw [hsub, reflection_normalization_variance P X hX Xc hXc,
    isCircleAverage_covariance P X hX Xc hXc]
  have he (z : ℂ) : (∫ w, gffKernel z w ∂circleMeasure 1 0) =
      symmetryReflectionPotential (1 - z) + symmetryReflectionKappa := by
    simpa only [show (1 : ℂ) - (1 - z) = z from symmetryReflection_involutive z] using
      reflection_source_circle_potential (1 - z)
  simp_rw [he]
  have hd : Integrable (fun z => symmetryReflectionPotential (1 - z))
      (circleMeasure (1 - x) r) :=
    integrable_circleMeasure_of_circleIntegrable (1 - x) r
      (symmetryReflectionPotential_continuous.comp (continuous_const.sub continuous_id)).measurable
      (symmetryReflectionPotential_continuous.comp
        (continuous_const.sub continuous_id)).continuousOn.circleIntegrable'
  rw [integral_add hd (integrable_const _), integral_const, probReal_univ, one_smul,
    symmetryReflection_circle_integral _ symmetryReflectionPotential_continuous.measurable]
  rw [show (1 : ℂ) - (1 - x) = x from symmetryReflection_involutive x]
  ring

end DOZZ.Proofs

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Correlations.Symmetry.ReflectionTest
public import DOZZ.GMC.CircleAverageLimits
public import DOZZ.GFFStructure.CirclePotential
public import Mathlib.MeasureTheory.Group.Integral
@[expose] public section
open MeasureTheory Set
open scoped Distributions
namespace DOZZ.Proofs

/-- Reflection preserves planar Lebesgue integrals, with the actual affine substitution. -/
theorem symmetryReflection_integral (f : ℂ → ℝ) :
    (∫ x, f (1 - x)) = ∫ x, f x :=
  (Measure.measurePreserving_sub_left (volume : Measure ℂ) 1).integral_comp
    symmetryReflectionHomeomorph.measurableEmbedding f

/-- The finite-energy scalar normalization of reflection. -/
noncomputable def symmetryReflectionKappa : ℝ :=
  ∫ w, Real.log (normPlus w) ∂circleMeasure 1 0

/-- The mixed point/circle potential contains both the pinning change and its circle average. -/
theorem reflection_source_circle_potential (x : ℂ) :
    (∫ w, gffKernel (1 - x) w ∂circleMeasure 1 0) =
      symmetryReflectionPotential x + symmetryReflectionKappa := by
  rw [integral_gffKernel_circleMeasure]
  simp only [neg_zero, Real.exp_zero,
    show (1 : ℂ) - (1 - x) = x by ring]
  unfold symmetryReflectionPotential symmetryReflectionKappa normPlus
  ring

/-- Actual cross covariance of a reflected test with the source normalization circle. -/
theorem reflection_test_circle_cross (f : TestFn) :
    circleCross 1 0 (symmetryReflectionTest f) =
      ∫ x, f x * (symmetryReflectionPotential x + symmetryReflectionKappa) := by
  unfold circleCross
  have he : (fun y : ℂ => symmetryReflectionTest f y *
      ∫ w, gffKernel y w ∂circleMeasure 1 0) =
      fun y => (fun x : ℂ => f x * (symmetryReflectionPotential x + symmetryReflectionKappa))
        (1 - y) := by
    funext y
    have hp := reflection_source_circle_potential (1 - y)
    rw [show (1 : ℂ) - (1 - y) = y by ring] at hp
    rw [hp]
    rfl
  rw [he]
  exact symmetryReflection_integral (fun x => f x * (symmetryReflectionPotential x + symmetryReflectionKappa))

/-- The scalar's correlation with source test coordinates, without an independence assumption. -/
theorem reflection_test_normalization_covariance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc)
    (f : TestFn) :
    gaussianCovariance P (fun ω => X ω (symmetryReflectionTest f))
      (fun ω => Xc ω 1 0) =
      ∫ x, f x * (symmetryReflectionPotential x + symmetryReflectionKappa) := by
  rw [isCircleAverage_cross_covariance P X hX Xc hXc,
    reflection_test_circle_cross]
/-- The normalization circle has variance twice the pinning constant. -/
theorem reflection_normalization_variance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) :
    gaussianVariance P (fun ω => Xc ω 1 0) = 2 * symmetryReflectionKappa := by
  unfold gaussianVariance
  rw [isCircleAverage_covariance P X hX Xc hXc]
  change circleSelfEnergy 1 0 = 2 * symmetryReflectionKappa
  rw [circleSelfEnergy_eq]
  simp only [zero_add, symmetryReflectionKappa]

/-- The correlated normalization is in the actual source field's Gaussian closure. -/
theorem reflection_normalization_gaussianL2
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (Xc : Ω → ℂ → ℝ → ℝ) (hXc : IsCircleAverage P X Xc) :
    IsGaussianL2Limit P X (fun ω => Xc ω 1 0) :=
  isCircleAverage_isGaussianL2Limit P X hX Xc hXc 1 0
end DOZZ.Proofs

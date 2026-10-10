/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.Correlations.Symmetry.ReflectionCircleCovariance
public import DOZZ.GFF.EnergyPositivity
@[expose] public section
open MeasureTheory Set
open scoped Distributions
namespace DOZZ.Proofs

/-- The reflection pullback preserves test mass. -/
theorem symmetryReflection_testMass (f : TestFn) :
    testMass (symmetryReflectionTest f) = testMass f :=
  symmetryReflection_integral f

/-- Translation and negation preserve the logarithmic part of the test pairing. -/
theorem symmetryReflection_logPairing (f g : TestFn) :
    testFnLogPairing (symmetryReflectionTest f) (symmetryReflectionTest g) =
      testFnLogPairing f g := by
  rw [testFnLogPairing_eq_complex, testFnLogPairing_eq_complex]
  let F : ℂ × ℂ → ℝ := fun p => f p.1 * g p.2 * (-Real.log ‖p.1 - p.2‖)
  have hmp := (Measure.measurePreserving_sub_left (volume : Measure ℂ) 1).prod
    (Measure.measurePreserving_sub_left (volume : Measure ℂ) 1)
  have h := hmp.integral_comp
    (symmetryReflectionHomeomorph.prodCongr symmetryReflectionHomeomorph).measurableEmbedding F
  convert h using 1
  · congr 1
    funext p
    change f (1 - p.1) * g (1 - p.2) * (-Real.log ‖p.1 - p.2‖) =
      f (1 - p.1) * g (1 - p.2) * (-Real.log ‖(1 - p.1) - (1 - p.2)‖)
    rw [show (1 - p.1) - (1 - p.2) = -(p.1 - p.2) by ring, norm_neg]

/-- Replacing the pinning potential adds exactly its bounded difference. -/
theorem symmetryReflection_testPotential (f : TestFn) :
    testFnPotential (symmetryReflectionTest f) = testFnPotential f +
      ∫ x, f x * symmetryReflectionPotential x := by
  rw [testFnPotential_eq_complex_logPlus, testFnPotential_eq_complex_logPlus]
  have h := symmetryReflection_integral (fun x => f x * Real.log (normPlus (1 - x)))
  have he : (fun x : ℂ => f (1 - x) * Real.log (normPlus (1 - (1 - x)))) =
      fun x => f (1 - x) * Real.log (normPlus x) := by
    funext x
    rw [show (1 : ℂ) - (1 - x) = x by ring]
  rw [he] at h
  change (∫ x, f (1 - x) * Real.log (normPlus x)) =
    (∫ x, f x * Real.log (normPlus x)) + ∫ x, f x * symmetryReflectionPotential x
  rw [h]
  have hi : Integrable (fun x : ℂ => f x * Real.log (normPlus x)) volume := by
    have hn : Continuous (fun x : ℂ => Real.log (normPlus x)) :=
      (continuous_const.max continuous_norm).log
        (fun x => (lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖x‖)).ne')
    exact (f.continuous.mul hn).integrable_of_hasCompactSupport f.hasCompactSupport.mul_right
  have hd : Integrable (fun x : ℂ => f x * symmetryReflectionPotential x) volume :=
    (f.continuous.mul symmetryReflectionPotential_continuous).integrable_of_hasCompactSupport
      f.hasCompactSupport.mul_right
  rw [← integral_add hi hd]
  congr 1
  funext x
  unfold symmetryReflectionPotential
  ring

/-- The covariance form carries the two correlated pinning corrections. -/
theorem gffCov_symmetryReflectionTest (f g : TestFn) :
    gffCov (symmetryReflectionTest f) (symmetryReflectionTest g) = gffCov f g +
      (∫ x, f x * symmetryReflectionPotential x) * testMass g +
      testMass f * (∫ x, g x * symmetryReflectionPotential x) := by
  rw [gffCov_eq_equatorLogEnergy, gffCov_eq_equatorLogEnergy,
    symmetryReflection_testMass, symmetryReflection_testMass,
    symmetryReflection_testPotential, symmetryReflection_testPotential,
    symmetryReflection_logPairing]
  ring
end DOZZ.Proofs

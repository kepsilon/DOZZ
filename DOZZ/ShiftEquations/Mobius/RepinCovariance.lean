/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.ShiftEquations.Mobius.AffinePush
public import DOZZ.ShiftEquations.Mobius.RepinPotential
public import DOZZ.Statements.Defs.GffCov
public import DOZZ.Statements.Defs.CircleCross
import DOZZ.GFFStructure.CircleCovariance
import DOZZ.GFFStructure.AnnularWeakLimit
import DOZZ.GMC.CirclePotential
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap

/-!
# Covariances of the repinned field

The affine map `ψ(y) = a y + b` changes the equator kernel by the metric defect `d` of
`AffineKernel`: `G(ψ y, ψ y') = G(y, y') + d(y) + d(y')` off the diagonal. Integrating this identity
against pushed test functions and pushed circles gives the covariance of the pushed tests, the cross
energies of a pushed test with the repinning circle and with a pushed circle, and the double energy
of two pushed circles. The diagonal is Lebesgue-null and circle-measure-null, which is why the
identity is only needed off it; circle measures carry no atoms.
-/

public section

open MeasureTheory Set

namespace DOZZ.Proofs

/-- Circle measures carry no atoms. -/
theorem circleMeasure_singleton_eq_zero (x : ℂ) (r : ℝ) (y : ℂ) :
    circleMeasure x r {y} = 0 := by
  have hcount : (circleMap x (Real.exp (-r)) ⁻¹' {y}).Countable :=
    (Set.countable_singleton y).preimage_circleMap x (Real.exp_pos _).ne'
  rw [circleMeasure, Measure.smul_apply, Measure.map_apply (measurable_circleMap _ _)
    (measurableSet_singleton y), Measure.restrict_apply' measurableSet_Ioc,
    measure_mono_null Set.inter_subset_left (hcount.measure_zero _), smul_zero]

namespace RepinCovariance

/-- Almost every point of a circle differs from a given point. -/
theorem ae_ne_circleMeasure (x : ℂ) (r : ℝ) (y : ℂ) : ∀ᵐ u ∂circleMeasure x r, u ≠ y := by
  rw [ae_iff]
  simpa only [ne_eq, not_not, Set.ofPred_eq_eq_singleton] using
    circleMeasure_singleton_eq_zero x r y

/-- A continuous function is integrable on every circle. -/
theorem integrable_circleMeasure_of_continuous {g : ℂ → ℝ} (hg : Continuous g) (x : ℂ) (r : ℝ) :
    Integrable g (circleMeasure x r) := by
  have _ := circleMeasure_isProbability x r
  obtain ⟨C, hC⟩ :=
    (isCompact_sphere x (Real.exp (-r))).exists_bound_of_continuousOn hg.continuousOn
  exact Integrable.of_bound hg.aestronglyMeasurable C
    (by filter_upwards [ae_mem_sphere_circleMeasure x r] with u hu using hC u hu)

/-- A test function is integrable. -/
theorem integrable_testFn (f : TestFn) : Integrable f :=
  f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport

/-- A test function times a continuous function is integrable. -/
theorem integrable_testFn_mul {h : ℂ → ℝ} (hh : Continuous h) (f : TestFn) :
    Integrable (fun y => f y * h y) :=
  (f.continuous.mul hh).integrable_of_hasCompactSupport f.hasCompactSupport.mul_right

/-- The circle potential at an affine image point, with the circle left unpushed. -/
theorem integral_gffKernel_affine_circleMeasure (a b : ℂ) (ha : a ≠ 0) (x y : ℂ) (r : ℝ) :
    ∫ v, gffKernel (a * x + b) (a * v + b) ∂circleMeasure y r =
      (∫ v, gffKernel x v ∂circleMeasure y r) + affineDefect a b x +
        ∫ v, affineDefect a b v ∂circleMeasure y r := by
  have _ := circleMeasure_isProbability y r
  have hae : (fun v => gffKernel (a * x + b) (a * v + b)) =ᵐ[circleMeasure y r]
      fun v => gffKernel x v + affineDefect a b x + affineDefect a b v := by
    filter_upwards [ae_ne_circleMeasure y r x] with v hv
    exact gffKernel_affine a b ha (Ne.symm hv)
  have hG : Integrable (fun v => gffKernel x v) (circleMeasure y r) :=
    integrable_gffKernel_circleMeasure y x r
  have hGc : Integrable (fun v => gffKernel x v + affineDefect a b x) (circleMeasure y r) :=
    hG.add (integrable_const _)
  rw [integral_congr_ae hae, integral_add hGc (integrable_affineDefect_circleMeasure a b ha y r),
    integral_add hG (integrable_const _), integral_const, probReal_univ, one_smul]

/-- The potential of an affinely pushed circle at an affine image point. -/
theorem integral_gffKernel_circleMeasure_affine (a b : ℂ) (ha : a ≠ 0) (x y : ℂ) (r : ℝ) :
    ∫ z, gffKernel (a * x + b) z ∂circleMeasure (a * y + b) (r - Real.log ‖a‖) =
      (∫ v, gffKernel x v ∂circleMeasure y r) + affineDefect a b x +
        ∫ v, affineDefect a b v ∂circleMeasure y r := by
  rw [← circleMeasure_map_affine a b ha y r,
    integral_map (by fun_prop) (CirclePotential.measurable_gffKernel _).aestronglyMeasurable]
  exact integral_gffKernel_affine_circleMeasure a b ha x y r

/-- The potential of a pushed test function at an affine image point. -/
theorem integral_gffKernel_mul_affinePushTestFn (a b : ℂ) (ha : a ≠ 0) (g : TestFn) (z : ℂ) :
    ∫ w, gffKernel (a * z + b) w * affinePushTestFn a b g w =
      (∫ w, gffKernel z w * g w) + affineDefect a b z * (∫ w, g w) +
        ∫ w, g w * affineDefect a b w := by
  have hcomm : ∀ w, gffKernel (a * z + b) w * affinePushTestFn a b g w =
      affinePushTestFn a b g w * gffKernel (a * z + b) w := fun w => mul_comm _ _
  simp_rw [hcomm]
  rw [integral_affinePushTestFn_mul a b ha g (gffKernel (a * z + b))]
  have hae : (fun y => g y * gffKernel (a * z + b) (a * y + b)) =ᵐ[volume]
      fun y => gffKernel z y * g y + affineDefect a b z * g y + g y * affineDefect a b y := by
    filter_upwards [Measure.ae_ne volume z] with y hy
    rw [gffKernel_affine a b ha (Ne.symm hy)]
    ring
  have h1 : Integrable (fun y => gffKernel z y * g y) := integrable_testKernel_section g z
  have h2 : Integrable (fun y => affineDefect a b z * g y) := (integrable_testFn g).const_mul _
  have h3 : Integrable (fun y => g y * affineDefect a b y) :=
    integrable_testFn_mul (continuous_affineDefect a b) g
  have h12 : Integrable (fun y => gffKernel z y * g y + affineDefect a b z * g y) := h1.add h2
  rw [integral_congr_ae hae, integral_add h12 h3, integral_add h1 h2, integral_const_mul]

end RepinCovariance

/-- Test covariance of the pushed tests. -/
theorem gffCov_affinePush (a b : ℂ) (ha : a ≠ 0) (f g : TestFn) :
    gffCov (affinePushTestFn a b f) (affinePushTestFn a b g) =
      gffCov f g + (∫ y, f y) * (∫ y, g y * affineDefect a b y) +
        (∫ y, g y) * (∫ y, f y * affineDefect a b y) := by
  rw [gffCov_eq_integral_testKernel (affinePushTestFn a b f) (affinePushTestFn a b g),
    gffCov_eq_integral_testKernel f g,
    integral_affinePushTestFn_mul a b ha f
      (fun z => ∫ w, gffKernel z w * affinePushTestFn a b g w)]
  simp_rw [RepinCovariance.integral_gffKernel_mul_affinePushTestFn a b ha g]
  have h1 : Integrable (fun y => f y * ∫ w, gffKernel y w * g w) :=
    RepinCovariance.integrable_testFn_mul (continuous_testKernelPotential g) f
  have h2 : Integrable (fun y => (∫ w, g w) * (f y * affineDefect a b y)) :=
    (RepinCovariance.integrable_testFn_mul (continuous_affineDefect a b) f).const_mul _
  have h3 : Integrable (fun y => (∫ w, g w * affineDefect a b w) * f y) :=
    (RepinCovariance.integrable_testFn f).const_mul _
  have h12 : Integrable (fun y => f y * (∫ w, gffKernel y w * g w) +
      (∫ w, g w) * (f y * affineDefect a b y)) := h1.add h2
  have e : ∀ y, f y * ((∫ w, gffKernel y w * g w) + affineDefect a b y * (∫ w, g w) +
      ∫ w, g w * affineDefect a b w) = f y * (∫ w, gffKernel y w * g w) +
      (∫ w, g w) * (f y * affineDefect a b y) + (∫ w, g w * affineDefect a b w) * f y :=
    fun y => by ring
  simp_rw [e]
  rw [integral_add h12 h3, integral_add h1 h2, integral_const_mul, integral_const_mul]
  ring

/-- Cross energy of a pushed test with the repinning circle. -/
theorem circleCross_repin_affinePush (a b : ℂ) (ha : a ≠ 0) (f : TestFn) :
    circleCross b (-Real.log ‖a‖) (affinePushTestFn a b f) =
      (∫ y, f y * affineDefect a b y) + repinKappa a b * ∫ y, f y := by
  unfold circleCross
  change ∫ y, affinePushTestFn a b f y * repinPotential a b y = _
  rw [integral_affinePushTestFn_mul a b ha f (repinPotential a b)]
  simp_rw [repinPotential_affine a b ha]
  have h1 : Integrable (fun y => f y * affineDefect a b y) :=
    RepinCovariance.integrable_testFn_mul (continuous_affineDefect a b) f
  have h2 : Integrable (fun y => repinKappa a b * f y) :=
    (RepinCovariance.integrable_testFn f).const_mul _
  have e : ∀ y, f y * (affineDefect a b y + repinKappa a b) =
      f y * affineDefect a b y + repinKappa a b * f y := fun y => by ring
  simp_rw [e]
  rw [integral_add h1 h2, integral_const_mul]

/-- Cross energy of a pushed test with a pushed circle. -/
theorem circleCross_affinePush (a b : ℂ) (ha : a ≠ 0) (f : TestFn) (y : ℂ) (r : ℝ) :
    circleCross (a * y + b) (r - Real.log ‖a‖) (affinePushTestFn a b f) =
      circleCross y r f + (∫ v, f v * affineDefect a b v) +
        (∫ v, f v) * ∫ u, affineDefect a b u ∂circleMeasure y r := by
  unfold circleCross
  rw [integral_affinePushTestFn_mul a b ha f
    (fun x => ∫ z, gffKernel x z ∂circleMeasure (a * y + b) (r - Real.log ‖a‖))]
  simp_rw [RepinCovariance.integral_gffKernel_circleMeasure_affine a b ha _ y r]
  have h1 : Integrable (fun v => f v * ∫ u, gffKernel v u ∂circleMeasure y r) :=
    RepinCovariance.integrable_testFn_mul (continuous_circleKernelPotential y r) f
  have h2 : Integrable (fun v => f v * affineDefect a b v) :=
    RepinCovariance.integrable_testFn_mul (continuous_affineDefect a b) f
  have h3 : Integrable (fun v => (∫ u, affineDefect a b u ∂circleMeasure y r) * f v) :=
    (RepinCovariance.integrable_testFn f).const_mul _
  have h12 : Integrable (fun v => f v * (∫ u, gffKernel v u ∂circleMeasure y r) +
      f v * affineDefect a b v) := h1.add h2
  have e : ∀ v, f v * ((∫ u, gffKernel v u ∂circleMeasure y r) + affineDefect a b v +
      ∫ u, affineDefect a b u ∂circleMeasure y r) =
      f v * (∫ u, gffKernel v u ∂circleMeasure y r) + f v * affineDefect a b v +
        (∫ u, affineDefect a b u ∂circleMeasure y r) * f v := fun v => by ring
  simp_rw [e]
  rw [integral_add h12 h3, integral_add h1 h2, integral_const_mul]
  ring

/-- Double circle energy of two pushed circles. -/
theorem circleEnergy_affine (a b : ℂ) (ha : a ≠ 0) (y y' : ℂ) (r r' : ℝ) :
    ∫ u, ∫ v, gffKernel u v ∂circleMeasure (a * y' + b) (r' - Real.log ‖a‖)
        ∂circleMeasure (a * y + b) (r - Real.log ‖a‖) =
      (∫ u, ∫ v, gffKernel u v ∂circleMeasure y' r' ∂circleMeasure y r) +
        (∫ u, affineDefect a b u ∂circleMeasure y r) +
        ∫ u, affineDefect a b u ∂circleMeasure y' r' := by
  have _ := circleMeasure_isProbability y r
  rw [← circleMeasure_map_affine a b ha y r,
    integral_map (by fun_prop)
      (continuous_circleKernelPotential (a * y' + b) (r' - Real.log ‖a‖)).aestronglyMeasurable]
  simp_rw [RepinCovariance.integral_gffKernel_circleMeasure_affine a b ha _ y' r']
  have h1 : Integrable (fun u => ∫ v, gffKernel u v ∂circleMeasure y' r') (circleMeasure y r) :=
    RepinCovariance.integrable_circleMeasure_of_continuous
      (continuous_circleKernelPotential y' r') y r
  have h2 : Integrable (affineDefect a b) (circleMeasure y r) :=
    integrable_affineDefect_circleMeasure a b ha y r
  have h12 : Integrable (fun u => (∫ v, gffKernel u v ∂circleMeasure y' r') +
      affineDefect a b u) (circleMeasure y r) := h1.add h2
  rw [integral_add h12 (integrable_const _), integral_add h1 h2, integral_const, probReal_univ,
    one_smul]

end DOZZ.Proofs

end

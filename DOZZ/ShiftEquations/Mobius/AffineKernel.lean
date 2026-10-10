/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.GffKernel
public import DOZZ.Statements.Defs.CircleMeasure
import DOZZ.GFFStructure.CirclePotential

/-!
# The affine metric defect of the equator kernel

Under an affine map `u ↦ a * u + b` with `a ≠ 0`, the logarithmic singularity of the equator
kernel `gffKernel` rescales by the constant `‖a‖`, while the two pinning terms `log |·|₊` change
by a bounded continuous function of the base point. This file records the resulting additive
decomposition `gffKernel (a y + b) (a y' + b) = gffKernel y y' + d y + d y'` with the affine
metric defect `d`, the boundedness and continuity of `d`, the vanishing of the unit-circle
average of the kernel, and the fact that affine images of circle measures are circle measures.
-/

@[expose] public section

open MeasureTheory Set

namespace DOZZ.Proofs

/-- The affine metric defect `d(y) = log|a y + b|₊ − log|y|₊ − ½ log|a|`. -/
noncomputable def affineDefect (a b : ℂ) (y : ℂ) : ℝ :=
  Real.log (normPlus (a * y + b)) - Real.log (normPlus y) - Real.log ‖a‖ / 2

/-- The equator kernel changes by the defect at both points under an affine map. -/
theorem gffKernel_affine (a b : ℂ) (ha : a ≠ 0) {y y' : ℂ} (hyy : y ≠ y') :
    gffKernel (a * y + b) (a * y' + b) =
      gffKernel y y' + affineDefect a b y + affineDefect a b y' := by
  have hna : ‖a‖ ≠ 0 := norm_ne_zero_iff.mpr ha
  have hny : ‖y - y'‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hyy)
  have hsub : (a * y + b) - (a * y' + b) = a * (y - y') := by ring
  unfold gffKernel affineDefect
  rw [hsub, norm_mul, Real.log_mul hna hny]
  ring

/-- The affine metric defect is continuous. -/
theorem continuous_affineDefect (a b : ℂ) : Continuous (affineDefect a b) := by
  unfold affineDefect
  exact ((continuous_log_normPlus.comp (by fun_prop :
    Continuous fun y : ℂ => a * y + b)).sub continuous_log_normPlus).sub continuous_const

namespace AffineKernel

/-- The pinning weight is at most multiplied by `‖c‖ + ‖d‖ + 1` under `z ↦ c z + d`. -/
theorem normPlus_affine_le (c d z : ℂ) :
    normPlus (c * z + d) ≤ (‖c‖ + ‖d‖ + 1) * normPlus z := by
  have hz1 : 1 ≤ normPlus z := le_max_left _ _
  have hz2 : ‖z‖ ≤ normPlus z := le_max_right _ _
  have hc := norm_nonneg c
  have hd := norm_nonneg d
  refine max_le ?_ ?_
  · nlinarith
  · calc ‖c * z + d‖ ≤ ‖c * z‖ + ‖d‖ := norm_add_le _ _
      _ = ‖c‖ * ‖z‖ + ‖d‖ := by rw [norm_mul]
      _ ≤ (‖c‖ + ‖d‖ + 1) * normPlus z := by nlinarith [mul_le_mul_of_nonneg_left hz2 hc]

/-- Logarithmic form of `normPlus_affine_le`. -/
theorem log_normPlus_affine_le (c d z : ℂ) :
    Real.log (normPlus (c * z + d)) ≤
      Real.log (‖c‖ + ‖d‖ + 1) + Real.log (normPlus z) := by
  have hz : 0 < normPlus z := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hK : 0 < ‖c‖ + ‖d‖ + 1 := by positivity
  rw [← Real.log_mul hK.ne' hz.ne']
  exact Real.log_le_log (lt_of_lt_of_le one_pos (le_max_left _ _)) (normPlus_affine_le c d z)

/-- The logarithmic growth constant of `z ↦ c z + d` is nonnegative. -/
theorem log_affine_const_nonneg (c d : ℂ) : 0 ≤ Real.log (‖c‖ + ‖d‖ + 1) :=
  Real.log_nonneg (by linarith [norm_nonneg c, norm_nonneg d])

end AffineKernel

/-- The defect is bounded on the whole plane. -/
theorem exists_abs_affineDefect_le (a b : ℂ) (ha : a ≠ 0) :
    ∃ C : ℝ, ∀ y : ℂ, |affineDefect a b y| ≤ C := by
  refine ⟨Real.log (‖a‖ + ‖b‖ + 1) + Real.log (‖a⁻¹‖ + ‖-(a⁻¹ * b)‖ + 1) +
    |Real.log ‖a‖| / 2, fun y => ?_⟩
  have h1 := AffineKernel.log_normPlus_affine_le a b y
  have h2 := AffineKernel.log_normPlus_affine_le a⁻¹ (-(a⁻¹ * b)) (a * y + b)
  have hy : a⁻¹ * (a * y + b) + -(a⁻¹ * b) = y := by
    rw [mul_add, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
    ring
  rw [hy] at h2
  have h3 := AffineKernel.log_affine_const_nonneg a b
  have h4 := AffineKernel.log_affine_const_nonneg a⁻¹ (-(a⁻¹ * b))
  have h5 := neg_abs_le (Real.log ‖a‖)
  have h6 := le_abs_self (Real.log ‖a‖)
  unfold affineDefect
  rw [abs_le]
  constructor <;> linarith

/-- The equator kernel has vanishing average over the unit circle (radius `e^0 = 1`). -/
theorem integral_gffKernel_circleMeasure_unit (y : ℂ) :
    ∫ u, gffKernel y u ∂circleMeasure 0 0 = 0 := by
  rw [integral_gffKernel_circleMeasure, integral_log_normPlus_circleMeasure_origin_eq_max]
  simp [normPlus]

namespace AffineKernel

/-- An affine map sends a circle parametrization to a rotated, rescaled circle parametrization. -/
theorem affine_circleMap (a b y : ℂ) (R θ : ℝ) :
    a * circleMap y R θ + b = circleMap (a * y + b) (‖a‖ * R) (θ + Complex.arg a) := by
  have h := Complex.norm_mul_exp_arg_mul_I a
  simp only [circleMap]
  push_cast
  rw [add_mul, Complex.exp_add]
  linear_combination (-(R * Complex.exp (θ * Complex.I))) * h

/-- Rotating the parameter of a `2π`-periodic map preserves the pushforward of arclength. -/
theorem map_restrict_Ioc_add_periodic {β : Type*} [MeasurableSpace β] {g : ℝ → β}
    (hg : Measurable g) (hper : Function.Periodic g (2 * Real.pi)) (φ : ℝ) :
    (volume.restrict (Ioc 0 (2 * Real.pi))).map (fun θ => g (θ + φ)) =
      (volume.restrict (Ioc 0 (2 * Real.pi))).map g := by
  have hT : 0 < 2 * Real.pi := Real.two_pi_pos
  have hgφ : Measurable (fun θ => g (θ + φ)) := hg.comp (measurable_add_const φ)
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply hgφ hs, Measure.map_apply hg hs, Measure.restrict_apply (hgφ hs),
    Measure.restrict_apply (hg hs)]
  have hA : MeasurableSet (g ⁻¹' s) := hg hs
  have hinv : ∀ k : AddSubgroup.zmultiples (2 * Real.pi),
      (fun x => k +ᵥ x) ⁻¹' (g ⁻¹' s) = g ⁻¹' s := by
    intro k
    ext x
    simp only [mem_preimage, hper.map_vadd_zmultiples]
  have : VAddInvariantMeasure (AddSubgroup.zmultiples (2 * Real.pi)) ℝ volume :=
    ⟨fun c s _ => measure_preimage_add _ _ _⟩
  have hset : (fun θ => g (θ + φ)) ⁻¹' s ∩ Ioc 0 (2 * Real.pi) =
      (fun θ => θ + φ) ⁻¹' (g ⁻¹' s ∩ Ioc φ (φ + 2 * Real.pi)) := by
    ext θ
    simp only [mem_inter_iff, mem_preimage, mem_Ioc]
    constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h1, by linarith, by linarith⟩
  rw [hset, measure_preimage_add_right]
  have h := (isAddFundamentalDomain_Ioc hT φ).measure_set_eq
    (isAddFundamentalDomain_Ioc hT 0) hA hinv
  rw [zero_add] at h
  exact h

end AffineKernel

/-- Affine images of circle measures are circle measures. -/
theorem circleMeasure_map_affine (a b : ℂ) (ha : a ≠ 0) (y : ℂ) (r : ℝ) :
    (circleMeasure y r).map (fun u => a * u + b) =
      circleMeasure (a * y + b) (r - Real.log ‖a‖) := by
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hR : Real.exp (-(r - Real.log ‖a‖)) = ‖a‖ * Real.exp (-r) := by
    rw [neg_sub, sub_eq_add_neg, Real.exp_add, Real.exp_log hna]
  have hmeas : Measurable (fun u : ℂ => a * u + b) := by fun_prop
  rw [circleMeasure, circleMeasure, Measure.map_smul _ hmeas.aemeasurable,
    Measure.map_map hmeas (measurable_circleMap _ _), hR]
  congr 1
  have hcomp : (fun u : ℂ => a * u + b) ∘ circleMap y (Real.exp (-r)) =
      fun θ => circleMap (a * y + b) (‖a‖ * Real.exp (-r)) (θ + Complex.arg a) := by
    funext θ
    exact AffineKernel.affine_circleMap a b y _ θ
  rw [hcomp]
  exact AffineKernel.map_restrict_Ioc_add_periodic (measurable_circleMap _ _)
    (periodic_circleMap _ _) _

end DOZZ.Proofs

end

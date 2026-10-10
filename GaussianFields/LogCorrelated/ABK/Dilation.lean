/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import GaussianFields.LogCorrelated.ABK.Constants

/-!
# GaussianFields.LogCorrelated/ABK/Dilation

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory
open scoped ENNReal Topology

namespace GaussianFields


/-- The real dimension of `Vec d`. -/
@[simp]
theorem finrank_real_vec (d : Nat) : Module.finrank ℝ (Vec d) = d := by
  simp [Vec]

/-- Change variables by `x ↦ r⁻¹ x` in `Vec d`. -/
theorem integral_comp_inv_smul_vec {d : Nat} (f : Vec d → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    (∫ x : Vec d, f (r⁻¹ • x) ∂(volume : Measure (Vec d))) =
      r ^ d * ∫ x : Vec d, f x ∂(volume : Measure (Vec d)) := by
  have hraw :=
    MeasureTheory.Measure.integral_comp_inv_smul_of_nonneg
      (μ := (volume : Measure (Vec d))) f (R := r) hr
  simpa [finrank_real_vec, smul_eq_mul] using hraw

/-- Inverse form of the positive dilation change of variables. -/
theorem integral_eq_pow_mul_integral_comp_smul_vec {d : Nat} (f : Vec d → ℝ)
    {r : ℝ} (hr : 0 < r) :
    (∫ x : Vec d, f x ∂(volume : Measure (Vec d))) =
      r ^ d * ∫ x : Vec d, f (r • x) ∂(volume : Measure (Vec d)) := by
  have hraw :=
    MeasureTheory.Measure.integral_comp_smul_of_nonneg
      (μ := (volume : Measure (Vec d))) f r (hR := hr.le)
  have hr_pow_ne : r ^ d ≠ 0 := pow_ne_zero d hr.ne'
  have h :
      (∫ x : Vec d, f (r • x) ∂(volume : Measure (Vec d))) =
        (r ^ d)⁻¹ * ∫ x : Vec d, f x ∂(volume : Measure (Vec d)) := by
    simpa [finrank_real_vec, smul_eq_mul] using hraw
  calc
    (∫ x : Vec d, f x ∂(volume : Measure (Vec d)))
        = r ^ d * ((r ^ d)⁻¹ *
            ∫ x : Vec d, f x ∂(volume : Measure (Vec d))) := by
            field_simp [hr_pow_ne]
    _ = r ^ d * ∫ x : Vec d, f (r • x) ∂(volume : Measure (Vec d)) := by
            rw [h]

/-- The scaled self-convolution `(ζ_r * ζ_r)(x)`. -/
@[expose]
noncomputable def abkScaledCutoffSelfConvolution {d : Nat} (ζ : ABKCutoff d)
    (r : ℝ) (x : Vec d) : ℝ :=
  ∫ y : Vec d, abkScaledCutoff ζ r y * abkScaledCutoff ζ r (x - y)

/-- The scaled cutoff self-convolution obeys the exact ABK dilation law
`(ζ_r * ζ_r)(x) = r^d (ζ * ζ)(x/r)` for positive `r`. -/
theorem abkScaledCutoffSelfConvolution_eq_pow_mul {d : Nat} (ζ : ABKCutoff d)
    {r : ℝ} (hr : 0 < r) (x : Vec d) :
    abkScaledCutoffSelfConvolution ζ r x =
      r ^ d * abkCutoffSelfConvolution ζ (r⁻¹ • x) := by
  let F : Vec d → ℝ := fun u => ζ u * ζ (r⁻¹ • x - u)
  have hscale := integral_comp_inv_smul_vec (d := d) F hr.le
  unfold abkScaledCutoffSelfConvolution abkCutoffSelfConvolution abkScaledCutoff
  rw [← hscale]
  refine integral_congr_ae ?_
  filter_upwards with y
  have hsub : r⁻¹ • (x - y) = r⁻¹ • x - r⁻¹ • y := by
    ext i
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  simp [F, hsub]

/-- The `L²` mass of the scaled cutoff is `r^d M_0`. -/
theorem integral_sq_abkScaledCutoff_eq_pow_mul {d : Nat} (ζ : ABKCutoff d)
    {r : ℝ} (hr : 0 < r) :
    (∫ y : Vec d, (abkScaledCutoff ζ r y) ^ (2 : Nat)
        ∂(volume : Measure (Vec d))) =
      r ^ d * abkM0 ζ := by
  let F : Vec d → ℝ := fun y => (ζ y) ^ (2 : Nat)
  have hscale := integral_comp_inv_smul_vec (d := d) F hr.le
  simpa [F, abkScaledCutoff, abkM0] using hscale

/-- The scaled cutoff is even, inherited from radiality of the ABK cutoff. -/
theorem abkScaledCutoff_neg {d : Nat} (ζ : ABKCutoff d) (r : ℝ) (x : Vec d) :
    abkScaledCutoff ζ r (-x) = abkScaledCutoff ζ r x := by
  unfold abkScaledCutoff
  have hsmul : r⁻¹ • (-x) = -(r⁻¹ • x) := by
    ext i
    simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    ring
  exact ζ.radial _ _ (by rw [hsmul, euclideanNorm_neg])

/-- The overlap of two translated scaled cutoffs is the scaled cutoff self-convolution at the
separation vector. -/
theorem integral_abkScaledCutoff_mul_abkScaledCutoff_sub_eq_selfConvolution {d : Nat}
    (ζ : ABKCutoff d) (r : ℝ) (x z : Vec d) :
    (∫ y : Vec d,
        abkScaledCutoff ζ r (x - y) * abkScaledCutoff ζ r (z - y)
        ∂(volume : Measure (Vec d))) =
      abkScaledCutoffSelfConvolution ζ r (x - z) := by
  let F : Vec d → ℝ := fun u =>
    abkScaledCutoff ζ r u * abkScaledCutoff ζ r (z - x + u)
  have hneg :
      (∫ y : Vec d, F (-y) ∂(volume : Measure (Vec d))) =
        ∫ y : Vec d, F y ∂(volume : Measure (Vec d)) := by
    exact
      (Measure.measurePreserving_neg (volume : Measure (Vec d))).integral_comp
        (Homeomorph.neg (Vec d)).measurableEmbedding F
  have htrans :
      (∫ y : Vec d, F (x - y) ∂(volume : Measure (Vec d))) =
        ∫ y : Vec d, F (-y) ∂(volume : Measure (Vec d)) := by
    have h :=
      (MeasureTheory.measurePreserving_add_right (volume : Measure (Vec d)) (-x)).integral_comp'
        (f := MeasurableEquiv.addRight (-x)) (fun y : Vec d => F (-y))
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  calc
    (∫ y : Vec d,
        abkScaledCutoff ζ r (x - y) * abkScaledCutoff ζ r (z - y)
        ∂(volume : Measure (Vec d)))
        = ∫ y : Vec d, F (x - y) ∂(volume : Measure (Vec d)) := by
            refine integral_congr_ae ?_
            filter_upwards with y
            dsimp [F]
            have harg : z - x + (x - y) = z - y := by
              ext i
              simp only [Pi.add_apply, Pi.sub_apply]
              ring
            rw [harg]
    _ = ∫ y : Vec d, F y ∂(volume : Measure (Vec d)) := by
          rw [htrans, hneg]
    _ = abkScaledCutoffSelfConvolution ζ r (x - z) := by
          unfold abkScaledCutoffSelfConvolution
          refine integral_congr_ae ?_
          filter_upwards with y
          dsimp [F]
          have harg : z - x + y = -(x - z - y) := by
            ext i
            simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
            ring
          rw [harg, abkScaledCutoff_neg]

/-- The `L²` mass of the translated scaled cutoff is independent of the center. -/
theorem integral_sq_abkScaledCutoff_sub_eq_pow_mul {d : Nat} (ζ : ABKCutoff d)
    {r : ℝ} (hr : 0 < r) (x : Vec d) :
    (∫ y : Vec d, (abkScaledCutoff ζ r (x - y)) ^ (2 : Nat)
        ∂(volume : Measure (Vec d))) =
      r ^ d * abkM0 ζ := by
  let F : Vec d → ℝ := fun y => (abkScaledCutoff ζ r y) ^ (2 : Nat)
  have hneg :
      (∫ y : Vec d, F (-y) ∂(volume : Measure (Vec d))) =
        ∫ y : Vec d, F y ∂(volume : Measure (Vec d)) := by
    exact
      (Measure.measurePreserving_neg (volume : Measure (Vec d))).integral_comp
        (Homeomorph.neg (Vec d)).measurableEmbedding F
  have htrans :
      (∫ y : Vec d, F (x - y) ∂(volume : Measure (Vec d))) =
        ∫ y : Vec d, F (-y) ∂(volume : Measure (Vec d)) := by
    have h :=
      (MeasureTheory.measurePreserving_add_right (volume : Measure (Vec d)) (-x)).integral_comp'
        (f := MeasurableEquiv.addRight (-x)) (fun y : Vec d => F (-y))
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  calc
    (∫ y : Vec d, (abkScaledCutoff ζ r (x - y)) ^ (2 : Nat)
        ∂(volume : Measure (Vec d)))
        = ∫ y : Vec d, F (x - y) ∂(volume : Measure (Vec d)) := rfl
    _ = ∫ y : Vec d, F (-y) ∂(volume : Measure (Vec d)) := htrans
    _ = ∫ y : Vec d, F y ∂(volume : Measure (Vec d)) := hneg
    _ = r ^ d * abkM0 ζ := integral_sq_abkScaledCutoff_eq_pow_mul ζ hr

end GaussianFields

end

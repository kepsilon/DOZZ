/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

public import Mathlib.MeasureTheory.Group.MeasurableEquiv
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import GaussianFields.LogCorrelated.ABK.Radial

/-!
# GaussianFields.LogCorrelated/ABK/Witness

Port of the corresponding GaussianFields source module.
-/

public section

open MeasureTheory

namespace GaussianFields


/-! ## The scalar profile -/

/-- The piecewise-linear radial profile: `1` on `[0, 1/2]`, linearly decreasing
on `[1/2, 1]`, `0` on `[1, ∞)`. -/
@[expose]
noncomputable def abkStandardProfile (r : ℝ) : ℝ :=
  min (max (2 * (1 - r)) 0) 1

theorem abkStandardProfile_of_le_half {r : ℝ} (hr : r ≤ 1 / 2) :
    abkStandardProfile r = 1 := by
  have h1 : (1 : ℝ) ≤ 2 * (1 - r) := by linarith
  have h2 : (1 : ℝ) ≤ max (2 * (1 - r)) 0 := h1.trans (le_max_left _ _)
  simpa [abkStandardProfile] using min_eq_right h2

theorem abkStandardProfile_of_one_le {r : ℝ} (hr : 1 ≤ r) :
    abkStandardProfile r = 0 := by
  have h1 : 2 * (1 - r) ≤ 0 := by linarith
  simp [abkStandardProfile, max_eq_right h1]

theorem abkStandardProfile_nonneg (r : ℝ) : 0 ≤ abkStandardProfile r :=
  le_min (le_max_right _ _) zero_le_one

theorem abkStandardProfile_le_one (r : ℝ) : abkStandardProfile r ≤ 1 :=
  min_le_right _ _

theorem lipschitzWith_abkStandardProfile : LipschitzWith 2 abkStandardProfile := by
  have hbase : LipschitzWith 2 (fun r : ℝ => 2 * (1 - r)) := by
    refine LipschitzWith.of_dist_le_mul fun r s => ?_
    rw [Real.dist_eq, Real.dist_eq]
    have : 2 * (1 - r) - 2 * (1 - s) = -(2 * (r - s)) := by ring
    rw [this, abs_neg, abs_mul]
    simp
  exact (hbase.max_const 0).min_const 1

/-! ## Euclidean-norm helpers -/

theorem euclideanNorm_zero {d : Nat} : euclideanNorm (0 : Vec d) = 0 := by
  simp [euclideanNorm, euclideanNormSq, euclideanDot, Real.sqrt_zero]

/-- Reverse triangle inequality for the project Euclidean norm. -/
theorem abs_euclideanNorm_sub_euclideanNorm_le {d : Nat} (x y : Vec d) :
    |euclideanNorm x - euclideanNorm y| ≤ euclideanNorm (x - y) := by
  have hxy : y + (x - y) = x := by
    ext i
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hyx : x + (y - x) = y := by
    ext i
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have h1 : euclideanNorm x - euclideanNorm y ≤ euclideanNorm (x - y) := by
    have := euclideanNorm_add_le y (x - y)
    rw [hxy] at this
    linarith
  have h2 : euclideanNorm y - euclideanNorm x ≤ euclideanNorm (x - y) := by
    have := euclideanNorm_add_le x (y - x)
    rw [hyx] at this
    rw [euclideanNorm_sub_comm] at this
    linarith
  exact abs_le.mpr ⟨by linarith, h1⟩

/-! ## The standard cutoff -/

/-- The standard piecewise-linear radial ABK cutoff witness. -/
@[expose]
noncomputable def abkStandardCutoffFun (d : Nat) : Vec d → ℝ :=
  fun x => abkStandardProfile (euclideanNorm x)

theorem continuous_abkStandardCutoffFun (d : Nat) :
    Continuous (abkStandardCutoffFun d) :=
  lipschitzWith_abkStandardProfile.continuous.comp continuous_euclideanNorm

theorem abkStandardCutoffFun_support_subset (d : Nat) :
    Function.support (abkStandardCutoffFun d) ⊆ {x | euclideanNorm x ≤ 1} := by
  intro x hx
  by_contra h
  have h1 : 1 ≤ euclideanNorm x := le_of_lt (by simpa using h)
  exact hx (abkStandardProfile_of_one_le h1)

theorem hasCompactSupport_abkStandardCutoffFun (d : Nat) :
    HasCompactSupport (abkStandardCutoffFun d) :=
  HasCompactSupport.of_support_subset_isCompact
    (isCompact_euclideanClosedBall (d := d) 1)
    (abkStandardCutoffFun_support_subset d)

/-- The standard witness for `ABKCutoff d`: the structure is inhabited. -/
@[expose]
noncomputable def abkStandardCutoff (d : Nat) : ABKCutoff d where
  toFun := abkStandardCutoffFun d
  continuous := continuous_abkStandardCutoffFun d
  hasCompactSupport := hasCompactSupport_abkStandardCutoffFun d
  memLp_two :=
    (continuous_abkStandardCutoffFun d).memLp_of_hasCompactSupport
      (hasCompactSupport_abkStandardCutoffFun d)
  support_subset_unitBall := abkStandardCutoffFun_support_subset d
  eq_one_of_norm_le_half := fun _ hx => abkStandardProfile_of_le_half hx
  nonneg := fun x => abkStandardProfile_nonneg _
  le_one := fun x => abkStandardProfile_le_one _
  radial := fun x y h => by simp only [abkStandardCutoffFun, h]
  lipschitz := by
    refine ⟨2, by norm_num, fun x y => ?_⟩
    have h1 : |abkStandardProfile (euclideanNorm x) -
        abkStandardProfile (euclideanNorm y)| ≤
        2 * |euclideanNorm x - euclideanNorm y| := by
      have := lipschitzWith_abkStandardProfile.dist_le_mul
        (euclideanNorm x) (euclideanNorm y)
      simpa [Real.dist_eq] using this
    have h2 := abs_euclideanNorm_sub_euclideanNorm_le x y
    calc |abkStandardCutoffFun d x - abkStandardCutoffFun d y|
        ≤ 2 * |euclideanNorm x - euclideanNorm y| := h1
      _ ≤ 2 * euclideanNorm (x - y) := by linarith

instance (d : Nat) : Nonempty (ABKCutoff d) := ⟨abkStandardCutoff d⟩

/-- Non-triviality certificate: the standard cutoff is `1` at the origin. -/
theorem abkStandardCutoff_apply_zero (d : Nat) :
    abkStandardCutoff d (0 : Vec d) = 1 := by
  show abkStandardProfile (euclideanNorm (0 : Vec d)) = 1
  rw [euclideanNorm_zero]
  exact abkStandardProfile_of_le_half (by norm_num)

/-! ## The standard mean-zero test function -/

/-- The translation vector used by the mean-zero witness. -/
@[expose]
def abkWitnessShift (d : Nat) : Vec d := fun _ => 3

/-- The translate-difference witness function `ζ(x) - ζ(x - v)`. -/
@[expose]
noncomputable def abkStandardMeanZeroFun (d : Nat) : Vec d → ℝ :=
  fun x => abkStandardCutoffFun d x - abkStandardCutoffFun d (x - abkWitnessShift d)

theorem continuous_abkStandardMeanZeroFun (d : Nat) :
    Continuous (abkStandardMeanZeroFun d) :=
  (continuous_abkStandardCutoffFun d).sub
    ((continuous_abkStandardCutoffFun d).comp
      (continuous_id.sub continuous_const))

theorem hasCompactSupport_abkStandardMeanZeroFun (d : Nat) :
    HasCompactSupport (abkStandardMeanZeroFun d) := by
  have htrans : HasCompactSupport
      (fun x : Vec d => abkStandardCutoffFun d (x - abkWitnessShift d)) := by
    have hcomp := (hasCompactSupport_abkStandardCutoffFun d).comp_homeomorph
      (Homeomorph.subRight (abkWitnessShift d))
    change HasCompactSupport
      (fun x => abkStandardCutoffFun d (Homeomorph.subRight (abkWitnessShift d) x)) at hcomp
    simpa only [Homeomorph.subRight_apply] using hcomp
  exact (hasCompactSupport_abkStandardCutoffFun d).sub htrans

/-- The standard witness for `MeanZeroTestFunction d`: the structure is
inhabited. -/
@[expose]
noncomputable def abkStandardMeanZeroTestFunction (d : Nat) :
    MeanZeroTestFunction d where
  toFun := abkStandardMeanZeroFun d
  continuous := continuous_abkStandardMeanZeroFun d
  hasCompactSupport := hasCompactSupport_abkStandardMeanZeroFun d
  integrable :=
    (continuous_abkStandardMeanZeroFun d).integrable_of_hasCompactSupport
      (hasCompactSupport_abkStandardMeanZeroFun d)
  memLp_two :=
    (continuous_abkStandardMeanZeroFun d).memLp_of_hasCompactSupport
      (hasCompactSupport_abkStandardMeanZeroFun d)
  integral_eq_zero := by
    have hint : Integrable (abkStandardCutoffFun d) (volume : Measure (Vec d)) :=
      (continuous_abkStandardCutoffFun d).integrable_of_hasCompactSupport
        (hasCompactSupport_abkStandardCutoffFun d)
    have hshift :
        (∫ x, abkStandardCutoffFun d (x - abkWitnessShift d)
          ∂(volume : Measure (Vec d))) =
        ∫ x, abkStandardCutoffFun d x ∂(volume : Measure (Vec d)) :=
      integral_sub_right_eq_self (abkStandardCutoffFun d) (abkWitnessShift d)
    have hshift_int : Integrable
        (fun x : Vec d => abkStandardCutoffFun d (x - abkWitnessShift d))
        (volume : Measure (Vec d)) := by
      have htrans : HasCompactSupport
          (fun x : Vec d => abkStandardCutoffFun d (x - abkWitnessShift d)) := by
        have hcomp := (hasCompactSupport_abkStandardCutoffFun d).comp_homeomorph
          (Homeomorph.subRight (abkWitnessShift d))
        change HasCompactSupport
          (fun x => abkStandardCutoffFun d (Homeomorph.subRight (abkWitnessShift d) x)) at hcomp
        simpa only [Homeomorph.subRight_apply] using hcomp
      exact ((continuous_abkStandardCutoffFun d).comp
        (continuous_id.sub continuous_const)).integrable_of_hasCompactSupport htrans
    simp only [abkStandardMeanZeroFun]
    rw [integral_sub hint hshift_int, hshift, sub_self]

instance (d : Nat) : Nonempty (MeanZeroTestFunction d) :=
  ⟨abkStandardMeanZeroTestFunction d⟩

/-- Non-triviality certificate: in positive dimension the mean-zero witness is
`1` at the origin (the translated bump does not reach the origin). -/
theorem abkStandardMeanZeroTestFunction_apply_zero {d : Nat} (hd : 0 < d) :
    abkStandardMeanZeroTestFunction d (0 : Vec d) = 1 := by
  have hnorm : euclideanNorm ((0 : Vec d) - abkWitnessShift d) =
      euclideanNorm (abkWitnessShift d) := by
    rw [zero_sub, euclideanNorm_neg]
  have hlarge : (1 : ℝ) ≤ euclideanNorm (abkWitnessShift d) := by
    have := abs_apply_le_euclideanNorm (abkWitnessShift d) ⟨0, hd⟩
    have h3 : |abkWitnessShift d ⟨0, hd⟩| = 3 := by
      simp [abkWitnessShift]
    linarith [this, h3.symm.le]
  show abkStandardCutoffFun d 0 -
      abkStandardCutoffFun d ((0 : Vec d) - abkWitnessShift d) = 1
  have h1 : abkStandardCutoffFun d (0 : Vec d) = 1 := by
    show abkStandardProfile (euclideanNorm (0 : Vec d)) = 1
    rw [euclideanNorm_zero]
    exact abkStandardProfile_of_le_half (by norm_num)
  have h2 : abkStandardCutoffFun d ((0 : Vec d) - abkWitnessShift d) = 0 := by
    show abkStandardProfile _ = 0
    rw [hnorm]
    exact abkStandardProfile_of_one_le hlarge
  rw [h1, h2, sub_zero]

end GaussianFields

end

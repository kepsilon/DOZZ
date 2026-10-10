/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Residue.ComplementMass
public import DOZZ.Statements.Correlations.UniformPositiveC1Family
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! Globally bounded local weights agreeing with the Coulomb density on insertion balls. -/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- Only the real weight outside the insertion ball is truncated. The local insertion mass
uses its exact Coulomb density on the whole unit ball. -/
noncomputable def residueLocalWeight (γ S α : ℝ) (w x : ℂ) : ℝ :=
  (min (max 1 ‖x‖) 10) ^ (γ * S) / (max 1 ‖x - w‖) ^ (γ * α)

/-- The truncations are inactive throughout each admissible insertion ball. -/
theorem residue_localWeight_eq (γ S α : ℝ) (z w x : ℂ)
    (hz : 2 ≤ ‖z‖) (hz8 : ‖z‖ ≤ 8) (hzw : 3 ≤ ‖z - w‖)
    (hx : x ∈ Metric.ball z 1) :
    residueLocalWeight γ S α w x = ‖x‖ ^ (γ * S) / ‖x - w‖ ^ (γ * α) := by
  have hd : ‖x - z‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
  have hzx : ‖z‖ ≤ ‖x - z‖ + ‖x‖ := by
    have hh := norm_add_le (z - x) x
    simpa only [norm_sub_rev, sub_add_cancel] using hh
  have hxx : ‖x‖ ≤ ‖x - z‖ + ‖z‖ := by
    simpa only [sub_add_cancel] using norm_add_le (x - z) z
  have hsep : ‖z - w‖ ≤ ‖x - z‖ + ‖x - w‖ := by
    have hh := norm_add_le (z - x) (x - w)
    rw [sub_add_sub_cancel] at hh
    rwa [norm_sub_rev z x] at hh
  have hx1 : 1 ≤ ‖x‖ := by linarith only [hz, hd, hzx]
  have hx10 : ‖x‖ ≤ 10 := by linarith only [hz8, hd, hxx]
  have hxw1 : 1 ≤ ‖x - w‖ := by linarith only [hzw, hd, hsep]
  unfold residueLocalWeight
  rw [max_eq_right hx1, min_eq_left hx10, max_eq_right hxw1]

/-- A local weight is positive, including its globally truncated values. -/
theorem residue_localWeight_pos (γ S α : ℝ) (w x : ℂ) :
    0 < residueLocalWeight γ S α w x := by
  have hn : 0 < min (max 1 ‖x‖) (10 : ℝ) := lt_min (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (by norm_num)
  have hd : 0 < max (1 : ℝ) ‖x - w‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  exact div_pos (Real.rpow_pos_of_pos hn _) (Real.rpow_pos_of_pos hd _)

/-- Uniform global bound over a bounded nonnegative total-charge interval. -/
theorem residue_localWeight_le (γ S α Smax : ℝ) (hγ : 0 ≤ γ) (hS : 0 ≤ S)
    (hSmax : S ≤ Smax) (hα : 0 ≤ α) (w x : ℂ) :
    residueLocalWeight γ S α w x ≤ (10 : ℝ) ^ (γ * Smax) := by
  have hn : 0 ≤ min (max 1 ‖x‖) (10 : ℝ) := le_min (by positivity) (by norm_num)
  have hd : 1 ≤ (max (1 : ℝ) ‖x - w‖) ^ (γ * α) :=
    Real.one_le_rpow (le_max_left _ _) (mul_nonneg hγ hα)
  unfold residueLocalWeight
  calc _ ≤ (min (max 1 ‖x‖) (10 : ℝ)) ^ (γ * S) :=
      div_le_self (Real.rpow_nonneg hn _) hd
    _ ≤ (10 : ℝ) ^ (γ * S) := Real.rpow_le_rpow hn (min_le_right _ _) (mul_nonneg hγ hS)
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_left hSmax hγ)

/-- Jointly smooth untruncated local density, away from zero and the other insertion. -/
theorem residue_localDensity_contDiffAt (γ S α : ℝ) (w : ℂ) (t : ℝ × ℂ)
    (h0 : t.2 ≠ 0) (hw : t.2 ≠ w) :
    ContDiffAt ℝ 1 (fun u : ℝ × ℂ => ‖u.2‖ ^ (γ * (S + u.1)) /
      ‖u.2 - w‖ ^ (γ * α)) t := by
  have hn : ContDiffAt ℝ 1 (fun u : ℝ × ℂ => ‖u.2‖) t :=
    contDiffAt_snd.norm ℂ h0
  have hd : ContDiffAt ℝ 1 (fun u : ℝ × ℂ => ‖u.2 - w‖) t :=
    (contDiffAt_snd.sub contDiffAt_const).norm ℂ (sub_ne_zero.mpr hw)
  exact (hn.rpow (contDiffAt_const.mul (contDiffAt_const.add contDiffAt_fst)) (norm_ne_zero_iff.mpr h0)).div
    (hd.rpow_const_of_ne (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hw)))
    (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hw)) _).ne'

end DOZZ.Proofs

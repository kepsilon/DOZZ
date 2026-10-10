/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.FusionDiskGeometry
public import DOZZ.FourPoint.RetainedAnnuliNestedCharts

/-! Concrete retained-disk geometry for two separated fusion scales. -/

@[expose] public section

open Set

namespace DOZZ.Proofs

/-- The normalized inner and outer fusion disks fit one strict chart and have a fixed gap. -/
theorem fusion_normalized_disks (r s d : ℝ) (hr : 0 < r) (hs : 0 < s)
    (hrs : 100 * r ≤ s) (hd : d ≤ 1 / 4) (j : Fin 5) :
    0 < (r / s) / 800 ∧ (r / s) / 800 ≤ 1 / 8 ∧
      ‖(((9 / 16 : ℝ) * (r / s) : ℝ) : ℂ)‖ + (r / s) / 800 ≤ 3 / 4 ∧
      ‖(((4 + (j.val : ℝ) / 5) / 8 : ℝ) : ℂ)‖ + 1 / 800 ≤ 3 / 4 ∧
      (r / s) / 800 + 1 / 800 + d ≤
        ‖((((9 / 16 : ℝ) * (r / s) : ℝ) : ℂ) -
          (((4 + (j.val : ℝ) / 5) / 8 : ℝ) : ℂ))‖ := by
  have he : 0 < r / s := div_pos hr hs
  have he1 : r / s ≤ 1 / 100 := (div_le_iff₀ hs).mpr (by linarith only [hrs])
  have hj0 : 0 ≤ (j.val : ℝ) := Nat.cast_nonneg _
  have hj4 : (j.val : ℝ) ≤ 4 := by exact_mod_cast (show j.val ≤ 4 by omega)
  have hnormu : ‖(((9 / 16 : ℝ) * (r / s) : ℝ) : ℂ)‖ = (9 / 16) * (r / s) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hnormv : ‖(((4 + (j.val : ℝ) / 5) / 8 : ℝ) : ℂ)‖ = (4 + (j.val : ℝ) / 5) / 8 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hgap : ‖((((9 / 16 : ℝ) * (r / s) : ℝ) : ℂ) -
      (((4 + (j.val : ℝ) / 5) / 8 : ℝ) : ℂ))‖ =
      (4 + (j.val : ℝ) / 5) / 8 - (9 / 16) * (r / s) := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_neg (by linarith only [he1, hj0])]
    ring
  rw [hnormu, hnormv, hgap]
  exact ⟨by positivity, by linarith only [he1], by linarith only [he1],
    by linarith only [hj4], by linarith only [he1, hj0, hd]⟩

/-- Undoing the common outer dilation gives the literal selected disks. -/
theorem fusion_normalized_disk_eq (z : ℂ) (r s : ℝ) (hs : 0 < s) (j : Fin 5) :
    Metric.ball (z + (8 * s) • (((9 / 16 : ℝ) * (r / s) : ℝ) : ℂ))
      ((8 * s) * ((r / s) / 800)) =
        Metric.ball (z + (((9 / 2 : ℝ) * r : ℝ) : ℂ)) (r / 100) ∧
    Metric.ball (z + (8 * s) • (((4 + (j.val : ℝ) / 5) / 8 : ℝ) : ℂ))
      ((8 * s) * (1 / 800)) =
        Metric.ball (z + (((4 + (j.val : ℝ) / 5) * s : ℝ) : ℂ)) (s / 100) := by
  have hu : (8 * s) • (((9 / 16 : ℝ) * (r / s) : ℝ) : ℂ) =
      (((9 / 2 : ℝ) * r : ℝ) : ℂ) := by
    rw [Complex.real_smul, ← Complex.ofReal_mul]
    congr 1
    field_simp
    ring
  have hv : (8 * s) • (((4 + (j.val : ℝ) / 5) / 8 : ℝ) : ℂ) =
      (((4 + (j.val : ℝ) / 5) * s : ℝ) : ℂ) := by
    rw [Complex.real_smul, ← Complex.ofReal_mul]
    congr 1
    ring
  rw [hu, hv, show (8 * s) * ((r / s) / 800) = r / 100 by field_simp; ring,
    show (8 * s) * (1 / 800 : ℝ) = s / 100 by ring]
  exact ⟨rfl, rfl⟩

/-- The fixed guard disk is separated from the entire scale cluster. -/
theorem fusion_fixed_disk_gap (z : ℂ) (r₀ d : ℝ) (hr₀ : 0 < r₀)
    (hd : d ≤ r₀) (j : Fin 5) :
    6 * r₀ + r₀ / 100 + d ≤ ‖z - (z + (((12 + (j.val : ℝ) / 5) * r₀ : ℝ) : ℂ))‖ := by
  have hj : 0 ≤ (j.val : ℝ) := Nat.cast_nonneg _
  rw [norm_sub_rev z, real_displacement_norm _ _ (by positivity)]
  nlinarith only [hr₀, hd, hj]

end DOZZ.Proofs

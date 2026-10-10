/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.FusionAllocationAlgebra
public import DOZZ.FourPoint.FusionDiskGeometry

/-! Lower kernel contracts for retained fusion disks, including truncated outer scales. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- The reference kernel on an enclosing triple disk has its literal three-charge power. -/
theorem fusion_triple_reference_product (γ r t : ℝ) (hr : 0 < r)
    (α : Fin 4 → ℝ) :
    (∏ i : Fin 4, (![r, r, r, t] i) ^ (γ * α i)) =
      r ^ (γ * (α 0 + α 1 + α 2)) * t ^ (γ * α 3) := by
  simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]
  rw [← Real.rpow_add hr, ← Real.rpow_add hr]
  congr 2
  ring

/-- A common reference distance gives the total-charge power. -/
theorem fusion_common_reference_product (γ t : ℝ) (ht : 0 < t)
    (α : Fin 4 → ℝ) :
    (∏ i : Fin 4, t ^ (γ * α i)) = t ^ (γ * ∑ i : Fin 4, α i) := by
  rw [Fin.prod_univ_four, Fin.sum_univ_four, ← Real.rpow_add ht,
    ← Real.rpow_add ht, ← Real.rpow_add ht]
  congr 1
  ring

/-- A selected outer disk is a uniformly weighted lower mass, even if the last root lies
at a larger distance than the truncated outer scale. -/
theorem fusion_outer_retained_kernel (γ H R t k m : ℝ)
    (hγ : 0 < γ) (ht : 0 < t) (hm : 1 ≤ m) (hm25 : 25 ≤ m)
    (hmk : 5 + k ≤ m) (htR : 5 * t ≤ R)
    (α : Fin 4 → ℝ) (hα : ∀ i, |α i| ≤ H) (y : Fin 4 → ℂ)
    (hy : ∀ i, ‖y i - y 0‖ ≤ k * t) (j : Fin 5)
    (hj : ∀ i, t / 20 ≤ ‖(y 0 + (((4 + (j.val : ℝ) / 5) * t : ℝ) : ℂ)) - y i‖)
    (M : Measure ℂ) :
    ENNReal.ofReal (((m ^ (γ * H)) ^ 4 * t ^ (γ * ∑ i : Fin 4, α i))⁻¹) *
      M (Metric.ball (y 0 + (((4 + (j.val : ℝ) / 5) * t : ℝ) : ℂ)) (t / 100)) ≤
        fourFusionMass γ M α y R := by
  have hmpos : 0 < m := zero_lt_one.trans_le hm
  apply four_fusion_retained_lower
  · intro x hx
    have hn := (guard_candidate_radial_bounds (y 0) t 4 ht (by norm_num) j x hx).2
    norm_num only [show (4 + 1 : ℝ) = 5 by norm_num, show (12 + 1 : ℝ) = 13 by norm_num] at hn
    simpa only [Metric.mem_ball, dist_eq_norm] using hn.trans_le htR
  · intro x hx
    have hl := guard_disk_root_distance y (y 0) t 4 j hj x hx
    have hu := (guard_candidate_radial_bounds (y 0) t 4 ht (by norm_num) j x hx).2
    have hlow (i : Fin 4) : t / m ≤ ‖x - y i‖ := by
      have hh : t / m ≤ t / 25 := div_le_div_of_nonneg_left ht.le (by norm_num) hm25
      exact hh.trans (hl i).le
    have hup (i : Fin 4) : ‖x - y i‖ ≤ m * t := by
      have hh := norm_sub_le_norm_sub_add_norm_sub x (y 0) (y i)
      rw [norm_sub_rev (y 0)] at hh
      have hk' := mul_le_mul_of_nonneg_right hmk ht.le
      linarith only [hh, hu, hy i, hk']
    have hkernel := four_kernel_lower_comparison γ H m hγ hm α hα y x (fun _ => t)
      (fun _ => ht) hlow hup
    rw [fusion_common_reference_product γ t ht α] at hkernel
    exact hkernel

/-- A selected fixed disk is a uniformly weighted lower mass throughout the compact geometry. -/
theorem fusion_fixed_retained_kernel (γ H R r₀ D m : ℝ)
    (hγ : 0 < γ) (hr₀ : 0 < r₀) (hm : 1 ≤ m) (hml : 25 ≤ m * r₀)
    (hmu : 13 * r₀ + D ≤ m) (hR : 13 * r₀ ≤ R)
    (α : Fin 4 → ℝ) (hα : ∀ i, |α i| ≤ H) (y : Fin 4 → ℂ)
    (hy : ∀ i, ‖y i - y 0‖ ≤ D) (j : Fin 5)
    (hj : ∀ i, r₀ / 20 ≤ ‖(y 0 + (((12 + (j.val : ℝ) / 5) * r₀ : ℝ) : ℂ)) - y i‖)
    (M : Measure ℂ) :
    ENNReal.ofReal (((m ^ (γ * H)) ^ 4)⁻¹) *
      M (Metric.ball (y 0 + (((12 + (j.val : ℝ) / 5) * r₀ : ℝ) : ℂ)) (r₀ / 100)) ≤
        fourFusionMass γ M α y R := by
  have hmpos : 0 < m := zero_lt_one.trans_le hm
  apply four_fusion_retained_lower
  · intro x hx
    have hn := (guard_candidate_radial_bounds (y 0) r₀ 12 hr₀ (by norm_num) j x hx).2
    norm_num only [show (4 + 1 : ℝ) = 5 by norm_num, show (12 + 1 : ℝ) = 13 by norm_num] at hn
    simpa only [Metric.mem_ball, dist_eq_norm] using hn.trans_le hR
  · intro x hx
    have hl := guard_disk_root_distance y (y 0) r₀ 12 j hj x hx
    have hu := (guard_candidate_radial_bounds (y 0) r₀ 12 hr₀ (by norm_num) j x hx).2
    have hlow (i : Fin 4) : (1 : ℝ) / m ≤ ‖x - y i‖ := by
      have hh : (1 : ℝ) / m ≤ r₀ / 25 := (div_le_iff₀ hmpos).mpr (by nlinarith only [hml])
      exact hh.trans (hl i).le
    have hup (i : Fin 4) : ‖x - y i‖ ≤ m * 1 := by
      have hh := norm_sub_le_norm_sub_add_norm_sub x (y 0) (y i)
      rw [norm_sub_rev (y 0)] at hh
      linarith only [hh, hu, hy i, hmu]
    have hkernel := four_kernel_lower_comparison γ H m hγ hm α hα y x (fun _ => 1)
      (fun _ => zero_lt_one) hlow hup
    simpa only [Real.one_rpow, Finset.prod_const_one, mul_one] using hkernel

/-- A small enclosing-triple disk retains the three inner charges and the outer reference scale. -/
theorem fusion_inner_triple_retained_kernel (γ H R r t k m : ℝ)
    (hγ : 0 < γ) (hr : 0 < r) (hrt : 100 * r ≤ t)
    (hm : 6 ≤ m) (hmk : 2 * k ≤ m) (hrR : 5 * r ≤ R)
    (α : Fin 4 → ℝ) (hα : ∀ i, |α i| ≤ H) (y : Fin 4 → ℂ)
    (hy : ∀ i : Fin 3, ‖y i.castSucc - y 0‖ ≤ r)
    (hyt : t ≤ ‖y 3 - y 0‖) (hyt' : ‖y 3 - y 0‖ ≤ k * t) (M : Measure ℂ) :
    ENNReal.ofReal (((m ^ (γ * H)) ^ 4 * r ^ (γ * (α 0 + α 1 + α 2)) *
        t ^ (γ * α 3))⁻¹) *
      M (Metric.ball (y 0 + (((9 / 2 : ℝ) * r : ℝ) : ℂ)) (r / 100)) ≤
        fourFusionMass γ M α y R := by
  have hm1 : 1 ≤ m := (by norm_num : (1 : ℝ) ≤ 6).trans hm
  have hmpos : 0 < m := zero_lt_one.trans_le hm1
  have ht : 0 < t := by linarith only [hr, hrt]
  apply four_fusion_retained_lower
  · intro x hx
    have hn := (retained_disk_radial_bounds (y 0) ((9 / 2 : ℝ) * r) (r / 100)
      (by positivity) x hx).2
    simpa only [Metric.mem_ball, dist_eq_norm] using hn.trans_le (by linarith only [hrR, hr])
  · intro x hx
    have hinner (i : Fin 3) := inner_disk_enclosed_root (y 0) (y i.castSucc) r hr (hy i) x hx
    have houter := inner_disk_external_root (y 0) (y 3) r hr (hrt.trans hyt) x hx
    have hlow (i : Fin 4) : (![r, r, r, t] i) / m ≤ ‖x - y i‖ := by
      fin_cases i
      · exact (div_le_self hr.le hm1).trans (hinner 0).1
      · exact (div_le_self hr.le hm1).trans (hinner 1).1
      · exact (div_le_self hr.le hm1).trans (hinner 2).1
      · exact (div_le_div_of_nonneg_left ht.le (by norm_num) ((by norm_num : (2 : ℝ) ≤ 6).trans hm)).trans
          ((div_le_div_of_nonneg_right hyt (by norm_num)).trans houter.1)
    have hup (i : Fin 4) : ‖x - y i‖ ≤ m * (![r, r, r, t] i) := by
      fin_cases i
      · exact (hinner 0).2.trans (mul_le_mul_of_nonneg_right hm hr.le)
      · exact (hinner 1).2.trans (mul_le_mul_of_nonneg_right hm hr.le)
      · exact (hinner 2).2.trans (mul_le_mul_of_nonneg_right hm hr.le)
      · change ‖x - y 3‖ ≤ m * t
        have hh := mul_le_mul_of_nonneg_left hyt' (by norm_num : (0 : ℝ) ≤ 2)
        have hh' := mul_le_mul_of_nonneg_right hmk ht.le
        exact houter.2.trans (by nlinarith only [hh, hh'])
    have href : ∀ i : Fin 4, 0 < (![r, r, r, t] i) := by intro i; fin_cases i <;> assumption
    have hkernel := four_kernel_lower_comparison γ H m hγ hm1 α hα y x ![r, r, r, t]
      href hlow hup
    rw [fusion_triple_reference_product γ r t hr α] at hkernel
    simpa only [mul_assoc] using hkernel

end DOZZ.Proofs

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.FusionRetainedKernels

/-! The retained pair kernel keeps both outer reference distances. -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Enclosed and distant roots on one retained inner disk admit one reference-vector bound. -/
theorem fusion_inner_cluster_retained_kernel (γ H R r k m : ℝ)
    (hγ : 0 < γ) (hr : 0 < r) (hm : 6 ≤ m) (hmk : 2 * k ≤ m) (hrR : 5 * r ≤ R)
    (α : Fin 4 → ℝ) (hα : ∀ i, |α i| ≤ H) (y : Fin 4 → ℂ)
    (d : Fin 4 → ℝ) (hd : ∀ i, 0 < d i)
    (hparts : ∀ i, (d i = r ∧ ‖y i - y 0‖ ≤ r) ∨
      (100 * r ≤ d i ∧ d i ≤ ‖y i - y 0‖ ∧ ‖y i - y 0‖ ≤ k * d i))
    (M : Measure ℂ) :
    ENNReal.ofReal (((m ^ (γ * H)) ^ 4 * ∏ i : Fin 4, (d i) ^ (γ * α i))⁻¹) *
      M (Metric.ball (y 0 + (((9 / 2 : ℝ) * r : ℝ) : ℂ)) (r / 100)) ≤
        fourFusionMass γ M α y R := by
  have hm1 : 1 ≤ m := (by norm_num : (1 : ℝ) ≤ 6).trans hm
  apply four_fusion_retained_lower
  · intro x hx
    have hn := (retained_disk_radial_bounds (y 0) ((9 / 2 : ℝ) * r) (r / 100)
      (by positivity) x hx).2
    simpa only [Metric.mem_ball, dist_eq_norm] using hn.trans_le (by linarith only [hrR, hr])
  · intro x hx
    have hbounds (i : Fin 4) : d i / m ≤ ‖x - y i‖ ∧ ‖x - y i‖ ≤ m * d i := by
      rcases hparts i with ⟨hdi, hyi⟩ | ⟨hfar, hlow, hup⟩
      · rw [hdi]
        obtain ⟨hl, hu⟩ := inner_disk_enclosed_root (y 0) (y i) r hr hyi x hx
        exact ⟨(div_le_self hr.le hm1).trans hl,
          hu.trans (mul_le_mul_of_nonneg_right hm hr.le)⟩
      · obtain ⟨hl, hu⟩ := inner_disk_external_root (y 0) (y i) r hr (hfar.trans hlow) x hx
        have hlo := (div_le_div_of_nonneg_left (hd i).le (by norm_num : (0 : ℝ) < 2)
          ((by norm_num : (2 : ℝ) ≤ 6).trans hm)).trans
          ((div_le_div_of_nonneg_right hlow (by norm_num)).trans hl)
        have hh := mul_le_mul_of_nonneg_left hup (by norm_num : (0 : ℝ) ≤ 2)
        have hh' := mul_le_mul_of_nonneg_right hmk (hd i).le
        exact ⟨hlo, hu.trans (by nlinarith only [hh, hh'])⟩
    exact four_kernel_lower_comparison γ H m hγ hm1 α hα y x d hd
      (fun i => (hbounds i).1) (fun i => (hbounds i).2)

/-- Reference distances on the retained pair disk give both literal outer-root powers. -/
theorem fusion_pair_reference_product (γ r v t : ℝ) (hr : 0 < r)
    (α : Fin 4 → ℝ) :
    (∏ i : Fin 4, (![r, r, v, t] i) ^ (γ * α i)) =
      r ^ (γ * (α 0 + α 1)) * v ^ (γ * α 2) * t ^ (γ * α 3) := by
  simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, Matrix.head_cons]
  rw [← Real.rpow_add hr]
  congr 3
  ring

end DOZZ.Proofs

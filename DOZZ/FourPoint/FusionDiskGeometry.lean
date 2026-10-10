/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.FusionGuardDisks

/-! Distance comparisons on the retained inner disk and ordered fusion geometry. -/

@[expose] public section

open MeasureTheory Set

namespace DOZZ.Proofs

/-- Ordered four-root geometry puts every insertion within the last radial distance. -/
theorem ordered_fusion_radial_bounds (y : Fin 4 → ℂ) (hy : OrderedFourFusionCenters y) :
    ‖y 0 - y 1‖ ≤ ‖y 0 - y 2‖ ∧ ‖y 0 - y 2‖ ≤ ‖y 0 - y 3‖ ∧
      ∀ i : Fin 4, ‖y i - y 0‖ ≤ ‖y 0 - y 3‖ := by
  have hr34 : ‖y 0 - y 2‖ ≤ ‖y 0 - y 3‖ := by
    have hh := hy.2.2 0
    simp only [Fin.castSucc_zero] at hh
    rw [norm_sub_rev (y 3)] at hh
    exact hy.2.1.trans hh
  refine ⟨hy.1, hr34, ?_⟩
  intro i
  fin_cases i
  · change ‖y 0 - y 0‖ ≤ _
    simpa only [sub_self, norm_zero] using norm_nonneg (y 0 - y 3)
  · change ‖y 1 - y 0‖ ≤ _
    rw [norm_sub_rev (y 1)]; exact hy.1.trans hr34
  · change ‖y 2 - y 0‖ ≤ _
    rw [norm_sub_rev (y 2)]; exact hr34
  · change ‖y 3 - y 0‖ ≤ _
    rw [norm_sub_rev (y 3)]

/-- A root in the inner cluster is at a distance comparable to the inner scale. -/
theorem inner_disk_enclosed_root (z v : ℂ) (r : ℝ) (hr : 0 < r)
    (hv : ‖v - z‖ ≤ r) (x : ℂ)
    (hx : x ∈ Metric.ball (z + (((9 / 2 : ℝ) * r : ℝ) : ℂ)) (r / 100)) :
    r ≤ ‖x - v‖ ∧ ‖x - v‖ ≤ 6 * r := by
  obtain ⟨hl, hu⟩ := retained_disk_radial_bounds z ((9 / 2 : ℝ) * r) (r / 100)
    (by positivity) x hx
  have hup := norm_sub_le_norm_sub_add_norm_sub x z v
  have hdown := norm_sub_le_norm_sub_add_norm_sub x v z
  rw [norm_sub_rev z v] at hup
  constructor <;> linarith only [hl, hu, hup, hdown, hv, hr]

/-- A root at least one hundred inner scales away retains its own radial distance. -/
theorem inner_disk_external_root (z v : ℂ) (r : ℝ) (hr : 0 < r)
    (hv : 100 * r ≤ ‖v - z‖) (x : ℂ)
    (hx : x ∈ Metric.ball (z + (((9 / 2 : ℝ) * r : ℝ) : ℂ)) (r / 100)) :
    ‖v - z‖ / 2 ≤ ‖x - v‖ ∧ ‖x - v‖ ≤ 2 * ‖v - z‖ := by
  obtain ⟨_, hu⟩ := retained_disk_radial_bounds z ((9 / 2 : ℝ) * r) (r / 100)
    (by positivity) x hx
  have hup := norm_sub_le_norm_sub_add_norm_sub x z v
  have hdown := norm_sub_le_norm_sub_add_norm_sub v x z
  rw [norm_sub_rev z v] at hup
  rw [norm_sub_rev v x] at hdown
  constructor <;> linarith only [hu, hup, hdown, hv, hr]

/-- All five outer candidates stay within their prescribed annular coordinate band. -/
theorem guard_candidate_radial_bounds (z : ℂ) (r t : ℝ)
    (hr : 0 < r) (ht : 0 ≤ t) (j : Fin 5) (x : ℂ)
    (hx : x ∈ Metric.ball (z + (((t + (j.val : ℝ) / 5) * r : ℝ) : ℂ)) (r / 100)) :
    (t - 1 / 100) * r < ‖x - z‖ ∧ ‖x - z‖ < (t + 1) * r := by
  have hj : (j.val : ℝ) ≤ 4 := by exact_mod_cast (show j.val ≤ 4 by omega)
  have hj0 : 0 ≤ (j.val : ℝ) := Nat.cast_nonneg _
  obtain ⟨hl, hu⟩ := retained_disk_radial_bounds z ((t + (j.val : ℝ) / 5) * r)
    (r / 100) (by positivity) x hx
  constructor <;> nlinarith only [hl, hu, hj, hj0, hr]

end DOZZ.Proofs

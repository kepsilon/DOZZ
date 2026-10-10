/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.GammaHalfKernel

/-! # Bounds for two colliding rooted singularities -/

@[expose] public section
namespace DOZZ.Proofs

/-- Two rooted singularities with the degenerate numerator are bounded by the two fused
singularities whenever the numerator is controlled by the larger distance. -/
theorem fusion_mixed_power_bound (a b c L k β : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 ≤ c) (hL : 0 < L) (hk : 0 ≤ k) (hβ : k ≤ β)
    (hcb : c ≤ L * max a b) :
    c ^ k / (a ^ β * b ^ (2 * k)) ≤
      L ^ k * (a ^ (-(β + k)) + b ^ (-(β + k))) := by
  have hak : 0 < a ^ k := Real.rpow_pos_of_pos ha _
  have hbk : 0 < b ^ k := Real.rpow_pos_of_pos hb _
  have haβ : 0 < a ^ β := Real.rpow_pos_of_pos ha _
  have hbβ : 0 < b ^ β := Real.rpow_pos_of_pos hb _
  have hLk : 0 ≤ L ^ k := Real.rpow_nonneg hL.le _
  rcases le_total a b with hab | hba
  · have hc' : c ^ k ≤ L ^ k * b ^ k := by
      rw [← Real.mul_rpow hL.le hb.le]
      exact Real.rpow_le_rpow hc (by simpa [max_eq_right hab] using hcb) hk
    have hb2 : b ^ (2 * k) = b ^ k * b ^ k := by
      rw [show 2 * k = k + k by ring, Real.rpow_add hb]
    have hbk' : a ^ k ≤ b ^ k := Real.rpow_le_rpow ha.le hab hk
    have hs : b ^ k / (a ^ β * b ^ (2 * k)) ≤ a ^ (-(β + k)) := by
      rw [hb2, Real.rpow_neg ha.le, Real.rpow_add ha]
      apply (div_le_iff₀ (mul_pos haβ (mul_pos hbk hbk))).mpr
      rw [inv_mul_eq_div]
      apply (le_div_iff₀ (mul_pos haβ hak)).mpr
      simpa only [mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_of_nonneg_left hbk' (mul_nonneg haβ.le hbk.le)
    calc
      _ ≤ (L ^ k * b ^ k) / (a ^ β * b ^ (2 * k)) :=
        div_le_div_of_nonneg_right hc' (by positivity)
      _ = L ^ k * (b ^ k / (a ^ β * b ^ (2 * k))) := by ring
      _ ≤ L ^ k * a ^ (-(β + k)) := mul_le_mul_of_nonneg_left hs hLk
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.rpow_nonneg hb.le _)) hLk
  · have hc' : c ^ k ≤ L ^ k * a ^ k := by
      rw [← Real.mul_rpow hL.le ha.le]
      exact Real.rpow_le_rpow hc (by simpa [max_eq_left hba] using hcb) hk
    have haβ' : a ^ β = a ^ k * a ^ (β - k) := by
      rw [← Real.rpow_add ha]
      congr 1
      ring
    have hbβ' : b ^ (β + k) = b ^ (β - k) * b ^ (2 * k) := by
      rw [← Real.rpow_add hb]
      congr 1
      ring
    have hpow : b ^ (β - k) ≤ a ^ (β - k) :=
      Real.rpow_le_rpow hb.le hba (sub_nonneg.mpr hβ)
    have hs : a ^ k / (a ^ β * b ^ (2 * k)) ≤ b ^ (-(β + k)) := by
      rw [Real.rpow_neg hb.le, hbβ']
      apply (div_le_iff₀ (mul_pos haβ (Real.rpow_pos_of_pos hb _))).mpr
      rw [inv_mul_eq_div]
      apply (le_div_iff₀ (mul_pos (Real.rpow_pos_of_pos hb _) (Real.rpow_pos_of_pos hb _))).mpr
      rw [haβ']
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hb.le _)) hak.le
    calc
      _ ≤ (L ^ k * a ^ k) / (a ^ β * b ^ (2 * k)) :=
        div_le_div_of_nonneg_right hc' (by positivity)
      _ = L ^ k * (a ^ k / (a ^ β * b ^ (2 * k))) := by ring
      _ ≤ L ^ k * b ^ (-(β + k)) := mul_le_mul_of_nonneg_left hs hLk
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Real.rpow_nonneg ha.le _)) hLk

/-- When the root moves as `y*z`, the numerator is bounded by the larger root distance. -/
theorem fusion_movingRoot_distance_bound (y z x : ℂ) (hy : y ≠ 0) :
    ‖x - z‖ ≤ (1 + 2 / ‖y‖) * max ‖x‖ ‖x - y * z‖ := by
  have hypos : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have ha : ‖x‖ ≤ max ‖x‖ ‖x - y * z‖ := le_max_left _ _
  have hb : ‖x - y * z‖ ≤ max ‖x‖ ‖x - y * z‖ := le_max_right _ _
  have hu : ‖y * z‖ ≤ ‖x‖ + ‖x - y * z‖ := by
    have h := norm_sub_le x (x - y * z)
    simpa only [sub_sub_cancel] using h
  rw [norm_mul] at hu
  have hz : ‖z‖ ≤ 2 / ‖y‖ * max ‖x‖ ‖x - y * z‖ := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hypos).mpr
    nlinarith only [hu, ha, hb]
  have h := norm_sub_le x z
  nlinarith only [ha, hz, h]

/-- The colliding singularities have the fused exponent at either root. -/
theorem fusion_movingRoot_power_bound (γ α₁ : ℝ) (hγ : 0 < γ)
    (hα : γ / 2 ≤ α₁) (y z x : ℂ) (hy : y ≠ 0)
    (hx : x ≠ 0) (hxu : x ≠ y * z) :
    ‖x - z‖ ^ (γ ^ 2 / 2) / (‖x‖ ^ (γ * α₁) * ‖x - y * z‖ ^ (γ ^ 2)) ≤
      (1 + 2 / ‖y‖) ^ (γ ^ 2 / 2) *
        (‖x‖ ^ (-γ * (α₁ + γ / 2)) + ‖x - y * z‖ ^ (-γ * (α₁ + γ / 2))) := by
  have hβ : γ ^ 2 / 2 ≤ γ * α₁ := by
    have h := mul_le_mul_of_nonneg_left hα hγ.le
    nlinarith only [h]
  have h := fusion_mixed_power_bound ‖x‖ ‖x - y * z‖ ‖x - z‖
    (1 + 2 / ‖y‖) (γ ^ 2 / 2) (γ * α₁)
    (norm_pos_iff.mpr hx) (norm_pos_iff.mpr (sub_ne_zero.mpr hxu)) (norm_nonneg _)
    (by positivity) (by positivity) hβ (fusion_movingRoot_distance_bound y z x hy)
  have he : 2 * (γ ^ 2 / 2) = γ ^ 2 := by ring
  have he' : -(γ * α₁ + γ ^ 2 / 2) = -γ * (α₁ + γ / 2) := by ring
  simpa only [he, he'] using h

end DOZZ.Proofs

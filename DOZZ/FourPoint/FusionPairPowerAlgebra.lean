/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.FusionPowerAlgebra

/-! Exact three-scale power bookkeeping for the pair-annulus allocation. -/

@[expose] public section

namespace DOZZ.Proofs

/-- Factoring the pair-annulus weights retains both intervening ratios. -/
theorem fusion_pair_weight_power (T r v t U Z V W a b s ξ ξa : ℝ)
    (hT : 0 < T) (hr : 0 < r) (hv : 0 < v) (ht : 0 < t) :
    ((T * r ^ U * v ^ Z * t ^ V)⁻¹) ^ (-a) * ((T * t ^ W)⁻¹) ^ (-b) * (T⁻¹) ^ (-s) *
        t ^ ξ * (r / t) ^ ξa =
      T ^ (a + b + s) * (r / v) ^ (U * a + ξa) * (v / t) ^ (U * a + Z * a + ξa) *
        t ^ (U * a + Z * a + V * a + W * b + ξ) := by
  rw [← Real.rpow_neg_eq_inv_rpow, neg_neg, ← Real.rpow_neg_eq_inv_rpow, neg_neg,
    ← Real.rpow_neg_eq_inv_rpow, neg_neg,
    Real.mul_rpow (mul_pos (mul_pos hT (Real.rpow_pos_of_pos hr _)) (Real.rpow_pos_of_pos hv _)).le
      (Real.rpow_pos_of_pos ht _).le,
    Real.mul_rpow (mul_pos hT (Real.rpow_pos_of_pos hr _)).le (Real.rpow_pos_of_pos hv _).le,
    Real.mul_rpow hT.le (Real.rpow_pos_of_pos hr _).le,
    Real.mul_rpow hT.le (Real.rpow_pos_of_pos ht _).le,
    ← Real.rpow_mul hr.le, ← Real.rpow_mul hv.le, ← Real.rpow_mul ht.le, ← Real.rpow_mul ht.le]
  have hrf : r ^ (U * a) = t ^ (U * a) * (v / t) ^ (U * a) * (r / v) ^ (U * a) := by
    rw [← Real.mul_rpow ht.le (div_pos hv ht).le,
      ← Real.mul_rpow (mul_pos ht (div_pos hv ht)).le (div_pos hr hv).le]
    congr 1
    field_simp
  have hvf : v ^ (Z * a) = t ^ (Z * a) * (v / t) ^ (Z * a) := by
    rw [← Real.mul_rpow ht.le (div_pos hv ht).le, mul_div_cancel₀ _ ht.ne']
  have hrat : (r / t) ^ ξa = (r / v) ^ ξa * (v / t) ^ ξa := by
    rw [← Real.mul_rpow (div_pos hr hv).le (div_pos hv ht).le]
    congr 1
    field_simp
  rw [hrf, hvf, hrat]
  calc
    _ = (T ^ a * T ^ b * T ^ s) * ((r / v) ^ (U * a) * (r / v) ^ ξa) *
        ((v / t) ^ (U * a) * (v / t) ^ (Z * a) * (v / t) ^ ξa) *
        (t ^ (U * a) * t ^ (Z * a) * t ^ (V * a) * t ^ (W * b) * t ^ ξ) := by ring
    _ = _ := by
      rw [← Real.rpow_add hT, ← Real.rpow_add hT,
        ← Real.rpow_add (div_pos hr hv), ← Real.rpow_add (div_pos hv ht),
        ← Real.rpow_add (div_pos hv ht), ← Real.rpow_add ht, ← Real.rpow_add ht,
        ← Real.rpow_add ht, ← Real.rpow_add ht]

/-- The pair allocation gives its drift square. -/
theorem fusion_case_two_inner_exponent (γ : ℝ) (α : Fin 4 → ℝ) (a : ℝ)
    (ha : γ * a = fourFusionNu2 γ α) :
    γ * (α 0 + α 1) * a + (γ * Q γ * (-a) - γ ^ 2 * a ^ 2 / 2) =
      fourFusionNu2 γ α ^ 2 / 2 := by
  calc
    _ = fourFusionNu2 γ α * (γ * a) - (γ * a) ^ 2 / 2 := by unfold fourFusionNu2; ring
    _ = _ := by rw [ha]; ring

/-- The middle ratio keeps the signed exponent specified by the source. -/
theorem fusion_case_two_middle_exponent (γ : ℝ) (α : Fin 4 → ℝ) (a : ℝ)
    (ha : γ * a = fourFusionNu2 γ α) :
    γ * (α 0 + α 1) * a + γ * α 2 * a + (γ * Q γ * (-a) - γ ^ 2 * a ^ 2 / 2) =
      (fourFusionNu3 γ α ^ 2 - (α 2) ^ 2) / 2 := by
  calc
    _ = fourFusionNu2 γ α * fourFusionNu3 γ α - fourFusionNu2 γ α ^ 2 / 2 := by
      rw [← ha]
      unfold fourFusionNu3
      ring
    _ = _ := fusion_middle_exponent γ α

/-- The common scale still sees the entire four-root drift. -/
theorem fusion_case_two_outer_exponent (γ : ℝ) (α : Fin 4 → ℝ) (a b : ℝ)
    (ha : γ * a = fourFusionNu2 γ α) (hb : γ * b = α 2 + α 3) :
    γ * (α 0 + α 1) * a + γ * α 2 * a + γ * α 3 * a + (γ * ∑ i : Fin 4, α i) * b +
      (γ * Q γ * (-(a + b)) - γ ^ 2 * (a + b) ^ 2 / 2) = fourFusionNu4 γ α ^ 2 / 2 := by
  have hab : γ * (a + b) = fourFusionNu4 γ α := by
    rw [mul_add, ha, hb, four_fusion_nu4, four_fusion_nu3]
    ring
  calc
    _ = fourFusionNu4 γ α * (γ * (a + b)) - (γ * (a + b)) ^ 2 / 2 := by
      unfold fourFusionNu4
      rw [Fin.sum_univ_four]
      ring
    _ = _ := by rw [hab]; ring

/-- Deterministic weights and joint GMC scaling give all three literal case-two powers. -/
theorem fusion_case_two_weight_power (γ T r v t a b s : ℝ)
    (hT : 0 < T) (hr : 0 < r) (hv : 0 < v) (ht : 0 < t) (α : Fin 4 → ℝ)
    (ha : γ * a = fourFusionNu2 γ α) (hb : γ * b = α 2 + α 3) :
    ((T * r ^ (γ * (α 0 + α 1)) * v ^ (γ * α 2) * t ^ (γ * α 3))⁻¹) ^ (-a) *
        ((T * t ^ (γ * ∑ i : Fin 4, α i))⁻¹) ^ (-b) * (T⁻¹) ^ (-s) *
        t ^ (γ * Q γ * (-(a + b)) - γ ^ 2 * (a + b) ^ 2 / 2) *
        (r / t) ^ (γ * Q γ * (-a) - γ ^ 2 * a ^ 2 / 2) =
      T ^ (a + b + s) * (r / v) ^ (fourFusionNu2 γ α ^ 2 / 2) *
        (v / t) ^ ((fourFusionNu3 γ α ^ 2 - (α 2) ^ 2) / 2) * t ^ (fourFusionNu4 γ α ^ 2 / 2) := by
  rw [fusion_pair_weight_power T r v t _ _ _ _ a b s _ _ hT hr hv ht,
    fusion_case_two_inner_exponent γ α a ha,
    fusion_case_two_middle_exponent γ α a ha,
    fusion_case_two_outer_exponent γ α a b ha hb]

end DOZZ.Proofs

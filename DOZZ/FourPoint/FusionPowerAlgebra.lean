/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.FusionAllocationAlgebra

/-! Exact powers from deterministic weights and the shared Gaussian scale. -/

@[expose] public section

namespace DOZZ.Proofs

/-- Factoring the deterministic weights into the common and relative spatial scales. -/
theorem fusion_nested_weight_power (T r t U V W a b s ξ ξa : ℝ)
    (hT : 0 < T) (hr : 0 < r) (ht : 0 < t) :
    ((T * r ^ U * t ^ V)⁻¹) ^ (-a) * ((T * t ^ W)⁻¹) ^ (-b) * (T⁻¹) ^ (-s) *
        t ^ ξ * (r / t) ^ ξa =
      T ^ (a + b + s) * (r / t) ^ (U * a + ξa) * t ^ (U * a + V * a + W * b + ξ) := by
  rw [← Real.rpow_neg_eq_inv_rpow, neg_neg, ← Real.rpow_neg_eq_inv_rpow, neg_neg,
    ← Real.rpow_neg_eq_inv_rpow, neg_neg,
    Real.mul_rpow (mul_pos hT (Real.rpow_pos_of_pos hr _)).le (Real.rpow_pos_of_pos ht _).le,
    Real.mul_rpow hT.le (Real.rpow_pos_of_pos hr _).le,
    Real.mul_rpow hT.le (Real.rpow_pos_of_pos ht _).le,
    ← Real.rpow_mul hr.le, ← Real.rpow_mul ht.le, ← Real.rpow_mul ht.le]
  have hrf : r ^ (U * a) = t ^ (U * a) * (r / t) ^ (U * a) := by
    rw [← Real.mul_rpow ht.le (div_pos hr ht).le, mul_div_cancel₀ _ ht.ne']
  rw [hrf]
  calc
    _ = (T ^ a * T ^ b * T ^ s) * ((r / t) ^ (U * a) * (r / t) ^ ξa) *
        (t ^ (U * a) * t ^ (V * a) * t ^ (W * b) * t ^ ξ) := by ring
    _ = _ := by
      rw [← Real.rpow_add hT, ← Real.rpow_add hT, ← Real.rpow_add (div_pos hr ht),
        ← Real.rpow_add ht, ← Real.rpow_add ht, ← Real.rpow_add ht]

/-- The inner allocated Gaussian square yields the triple drift exponent. -/
theorem fusion_case_one_inner_exponent (γ : ℝ) (α : Fin 4 → ℝ) (a : ℝ)
    (ha : γ * a = fourFusionNu3 γ α) :
    γ * (α 0 + α 1 + α 2) * a +
      (γ * Q γ * (-a) - γ ^ 2 * a ^ 2 / 2) = fourFusionNu3 γ α ^ 2 / 2 := by
  calc
    _ = fourFusionNu3 γ α * (γ * a) - (γ * a) ^ 2 / 2 := by unfold fourFusionNu3; ring
    _ = _ := by rw [ha]; ring

/-- The common outer Gaussian square sees the sum of the allocated cluster orders. -/
theorem fusion_case_one_outer_exponent (γ : ℝ) (α : Fin 4 → ℝ) (a b : ℝ)
    (ha : γ * a = fourFusionNu3 γ α) (hb : γ * b = α 3) :
    γ * (α 0 + α 1 + α 2) * a + γ * α 3 * a + (γ * ∑ i : Fin 4, α i) * b +
      (γ * Q γ * (-(a + b)) - γ ^ 2 * (a + b) ^ 2 / 2) = fourFusionNu4 γ α ^ 2 / 2 := by
  have hab : γ * (a + b) = fourFusionNu4 γ α := by
    rw [mul_add, ha, hb, four_fusion_nu4]
  calc
    _ = fourFusionNu4 γ α * (γ * (a + b)) - (γ * (a + b)) ^ 2 / 2 := by
      unfold fourFusionNu4
      rw [Fin.sum_univ_four]
      ring
    _ = _ := by rw [hab]; ring

/-- The two-scale deterministic and Gaussian factors yield the exact first fusion bound. -/
theorem fusion_case_one_weight_power (γ T r t a b s : ℝ)
    (hT : 0 < T) (hr : 0 < r) (ht : 0 < t) (α : Fin 4 → ℝ)
    (ha : γ * a = fourFusionNu3 γ α) (hb : γ * b = α 3) :
    ((T * r ^ (γ * (α 0 + α 1 + α 2)) * t ^ (γ * α 3))⁻¹) ^ (-a) *
        ((T * t ^ (γ * ∑ i : Fin 4, α i))⁻¹) ^ (-b) * (T⁻¹) ^ (-s) *
        t ^ (γ * Q γ * (-(a + b)) - γ ^ 2 * (a + b) ^ 2 / 2) *
        (r / t) ^ (γ * Q γ * (-a) - γ ^ 2 * a ^ 2 / 2) =
      T ^ (a + b + s) * (r / t) ^ (fourFusionNu3 γ α ^ 2 / 2) *
        t ^ (fourFusionNu4 γ α ^ 2 / 2) := by
  rw [fusion_nested_weight_power T r t _ _ _ a b s _ _ hT hr ht,
    fusion_case_one_inner_exponent γ α a ha,
    fusion_case_one_outer_exponent γ α a b ha hb]

/-- A single allocated outer scale yields the full fused drift square. -/
theorem fusion_single_weight_power (γ T t a s : ℝ) (hT : 0 < T) (ht : 0 < t)
    (α : Fin 4 → ℝ) (ha : γ * a = fourFusionNu4 γ α) :
    ((T * t ^ (γ * ∑ i : Fin 4, α i))⁻¹) ^ (-a) * (T⁻¹) ^ (-s) *
        t ^ (γ * Q γ * (-a) - γ ^ 2 * a ^ 2 / 2) =
      T ^ (a + s) * t ^ (fourFusionNu4 γ α ^ 2 / 2) := by
  rw [← Real.rpow_neg_eq_inv_rpow, neg_neg, ← Real.rpow_neg_eq_inv_rpow, neg_neg,
    Real.mul_rpow hT.le (Real.rpow_pos_of_pos ht _).le, ← Real.rpow_mul ht.le]
  have he : (γ * ∑ i : Fin 4, α i) * a + (γ * Q γ * (-a) - γ ^ 2 * a ^ 2 / 2) =
      fourFusionNu4 γ α ^ 2 / 2 := by
    calc
      _ = fourFusionNu4 γ α * (γ * a) - (γ * a) ^ 2 / 2 := by unfold fourFusionNu4; ring
      _ = _ := by rw [ha]; ring
  calc
    _ = (T ^ a * T ^ s) * (t ^ ((γ * ∑ i : Fin 4, α i) * a) *
        t ^ (γ * Q γ * (-a) - γ ^ 2 * a ^ 2 / 2)) := by ring
    _ = _ := by rw [← Real.rpow_add hT, ← Real.rpow_add ht, he]

end DOZZ.Proofs

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.FusionAllocationAlgebra

/-! Strict exponent margins for the corrected two-rooted Taylor domain. -/

@[expose] public section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The time exponent retains alpha_1; it lies strictly between -1 and 0 (erratum K20, see
docs/ERRATA-AND-DEVIATIONS.md). -/
theorem twoRooted_time_exponent (γ α : ℝ) (hγ : 0 < γ) (hγsq : 2 < γ ^ 2)
    (hα : γ / 2 < α) (hα2 : α < 2 / γ) :
    γ * (Q γ - α) - 2 = γ ^ 2 / 2 - γ * α ∧
      1 < γ * (Q γ - α) ∧ γ * (Q γ - α) < 2 := by
  have he : γ * (Q γ - α) = 2 + γ ^ 2 / 2 - γ * α := by
    unfold Q
    field_simp
  have hm1 : γ * α < 2 := by simpa only [mul_comm] using (lt_div_iff₀ hγ).mp hα2
  have hm2 := mul_lt_mul_of_pos_left hα hγ
  rw [he]
  constructor
  · ring
  · constructor <;> nlinarith only [hγsq, hm1, hm2]

/-- The near-cluster exponent has a strictly positive extra power. -/
theorem twoRooted_near_gain (γ α : ℝ) (hγ : 0 < γ) (hα2 : α < 2 / γ) :
    2 - 2 * γ * α + (3 * γ / 2 + α - Q γ) ^ 2 / 2 =
      γ * (Q γ - α) - 2 + (α - 2 / γ) ^ 2 / 2 ∧
      0 < (α - 2 / γ) ^ 2 / 2 := by
  constructor
  · unfold Q
    field_simp
    ring
  · exact div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hα2.ne)) (by norm_num)

/-- The middle-region optimized moment leaves the exact positive square margin. -/
theorem twoRooted_intermediate_gain (γ α : ℝ) (_hγ : 0 < γ) (hα2 : α < 2 / γ) :
    (γ / 2 + Q γ - α) ^ 2 / 2 - γ * (Q γ - α) =
      (Q γ - α - γ / 2) ^ 2 / 2 ∧ 0 < (Q γ - α - γ / 2) ^ 2 / 2 := by
  have hdiff : 0 < Q γ - α - γ / 2 := by unfold Q; linarith only [hα2]
  exact ⟨by ring, div_pos (sq_pos_of_pos hdiff) (by norm_num)⟩

/-- Strictly integrable powers in the two-root near-diagonal sectors. -/
theorem twoRooted_diagonal_exponents (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hγsq : 2 < γ ^ 2) :
    0 < 3 * γ / 2 - Q γ ∧ 0 < 2 * γ - Q γ ∧
      γ ^ 2 / 4 < 2 ∧ γ ^ 2 - (2 * γ - Q γ) ^ 2 / 2 < 2 := by
  have hmult : γ * Q γ = 2 + γ ^ 2 / 2 := by unfold Q; field_simp
  have hQ : 2 < Q γ := by
    have he : γ * (Q γ - 2) = (γ - 2) ^ 2 / 2 := by rw [mul_sub, hmult]; ring
    have hs : 0 < (γ - 2) ^ 2 / 2 := div_pos
      (sq_pos_of_ne_zero (sub_ne_zero.mpr hγ2.ne)) (by norm_num)
    have hh : 0 < γ * (Q γ - 2) := by rwa [he]
    exact lt_of_sub_pos ((mul_pos_iff_of_pos_left hγ).mp hh)
  have he : γ ^ 2 - (2 * γ - Q γ) ^ 2 / 2 = 4 - Q γ ^ 2 / 2 := by
    nlinarith only [hmult]
  have hν3 : 0 < 3 * γ / 2 - Q γ := by
    apply (mul_pos_iff_of_pos_left hγ).mp
    nlinarith only [hmult, hγsq]
  have hν2 : 0 < 2 * γ - Q γ := by linarith only [hν3, hγ]
  refine ⟨hν3, hν2, ?_, ?_⟩
  · nlinarith only [hγ2, hγ]
  · rw [he]
    nlinarith only [hQ]

/-- The actual global inverse order exceeds the four-root allocation budget (erratum K25, see
docs/ERRATA-AND-DEVIATIONS.md). -/
theorem twoRooted_global_inverse_budget (γ α₁ α₂ α₃ : ℝ) (hγ : 0 < γ)
    (hα₁ : α₁ < Q γ) (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃) :
    0 < (α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ + 2 ∧
      (3 * γ / 2 + α₁ - Q γ) / γ <
        (α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ + 2 := by
  have hp : 0 < (α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ :=
    div_pos (by linarith only [hs]) hγ
  refine ⟨by linarith only [hp], ?_⟩
  have he : ((α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ + 2) -
      (3 * γ / 2 + α₁ - Q γ) / γ = (α₂ + α₃ - Q γ) / γ := by field_simp; ring
  apply lt_of_sub_pos
  rw [he]
  exact div_pos (by linarith only [hα₁, hs, hγ]) hγ

end DOZZ.Proofs

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.ExtendedSeiberg3

/-! # Parameter windows for the two fusion limits -/

@[expose] public section
namespace DOZZ.Proofs

/-- The fusion exponent is the scaling degree of the planar integral. -/
theorem fusion_exponent_eq (γ α₁ : ℝ) (hγ : γ ≠ 0) :
    γ * (Q γ - α₁) = 2 + γ ^ 2 / 2 - γ * α₁ := by
  unfold Q
  field_simp

/-- The Taylor domain supplies the subtracted planar-integral window and `κ < 2`. -/
theorem fusion_taylor_parameters (γ α₁ : ℝ) (hγ : 0 < γ)
    (hlo : γ / 2 < α₁) (hsq : 2 < γ ^ 2) (hhi : α₁ < 2 / γ) :
    0 < γ ^ 2 / 2 ∧ γ ^ 2 / 2 < γ * α₁ ∧ γ * α₁ < 2 ∧
      γ * α₁ < γ ^ 2 / 2 + 1 ∧ 0 < γ * (Q γ - α₁) ∧
      γ * (Q γ - α₁) < 2 := by
  have hβ : γ * α₁ < 2 := by
    have := (lt_div_iff₀ hγ).mp hhi
    nlinarith
  have hlo' := mul_lt_mul_of_pos_left hlo hγ
  rw [fusion_exponent_eq γ α₁ hγ.ne']
  refine ⟨by positivity, by nlinarith, hβ, by linarith, by nlinarith, by nlinarith⟩

/-- The restricted KRV domain supplies the unsubtracted difference window and `κ < 1`. -/
theorem fusion_difference_parameters (γ α₁ : ℝ) (hγ : 0 < γ)
    (hlo : γ / 2 + 1 / γ < α₁) (hhi : α₁ < 2 / γ) :
    0 < γ ^ 2 / 2 ∧ γ ^ 2 / 2 + 1 < γ * α₁ ∧ γ * α₁ < 2 ∧
      0 < γ * (Q γ - α₁) ∧ γ * (Q γ - α₁) < 1 := by
  have hβ : γ * α₁ < 2 := by
    have := (lt_div_iff₀ hγ).mp hhi
    nlinarith
  have hlo' := mul_lt_mul_of_pos_left hlo hγ
  have he : γ * (γ / 2 + 1 / γ) = γ ^ 2 / 2 + 1 := by
    field_simp
  rw [he] at hlo'
  rw [fusion_exponent_eq γ α₁ hγ.ne']
  exact ⟨by positivity, hlo', hβ, by nlinarith, by linarith⟩

/-- The shifted three charges lie in the ordinary, hence extended, Seiberg range. -/
theorem fusion_shifted_domain (γ α₁ α₂ α₃ : ℝ) (hγ : 0 < γ)
    (hhi : α₁ < 2 / γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃) :
    ExtendedSeiberg3 γ (α₁ + γ / 2) α₂ α₃ := by
  have hα₁ : α₁ + γ / 2 < Q γ := by unfold Q; linarith
  have hp : 0 < sExp γ (α₁ + γ / 2) α₂ α₃ := by
    unfold sExp
    exact div_pos (by linarith) hγ
  refine ⟨hα₁, hα₂, hα₃, lt_min ?_ (lt_min ?_ (lt_min ?_ ?_))⟩
  · exact lt_of_lt_of_le (neg_neg_of_pos hp) (by positivity)
  · exact lt_of_lt_of_le (neg_neg_of_pos hp)
      (mul_nonneg (by positivity) (sub_nonneg.mpr hα₁.le))
  · exact lt_of_lt_of_le (neg_neg_of_pos hp)
      (mul_nonneg (by positivity) (sub_nonneg.mpr hα₂.le))
  · exact lt_of_lt_of_le (neg_neg_of_pos hp)
      (mul_nonneg (by positivity) (sub_nonneg.mpr hα₃.le))

end DOZZ.Proofs

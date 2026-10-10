/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Defs

/-! Exact zero strata of the undivided real Gamma coefficients. -/

@[expose] public section

namespace DOZZ.Proofs

/-- The reciprocal-Gamma factors give the exact coefficient zero strata away from integer `c`.
-/
theorem gauss_coefficients_zero_iff (a b c : ℝ) (hc : ∀ n : ℤ, c ≠ (n : ℝ)) :
    (gaussK₁ a b c = 0 ↔ ∃ n : ℕ,
      a = -(n : ℝ) ∨ b = -(n : ℝ) ∨ c - a = -(n : ℝ) ∨ c - b = -(n : ℝ)) ∧
    (gaussK₂ a b c = 0 ↔ ∃ n : ℕ,
      a = (n : ℝ) + 1 ∨ b = (n : ℝ) + 1 ∨
        c - a = (n : ℝ) + 1 ∨ c - b = (n : ℝ) + 1) := by
  have hΓc : Real.Gamma c ≠ 0 := by
    intro hzero
    obtain ⟨n, hn⟩ := (Real.Gamma_eq_zero_iff c).mp hzero
    apply hc (-(n : ℤ))
    norm_num [hn]
  have hΓ2c : Real.Gamma (2 - c) ≠ 0 := by
    intro hzero
    obtain ⟨n, hn⟩ := (Real.Gamma_eq_zero_iff (2 - c)).mp hzero
    apply hc (n + 2)
    have hcast : c = (n : ℝ) + 2 := by
      calc
        c = 2 - (2 - c) := by ring
        _ = 2 - (-(n : ℝ)) := by rw [hn]
        _ = (n : ℝ) + 2 := by ring
    exact_mod_cast hcast
  have hK₁ : gaussK₁ a b c = 0 ↔ ∃ n : ℕ,
      a = -(n : ℝ) ∨ b = -(n : ℝ) ∨ c - a = -(n : ℝ) ∨ c - b = -(n : ℝ) := by
    constructor
    · intro hzero
      have hproduct :
          Real.Gamma c ^ 2 * (Real.Gamma (c - a))⁻¹ * (Real.Gamma (c - b))⁻¹ *
            (Real.Gamma a)⁻¹ * (Real.Gamma b)⁻¹ = 0 := by
        simpa only [gaussK₁] using hzero
      simp only [mul_eq_zero, sq_eq_zero_iff, inv_eq_zero, or_assoc] at hproduct
      rcases hproduct with hΓcZero | hca | hcb | ha | hb
      · exact False.elim (hΓc hΓcZero)
      · obtain ⟨n, hn⟩ := (Real.Gamma_eq_zero_iff (c - a)).mp hca
        exact ⟨n, Or.inr (Or.inr (Or.inl hn))⟩
      · obtain ⟨n, hn⟩ := (Real.Gamma_eq_zero_iff (c - b)).mp hcb
        exact ⟨n, Or.inr (Or.inr (Or.inr hn))⟩
      · obtain ⟨n, hn⟩ := (Real.Gamma_eq_zero_iff a).mp ha
        exact ⟨n, Or.inl hn⟩
      · obtain ⟨n, hn⟩ := (Real.Gamma_eq_zero_iff b).mp hb
        exact ⟨n, Or.inr (Or.inl hn)⟩
    · rintro ⟨n, hn | hn | hn | hn⟩
      · have hzero : Real.Gamma a = 0 := (Real.Gamma_eq_zero_iff a).mpr ⟨n, hn⟩
        simp [gaussK₁, hzero]
      · have hzero : Real.Gamma b = 0 := (Real.Gamma_eq_zero_iff b).mpr ⟨n, hn⟩
        simp [gaussK₁, hzero]
      · have hzero : Real.Gamma (c - a) = 0 := (Real.Gamma_eq_zero_iff (c - a)).mpr ⟨n, hn⟩
        simp [gaussK₁, hzero]
      · have hzero : Real.Gamma (c - b) = 0 := (Real.Gamma_eq_zero_iff (c - b)).mpr ⟨n, hn⟩
        simp [gaussK₁, hzero]
  have hK₂ : gaussK₂ a b c = 0 ↔ ∃ n : ℕ,
      a = (n : ℝ) + 1 ∨ b = (n : ℝ) + 1 ∨
        c - a = (n : ℝ) + 1 ∨ c - b = (n : ℝ) + 1 := by
    constructor
    · intro hzero
      have hproduct :
          Real.Gamma (2 - c) ^ 2 * (Real.Gamma (1 - a))⁻¹ *
            (Real.Gamma (1 - b))⁻¹ * (Real.Gamma (a - c + 1))⁻¹ *
            (Real.Gamma (b - c + 1))⁻¹ = 0 := by
        simpa only [gaussK₂] using hzero
      simp only [mul_eq_zero, sq_eq_zero_iff, inv_eq_zero, or_assoc] at hproduct
      rcases hproduct with hΓ2cZero | ha | hb | hac | hbc
      · exact False.elim (hΓ2c hΓ2cZero)
      · obtain ⟨n, hn⟩ := (Real.Gamma_eq_zero_iff (1 - a)).mp ha
        refine ⟨n, Or.inl ?_⟩
        linarith
      · obtain ⟨n, hn⟩ := (Real.Gamma_eq_zero_iff (1 - b)).mp hb
        refine ⟨n, Or.inr (Or.inl ?_)⟩
        linarith
      · obtain ⟨n, hn⟩ := (Real.Gamma_eq_zero_iff (a - c + 1)).mp hac
        refine ⟨n, Or.inr (Or.inr (Or.inl ?_))⟩
        linarith
      · obtain ⟨n, hn⟩ := (Real.Gamma_eq_zero_iff (b - c + 1)).mp hbc
        refine ⟨n, Or.inr (Or.inr (Or.inr ?_))⟩
        linarith
    · rintro ⟨n, hn | hn | hn | hn⟩
      · have hzero : Real.Gamma (1 - a) = 0 := by
          apply (Real.Gamma_eq_zero_iff (1 - a)).mpr
          refine ⟨n, ?_⟩
          linarith
        simp [gaussK₂, hzero]
      · have hzero : Real.Gamma (1 - b) = 0 := by
          apply (Real.Gamma_eq_zero_iff (1 - b)).mpr
          refine ⟨n, ?_⟩
          linarith
        simp [gaussK₂, hzero]
      · have hzero : Real.Gamma (a - c + 1) = 0 := by
          apply (Real.Gamma_eq_zero_iff (a - c + 1)).mpr
          refine ⟨n, ?_⟩
          linarith
        simp [gaussK₂, hzero]
      · have hzero : Real.Gamma (b - c + 1) = 0 := by
          apply (Real.Gamma_eq_zero_iff (b - c + 1)).mpr
          refine ⟨n, ?_⟩
          linarith
        simp [gaussK₂, hzero]
  exact ⟨hK₁, hK₂⟩

end DOZZ.Proofs

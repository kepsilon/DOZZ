/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! A nonzero Wronskian makes a Hermitian tensor unique from its mixed Wirtinger jet. -/

@[expose] public section

namespace DOZZ.Proofs

/-- The four entries of a Hermitian tensor are determined by the value, the two first Wirtinger
derivatives, and the mixed derivative at any point where the basis Wronskian is nonzero. -/
theorem hermitianTensor_coefficients_eq_of_wirtinger_jet
    (f g df dg A B C D : ℂ) (hW : f * dg - df * g ≠ 0)
    (h₀₀ : A * f * star f + B * f * star g +
      C * g * star f + D * g * star g = 0)
    (h₁₀ : A * df * star f + B * df * star g +
      C * dg * star f + D * dg * star g = 0)
    (h₀₁ : A * f * star df + B * f * star dg +
      C * g * star df + D * g * star dg = 0)
    (h₁₁ : A * df * star df + B * df * star dg +
      C * dg * star df + D * dg * star dg = 0) :
    A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0 := by
  have hR₁prod : (f * dg - df * g) * (A * star f + B * star g) = 0 := by
    linear_combination dg * h₀₀ - g * h₁₀
  have hR₂prod : (f * dg - df * g) * (C * star f + D * star g) = 0 := by
    linear_combination f * h₁₀ - df * h₀₀
  have hR₁ : A * star f + B * star g = 0 :=
    (mul_eq_zero.mp hR₁prod).resolve_left hW
  have hR₂ : C * star f + D * star g = 0 :=
    (mul_eq_zero.mp hR₂prod).resolve_left hW
  have hS₁prod : (f * dg - df * g) * (A * star df + B * star dg) = 0 := by
    linear_combination dg * h₀₁ - g * h₁₁
  have hS₂prod : (f * dg - df * g) * (C * star df + D * star dg) = 0 := by
    linear_combination f * h₁₁ - df * h₀₁
  have hS₁ : A * star df + B * star dg = 0 :=
    (mul_eq_zero.mp hS₁prod).resolve_left hW
  have hS₂ : C * star df + D * star dg = 0 :=
    (mul_eq_zero.mp hS₂prod).resolve_left hW
  have hWstar : star (f * dg - df * g) ≠ 0 := star_ne_zero.mpr hW
  have hAprod : star (f * dg - df * g) * A = 0 := by
    rw [star_sub, star_mul, star_mul]
    linear_combination star dg * hR₁ - star g * hS₁
  have hBprod : star (f * dg - df * g) * B = 0 := by
    rw [star_sub, star_mul, star_mul]
    linear_combination star f * hS₁ - star df * hR₁
  have hCprod : star (f * dg - df * g) * C = 0 := by
    rw [star_sub, star_mul, star_mul]
    linear_combination star dg * hR₂ - star g * hS₂
  have hDprod : star (f * dg - df * g) * D = 0 := by
    rw [star_sub, star_mul, star_mul]
    linear_combination star f * hS₂ - star df * hR₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (mul_eq_zero.mp hAprod).resolve_left hWstar
  · exact (mul_eq_zero.mp hBprod).resolve_left hWstar
  · exact (mul_eq_zero.mp hCprod).resolve_left hWstar
  · exact (mul_eq_zero.mp hDprod).resolve_left hWstar

/-- For a Hermitian off-diagonal tensor, its value and first holomorphic Wirtinger derivative
already determine the two off-diagonal entries when the basis Wronskian is nonzero. -/
theorem hermitianOffDiagonal_eq_zero_of_value_and_z_derivative
    (f g df dg B C : ℂ) (hW : f * dg - df * g ≠ 0)
    (hHerm : C = star B)
    (h₀ : B * f * star g + C * g * star f = 0)
    (h₁ : B * df * star g + C * dg * star f = 0) :
    B = 0 ∧ C = 0 := by
  have hBgProd : (f * dg - df * g) * (B * star g) = 0 := by
    linear_combination dg * h₀ - g * h₁
  have hCfProd : (f * dg - df * g) * (C * star f) = 0 := by
    linear_combination f * h₁ - df * h₀
  have hBg : B * star g = 0 :=
    (mul_eq_zero.mp hBgProd).resolve_left hW
  have hCf : C * star f = 0 :=
    (mul_eq_zero.mp hCfProd).resolve_left hW
  by_cases hg : g = 0
  · have hf : f ≠ 0 := by
      intro hf
      apply hW
      rw [hf, hg]
      ring
    have hC : C = 0 := (mul_eq_zero.mp hCf).resolve_right (star_ne_zero.mpr hf)
    have hB : B = 0 := by
      calc
        B = star C := by simpa using (congrArg star hHerm).symm
        _ = 0 := by rw [hC]; simp
    exact ⟨hB, hC⟩
  · have hB : B = 0 := (mul_eq_zero.mp hBg).resolve_right (star_ne_zero.mpr hg)
    exact ⟨hB, by rw [hHerm, hB]; simp⟩

end DOZZ.Proofs

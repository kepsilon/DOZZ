/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.VertexVarianceBound

/-! The imaginary equator pin is a bounded quadratic form. -/

@[expose] public section
namespace DOZZ.Proofs

/-- The imaginary zero-mode power has the exact total-charge scaling. -/
theorem complexMomentPower_im_scaled {N : ℕ} (γ : ℝ) (hγ : γ ≠ 0)
    (β : Fin N → ℂ) :
    γ * (complexMomentPower γ β).im = -∑ i, (β i).im := by
  unfold complexMomentPower
  rw [← Complex.ofReal_inv]
  simp only [Complex.neg_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.im_sum, zero_mul, add_zero, zero_add]
  field_simp

/-- A bounded pin vector gives a quadratic bound in all imaginary charges, including the
outward vertex. -/
theorem imaginary_pin_le {N : ℕ} (b : Fin (N + 1) → ℝ) (A : Fin N → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hA : ∀ i, |A i| ≤ B) :
    -(∑ i, b i) * (∑ i, b i.castSucc * A i) ≤
      B * (N + 1 : ℕ) * ∑ i, b i ^ 2 := by
  classical
  let S := ∑ i, |b i|
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hsum : |∑ i, b i| ≤ S := Finset.abs_sum_le_sum_abs _ _
  have hsub : ∑ i : Fin N, |b i.castSucc| ≤ S := by
    dsimp only [S]
    rw [Fin.sum_univ_castSucc]
    exact le_add_of_nonneg_right (abs_nonneg _)
  have hpin : |∑ i, b i.castSucc * A i| ≤ S * B := by
    calc
      _ ≤ ∑ i, |b i.castSucc * A i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |b i.castSucc| * B := Finset.sum_le_sum (fun i _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hA i) (abs_nonneg _))
      _ = (∑ i : Fin N, |b i.castSucc|) * B := (Finset.sum_mul ..).symm
      _ ≤ S * B := mul_le_mul_of_nonneg_right hsub hB
  have hsq : S ^ 2 ≤ (N + 1 : ℕ) * ∑ i, b i ^ 2 := by
    simpa only [S, Finset.card_univ, Fintype.card_fin, sq_abs] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |b i|))
  calc
    _ ≤ |-(∑ i, b i) * (∑ i, b i.castSucc * A i)| := le_abs_self _
    _ = |∑ i, b i| * |∑ i, b i.castSucc * A i| := by rw [abs_mul, abs_neg]
    _ ≤ S * (S * B) := mul_le_mul hsum hpin (abs_nonneg _) hS
    _ = B * S ^ 2 := by ring
    _ ≤ B * ((N + 1 : ℕ) * ∑ i, b i ^ 2) := mul_le_mul_of_nonneg_left hsq hB
    _ = _ := by ring

end DOZZ.Proofs

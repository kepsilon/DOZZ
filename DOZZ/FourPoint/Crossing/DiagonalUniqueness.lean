/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ClassificationHermitianMixedJet
public import DOZZ.Hypergeom.ClassificationDiagonalConstraint
public import DOZZ.Hypergeom.BasisSpanning
import Mathlib.Tactic

/-! # Uniqueness of the real one-channel diagonal coefficients -/

public section
open Set
namespace DOZZ.Proofs

/-- A diagonal norm-square form has unique coefficients on an open set where
the two holomorphic functions have a nonzero Wronskian. -/
theorem crossing_diagonal_norm_coefficients_unique
    {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (A D A' D' : ℝ) {z : ℂ} (hz : z ∈ U)
    (hW : f z * deriv g z - deriv f z * g z ≠ 0)
    (hEq : ∀ w ∈ U, A * ‖f w‖ ^ 2 + D * ‖g w‖ ^ 2 =
      A' * ‖f w‖ ^ 2 + D' * ‖g w‖ ^ 2) : A = A' ∧ D = D' := by
  have hd (a d : ℝ) (w : ℂ) :
      hermitianQuadraticTensor f g (a : ℂ) 0 0 (d : ℂ) w =
        ((a * ‖f w‖ ^ 2 + d * ‖g w‖ ^ 2 : ℝ) : ℂ) := by
    simp only [hermitianQuadraticTensor, zero_mul, add_zero]
    calc
      _ = (a : ℂ) * (f w * star (f w)) + (d : ℂ) * (g w * star (g w)) := by ring
      _ = _ := by
        rw [complex_mul_star_eq_normSq, complex_mul_star_eq_normSq,
          Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
        push_cast
        ring
  have he : ∀ w ∈ U,
      hermitianQuadraticTensor f g (A : ℂ) 0 0 (D : ℂ) w =
        hermitianQuadraticTensor f g (A' : ℂ) 0 0 (D' : ℂ) w := by
    intro w hw
    rw [hd, hd, hEq w hw]
  have hcoeff := hermitianTensor_coefficients_eq_of_eqOn hU hf hg A 0 0 D A' 0 0 D'
    hz hW he
  exact ⟨Complex.ofReal_injective hcoeff.1, Complex.ofReal_injective hcoeff.2.2.2⟩

/-- In particular, the two real one-channel coefficients in a physical crossing
comparison can be identified without taking a subleading endpoint limit. -/
theorem crossing_one_channel_coefficients_unique
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (a b c A D A' D' : ℝ) (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℝ))
    (he : ∀ z ∈ gaussCutPlane,
      A * ‖gaussGMinus H a b c z‖ ^ 2 + D * ‖gaussGPlus H a b c z‖ ^ 2 =
        A' * ‖gaussGMinus H a b c z‖ ^ 2 + D' * ‖gaussGPlus H a b c z‖ ^ 2) :
    A = A' ∧ D = D' := by
  have hδC : ∀ n : ℤ, (c : ℂ) - (a : ℂ) - (b : ℂ) ≠ (n : ℂ) := by
    intro n hn
    apply hδ n
    exact_mod_cast hn
  have hbases := gauss_local_basis_one hH (a : ℂ) (b : ℂ) (c : ℂ) hδC
  have hmid : (1 / 2 : ℂ) ∈ gaussCutPlane := by norm_num [gaussCutPlane]
  have hδ0 : (c : ℂ) - (a : ℂ) - (b : ℂ) ≠ 0 := by simpa using hδC 0
  have hW : gaussGMinus H a b c (1 / 2 : ℂ) * deriv (gaussGPlus H a b c) (1 / 2 : ℂ) -
      deriv (gaussGMinus H a b c) (1 / 2 : ℂ) * gaussGPlus H a b c (1 / 2 : ℂ) ≠ 0 := by
    rw [(hbases.2.2.1 (1 / 2 : ℂ) hmid).2.2]
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hδ0)
      (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num))))
      (Complex.cpow_ne_zero_iff.mpr (Or.inl (by norm_num)))
  exact crossing_diagonal_norm_coefficients_unique gaussCutPlane_isOpen
    (hbases.1.analyticOnNhd gaussCutPlane_isOpen)
    (hbases.2.1.analyticOnNhd gaussCutPlane_isOpen) A D A' D' hmid hW he

end DOZZ.Proofs

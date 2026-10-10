/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ClassificationDiagonalConstraint
public import DOZZ.Hypergeom.ClassificationHermitianMixedJet
public import DOZZ.Hypergeom.BasisRegularity

/-! Necessity in the diagonal-extension criterion `DOZZ.gauss_diagonal_extension_iff`. -/

@[expose] public section

namespace DOZZ.Proofs

private theorem hermitianQuadraticTensor_realDiagonal_eq
    {f g : ℂ → ℂ} (α δ : ℝ) (z : ℂ) :
    hermitianQuadraticTensor f g (α : ℂ) 0 0 (δ : ℂ) z =
      ((α * Complex.normSq (f z) + δ * Complex.normSq (g z) : ℝ) : ℂ) := by
  simp only [hermitianQuadraticTensor, zero_mul, add_zero]
  calc
    _ = (α : ℂ) * (f z * star (f z)) +
        (δ : ℂ) * (g z * star (g z)) := by ring
    _ = _ := by
      rw [complex_mul_star_eq_normSq, complex_mul_star_eq_normSq]
      push_cast
      ring

/-- Any global real Gauss solution agreeing with a diagonal norm-square formula on the cut plane
must have its coefficients on the undivided `K₁,K₂` line. -/
theorem gauss_diagonal_extension_iff_forward
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (a b c : ℝ) (hc : ∀ n : ℤ, c ≠ (n : ℝ))
    (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℝ)) (coeff₁ coeff₂ : ℝ)
    (hleft : ∃ T : ℂ → ℝ, IsRealGaussSolution a b c T ∧
      ∀ z ∈ gaussCutPlane,
        T z = coeff₁ * ‖gaussFMinus H a b c z‖ ^ 2 +
          coeff₂ * ‖gaussFPlus H a b c z‖ ^ 2) :
    gaussK₁ a b c * coeff₁ + gaussK₂ a b c * coeff₂ = 0 := by
  obtain ⟨T, hT, hrep⟩ := hleft
  obtain ⟨α, δ, hcanonical, hconstraint⟩ :=
    realGaussSolution_canonical_diagonal_constraint hH a b c hc hδ T hT
  have hcC : ∀ n : ℤ, (c : ℂ) ≠ (n : ℂ) := by
    intro n hn
    apply hc n
    exact_mod_cast hn
  have hzero := gauss_local_basis_zero hH (a : ℂ) (b : ℂ) (c : ℂ) hcC
  have hF : AnalyticOnNhd ℂ (gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ)) gaussCutPlane :=
    hzero.1.analyticOnNhd gaussCutPlane_isOpen
  have hG : AnalyticOnNhd ℂ (gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ)) gaussCutPlane :=
    hzero.2.1.analyticOnNhd gaussCutPlane_isOpen
  have hmid : (1 / 2 : ℂ) ∈ gaussCutPlane := by norm_num [gaussCutPlane]
  have hWr := (hzero.2.2.1 (1 / 2 : ℂ) hmid).2.2
  have h1c : (1 : ℂ) - (c : ℂ) ≠ 0 := by
    intro he
    apply hc 1
    have hreal : c = (1 : ℝ) := by exact_mod_cast (sub_eq_zero.mp he).symm
    simpa using hreal
  have hmid0 : (1 / 2 : ℂ) ≠ 0 := by norm_num
  have hmid1 : 1 - (1 / 2 : ℂ) ≠ 0 := by norm_num
  have hpow0 : (1 / 2 : ℂ) ^ (-(c : ℂ)) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hmid0)
  have hpow1 : (1 - (1 / 2 : ℂ)) ^
      ((c : ℂ) - (a : ℂ) - (b : ℂ) - 1) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hmid1)
  have hWmid :
      gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) (1 / 2 : ℂ) *
          deriv (gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ)) (1 / 2 : ℂ) -
        deriv (gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ)) (1 / 2 : ℂ) *
          gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) (1 / 2 : ℂ) ≠ 0 := by
    rw [hWr]
    exact mul_ne_zero (mul_ne_zero h1c hpow0) hpow1
  have hEq : ∀ z ∈ gaussCutPlane,
      hermitianQuadraticTensor (gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ))
        (gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ)) (α : ℂ) 0 0 (δ : ℂ) z =
      hermitianQuadraticTensor (gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ))
        (gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ))
        (coeff₁ : ℂ) 0 0 (coeff₂ : ℂ) z := by
    intro z hz
    have hreal : α * ‖gaussFMinus H a b c z‖ ^ 2 +
        δ * ‖gaussFPlus H a b c z‖ ^ 2 =
        coeff₁ * ‖gaussFMinus H a b c z‖ ^ 2 +
          coeff₂ * ‖gaussFPlus H a b c z‖ ^ 2 := by
      calc
        _ = T z := (hcanonical z hz).symm
        _ = _ := hrep z hz
    calc
      _ = ((α * Complex.normSq (gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) z) +
          δ * Complex.normSq (gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z) : ℝ) : ℂ) :=
        hermitianQuadraticTensor_realDiagonal_eq _ _ _
      _ = ((α * ‖gaussFMinus H a b c z‖ ^ 2 +
          δ * ‖gaussFPlus H a b c z‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
      _ = ((coeff₁ * ‖gaussFMinus H a b c z‖ ^ 2 +
          coeff₂ * ‖gaussFPlus H a b c z‖ ^ 2 : ℝ) : ℂ) := congrArg Complex.ofReal hreal
      _ = ((coeff₁ * Complex.normSq (gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) z) +
          coeff₂ * Complex.normSq (gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z) : ℝ) : ℂ) := by
        rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
      _ = _ := (hermitianQuadraticTensor_realDiagonal_eq coeff₁ coeff₂ z).symm
  have hcoeff := hermitianTensor_coefficients_eq_of_eqOn gaussCutPlane_isOpen
    hF hG α 0 0 δ coeff₁ 0 0 coeff₂ hmid hWmid hEq
  have hα : α = coeff₁ := Complex.ofReal_injective hcoeff.1
  have hdeltaCoeff : δ = coeff₂ := Complex.ofReal_injective hcoeff.2.2.2
  rw [← hα, ← hdeltaCoeff]
  exact hconstraint

end DOZZ.Proofs

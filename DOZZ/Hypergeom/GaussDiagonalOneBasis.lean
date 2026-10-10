/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.Defs
public import DOZZ.Hypergeom.GaussConnectionMinus
public import DOZZ.Hypergeom.GaussConnectionPlus
public import DOZZ.Hypergeom.ConnectionDiagonalAlgebra
public import DOZZ.Hypergeom.ConnectionDiagonalCoefficients

/-! The two connection formulas carry the zero-basis diagonal norm to the one-basis diagonal norm. -/

@[expose] public section

namespace DOZZ.Proofs

/-- The diagonal norm identity in the one-basis follows from the two Gauss connection
formulas and the weighted cancellation of their cross coefficient. -/
theorem gauss_diagonal_one_basis
    {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) (a b c : ℝ)
    (hc : ∀ n : ℤ, c ≠ (n : ℝ)) (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℝ))
    (hK₂ : gaussK₂ a b c ≠ 0) :
    ∀ z ∈ gaussCutPlane,
      ‖gaussFMinus H a b c z‖ ^ 2 + gaussCoefficientRatio a b c *
        ‖gaussFPlus H a b c z‖ ^ 2 =
      gaussCrossD a b c * ‖gaussGMinus H a b c z‖ ^ 2 +
        gaussCrossE a b c * ‖gaussGPlus H a b c z‖ ^ 2 := by
  let u : ℝ := Real.Gamma c * Real.Gamma (c - a - b) *
    (Real.Gamma (c - a))⁻¹ * (Real.Gamma (c - b))⁻¹
  let v : ℝ := Real.Gamma c * Real.Gamma (a + b - c) *
    (Real.Gamma a)⁻¹ * (Real.Gamma b)⁻¹
  let w : ℝ := Real.Gamma (2 - c) * Real.Gamma (c - a - b) *
    (Real.Gamma (1 - a))⁻¹ * (Real.Gamma (1 - b))⁻¹
  let x : ℝ := Real.Gamma (2 - c) * Real.Gamma (a + b - c) *
    (Real.Gamma (a - c + 1))⁻¹ * (Real.Gamma (b - c + 1))⁻¹
  have hδcast : ((c - a - b : ℝ) : ℂ) = (c : ℂ) - (a : ℂ) - (b : ℂ) := by
    push_cast
    ring
  have hnegδcast : ((a + b - c : ℝ) : ℂ) = (a : ℂ) + (b : ℂ) - (c : ℂ) := by
    push_cast
    ring
  have hcaCast : ((c - a : ℝ) : ℂ) = (c : ℂ) - (a : ℂ) := by push_cast; ring
  have hcbCast : ((c - b : ℝ) : ℂ) = (c : ℂ) - (b : ℂ) := by push_cast; ring
  have h2cCast : ((2 - c : ℝ) : ℂ) = (2 : ℂ) - (c : ℂ) := by push_cast; ring
  have h1aCast : ((1 - a : ℝ) : ℂ) = (1 : ℂ) - (a : ℂ) := by push_cast; ring
  have h1bCast : ((1 - b : ℝ) : ℂ) = (1 : ℂ) - (b : ℂ) := by push_cast; ring
  have hac1Cast : ((a - c + 1 : ℝ) : ℂ) = (a : ℂ) - (c : ℂ) + 1 := by push_cast; ring
  have hbc1Cast : ((b - c + 1 : ℝ) : ℂ) = (b : ℂ) - (c : ℂ) + 1 := by push_cast; ring
  have hU : Complex.Gamma (c : ℂ) * Complex.Gamma ((c : ℂ) - (a : ℂ) - (b : ℂ)) *
      (Complex.Gamma ((c : ℂ) - (a : ℂ)))⁻¹ *
        (Complex.Gamma ((c : ℂ) - (b : ℂ)))⁻¹ = (u : ℂ) := by
    rw [← hδcast, ← hcaCast, ← hcbCast]
    simp only [u, Complex.Gamma_ofReal, Complex.ofReal_inv, Complex.ofReal_mul]
  have hV : Complex.Gamma (c : ℂ) * Complex.Gamma ((a : ℂ) + (b : ℂ) - (c : ℂ)) *
      (Complex.Gamma (a : ℂ))⁻¹ * (Complex.Gamma (b : ℂ))⁻¹ = (v : ℂ) := by
    rw [← hnegδcast]
    simp only [v, Complex.Gamma_ofReal, Complex.ofReal_inv, Complex.ofReal_mul]
  have hW : Complex.Gamma (2 - (c : ℂ)) *
      Complex.Gamma ((c : ℂ) - (a : ℂ) - (b : ℂ)) *
        (Complex.Gamma (1 - (a : ℂ)))⁻¹ * (Complex.Gamma (1 - (b : ℂ)))⁻¹ =
      (w : ℂ) := by
    rw [← h2cCast, ← hδcast, ← h1aCast, ← h1bCast]
    simp only [w, Complex.Gamma_ofReal, Complex.ofReal_inv, Complex.ofReal_mul]
  have hX : Complex.Gamma (2 - (c : ℂ)) *
      Complex.Gamma ((a : ℂ) + (b : ℂ) - (c : ℂ)) *
        (Complex.Gamma ((a : ℂ) - (c : ℂ) + 1))⁻¹ *
          (Complex.Gamma ((b : ℂ) - (c : ℂ) + 1))⁻¹ = (x : ℂ) := by
    rw [← h2cCast, ← hnegδcast, ← hac1Cast, ← hbc1Cast]
    simp only [x, Complex.Gamma_ofReal, Complex.ofReal_inv, Complex.ofReal_mul]
  have hcC : ∀ n : ℤ, (c : ℂ) ≠ (n : ℂ) := by
    intro n hn
    apply hc n
    exact_mod_cast hn
  have hδC : ∀ n : ℤ, (c : ℂ) - (a : ℂ) - (b : ℂ) ≠ (n : ℂ) := by
    intro n hn
    apply hδ n
    have hnCast : (n : ℂ) = ((n : ℝ) : ℂ) := by simp
    apply Complex.ofReal_injective
    exact hδcast.trans (hn.trans hnCast)
  have hcross := gaussGammaConnection_weighted_cross_eq_zero a b c hK₂
  rw [show gaussConnectionMinusGammaCoefficient₁ (a, b, c) = (u : ℂ) by
        dsimp [gaussConnectionMinusGammaCoefficient₁]
        rw [← hδcast, ← hcaCast, ← hcbCast]
        simp only [u, Complex.Gamma_ofReal, Complex.ofReal_inv, Complex.ofReal_mul],
      show gaussConnectionMinusGammaCoefficient₂ (a, b, c) = (v : ℂ) by
        dsimp [gaussConnectionMinusGammaCoefficient₂]
        rw [← hnegδcast]
        simp only [v, Complex.Gamma_ofReal, Complex.ofReal_inv, Complex.ofReal_mul],
      show gaussConnectionPlusGammaCoefficient₁ (a, b, c) = (w : ℂ) by
        dsimp [gaussConnectionPlusGammaCoefficient₁]
        rw [← h2cCast, ← hδcast, ← h1aCast, ← h1bCast]
        simp only [w, Complex.Gamma_ofReal, Complex.ofReal_inv, Complex.ofReal_mul],
      show gaussConnectionPlusGammaCoefficient₂ (a, b, c) = (x : ℂ) by
        dsimp [gaussConnectionPlusGammaCoefficient₂]
        rw [← h2cCast, ← hnegδcast, ← hac1Cast, ← hbc1Cast]
        simp only [x, Complex.Gamma_ofReal, Complex.ofReal_inv, Complex.ofReal_mul]] at hcross
  have hcrossR : u * v + gaussCoefficientRatio a b c * w * x = 0 := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_zero,
      Complex.ofReal_ofNat] using hcross
  intro z hz
  have hminus := gauss_connection_minus hH (a : ℂ) (b : ℂ) (c : ℂ) hcC hδC z hz
  have hplus := gauss_connection_plus hH (a : ℂ) (b : ℂ) (c : ℂ) hcC hδC z hz
  have hminus' : gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) z =
      (u : ℂ) * gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ) z +
        (v : ℂ) * gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ) z := by
    rw [hU, hV] at hminus
    exact hminus
  have hplus' : gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z =
      (w : ℂ) * gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ) z +
        (x : ℂ) * gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ) z := by
    rw [hW, hX] at hplus
    exact hplus
  have hnorm := real_weighted_normSq_connection_change u v w x
    (gaussCoefficientRatio a b c)
    (gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ) z)
    (gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ) z) hcrossR
  have hD : u ^ 2 + gaussCoefficientRatio a b c * w ^ 2 = gaussCrossD a b c := by
    simp [gaussCrossD, u, w]
  have hE : v ^ 2 + gaussCoefficientRatio a b c * x ^ 2 = gaussCrossE a b c := by
    simp [gaussCrossE, v, x]
  calc
    _ = Complex.normSq (gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) z) +
        gaussCoefficientRatio a b c *
          Complex.normSq (gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z) := by
      simp only [← Complex.normSq_eq_norm_sq]
    _ = Complex.normSq ((u : ℂ) * gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ) z +
          (v : ℂ) * gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ) z) +
        gaussCoefficientRatio a b c *
          Complex.normSq ((w : ℂ) * gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ) z +
            (x : ℂ) * gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ) z) := by
      rw [hminus', hplus']
    _ = (u ^ 2 + gaussCoefficientRatio a b c * w ^ 2) *
          Complex.normSq (gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ) z) +
        (v ^ 2 + gaussCoefficientRatio a b c * x ^ 2) *
          Complex.normSq (gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ) z) := hnorm
    _ = gaussCrossD a b c *
          Complex.normSq (gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ) z) +
        gaussCrossE a b c *
          Complex.normSq (gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ) z) := by rw [hD, hE]
    _ = gaussCrossD a b c * ‖gaussGMinus H a b c z‖ ^ 2 +
        gaussCrossE a b c * ‖gaussGPlus H a b c z‖ ^ 2 := by
      simp only [← Complex.normSq_eq_norm_sq]

end DOZZ.Proofs

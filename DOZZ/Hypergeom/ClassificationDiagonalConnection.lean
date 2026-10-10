/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ConnectionDiagonalAlgebra
public import DOZZ.Hypergeom.ODE.ConnectionGammaCoefficients
public import DOZZ.Hypergeom.GaussConnectionMinus
public import DOZZ.Hypergeom.GaussConnectionPlus
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! Undivided coefficient transfer for the real Gauss connection matrix. -/

@[expose] public section

namespace DOZZ.Proofs

/-- The weighted connection cross coefficient vanishes directly from the undivided `K₁,K₂` relation.
This remains valid when either diagonal coefficient or `K₂` vanishes. -/
theorem gaussGammaConnection_weighted_cross_eq_zero_of_constraint
    (a b c α δ : ℝ) (hconstraint : gaussK₁ a b c * α + gaussK₂ a b c * δ = 0) :
    (α : ℂ) * gaussConnectionMinusGammaCoefficient₁ (a, b, c) *
        gaussConnectionMinusGammaCoefficient₂ (a, b, c) +
      (δ : ℂ) * gaussConnectionPlusGammaCoefficient₁ (a, b, c) *
        gaussConnectionPlusGammaCoefficient₂ (a, b, c) = 0 := by
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
  have hac1Cast : ((a - c + 1 : ℝ) : ℂ) = (a : ℂ) - (c : ℂ) + 1 := by
    push_cast
    ring
  have hbc1Cast : ((b - c + 1 : ℝ) : ℂ) = (b : ℂ) - (c : ℂ) + 1 := by
    push_cast
    ring
  have hU : gaussConnectionMinusGammaCoefficient₁ (a, b, c) = (u : ℂ) := by
    dsimp [gaussConnectionMinusGammaCoefficient₁, u]
    rw [← hδcast, ← hcaCast, ← hcbCast]
    simp only [Complex.Gamma_ofReal, Complex.ofReal_inv, Complex.ofReal_mul]
  have hV : gaussConnectionMinusGammaCoefficient₂ (a, b, c) = (v : ℂ) := by
    dsimp [gaussConnectionMinusGammaCoefficient₂, v]
    rw [← hnegδcast]
    simp only [Complex.Gamma_ofReal, Complex.ofReal_inv, Complex.ofReal_mul]
  have hW : gaussConnectionPlusGammaCoefficient₁ (a, b, c) = (w : ℂ) := by
    dsimp [gaussConnectionPlusGammaCoefficient₁, w]
    rw [← h2cCast, ← hδcast, ← h1aCast, ← h1bCast]
    simp only [Complex.Gamma_ofReal, Complex.ofReal_inv, Complex.ofReal_mul]
  have hX : gaussConnectionPlusGammaCoefficient₂ (a, b, c) = (x : ℂ) := by
    dsimp [gaussConnectionPlusGammaCoefficient₂, x]
    rw [← h2cCast, ← hnegδcast, ← hac1Cast, ← hbc1Cast]
    simp only [Complex.Gamma_ofReal, Complex.ofReal_inv, Complex.ofReal_mul]
  have hUV : u * v =
      Real.Gamma (c - a - b) * Real.Gamma (a + b - c) * gaussK₁ a b c := by
    dsimp [u, v, gaussK₁]
    ring
  have hWX : w * x =
      Real.Gamma (c - a - b) * Real.Gamma (a + b - c) * gaussK₂ a b c := by
    dsimp [w, x, gaussK₂]
    ring
  have hcross : α * u * v + δ * w * x = 0 := by
    calc
      α * u * v + δ * w * x = α * (u * v) + δ * (w * x) := by ring
      _ =
          α * (Real.Gamma (c - a - b) * Real.Gamma (a + b - c) * gaussK₁ a b c) +
            δ * (Real.Gamma (c - a - b) * Real.Gamma (a + b - c) * gaussK₂ a b c) := by
        rw [hUV, hWX]
      _ =
          Real.Gamma (c - a - b) * Real.Gamma (a + b - c) *
            (gaussK₁ a b c * α + gaussK₂ a b c * δ) := by ring
      _ = 0 := by rw [hconstraint]; ring
  rw [hU, hV, hW, hX]
  exact_mod_cast hcross

/-- The diagonal norm-square connection identity uses only the undivided coefficient constraint, and
therefore also covers the `K₂ = 0` case. -/
theorem gauss_diagonal_one_basis_of_constraint
    {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H) (a b c α δ : ℝ)
    (hc : ∀ n : ℤ, c ≠ (n : ℝ))
    (hδint : ∀ n : ℤ, c - a - b ≠ (n : ℝ))
    (hconstraint : gaussK₁ a b c * α + gaussK₂ a b c * δ = 0) :
    ∀ z ∈ gaussCutPlane,
      α * ‖gaussFMinus H a b c z‖ ^ 2 + δ * ‖gaussFPlus H a b c z‖ ^ 2 =
        (α * (Real.Gamma c * Real.Gamma (c - a - b) *
            (Real.Gamma (c - a))⁻¹ * (Real.Gamma (c - b))⁻¹) ^ 2 +
          δ * (Real.Gamma (2 - c) * Real.Gamma (c - a - b) *
            (Real.Gamma (1 - a))⁻¹ * (Real.Gamma (1 - b))⁻¹) ^ 2) *
            ‖gaussGMinus H a b c z‖ ^ 2 +
        (α * (Real.Gamma c * Real.Gamma (a + b - c) *
            (Real.Gamma a)⁻¹ * (Real.Gamma b)⁻¹) ^ 2 +
          δ * (Real.Gamma (2 - c) * Real.Gamma (a + b - c) *
            (Real.Gamma (a - c + 1))⁻¹ * (Real.Gamma (b - c + 1))⁻¹) ^ 2) *
            ‖gaussGPlus H a b c z‖ ^ 2 := by
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
  have hac1Cast : ((a - c + 1 : ℝ) : ℂ) = (a : ℂ) - (c : ℂ) + 1 := by
    push_cast
    ring
  have hbc1Cast : ((b - c + 1 : ℝ) : ℂ) = (b : ℂ) - (c : ℂ) + 1 := by
    push_cast
    ring
  have hU : gaussConnectionMinusGammaCoefficient₁ (a, b, c) = (u : ℂ) := by
    dsimp [gaussConnectionMinusGammaCoefficient₁, u]
    rw [← hδcast, ← hcaCast, ← hcbCast]
    simp only [Complex.Gamma_ofReal, Complex.ofReal_inv, Complex.ofReal_mul]
  have hV : gaussConnectionMinusGammaCoefficient₂ (a, b, c) = (v : ℂ) := by
    dsimp [gaussConnectionMinusGammaCoefficient₂, v]
    rw [← hnegδcast]
    simp only [Complex.Gamma_ofReal, Complex.ofReal_inv, Complex.ofReal_mul]
  have hW : gaussConnectionPlusGammaCoefficient₁ (a, b, c) = (w : ℂ) := by
    dsimp [gaussConnectionPlusGammaCoefficient₁, w]
    rw [← h2cCast, ← hδcast, ← h1aCast, ← h1bCast]
    simp only [Complex.Gamma_ofReal, Complex.ofReal_inv, Complex.ofReal_mul]
  have hX : gaussConnectionPlusGammaCoefficient₂ (a, b, c) = (x : ℂ) := by
    dsimp [gaussConnectionPlusGammaCoefficient₂, x]
    rw [← h2cCast, ← hnegδcast, ← hac1Cast, ← hbc1Cast]
    simp only [Complex.Gamma_ofReal, Complex.ofReal_inv, Complex.ofReal_mul]
  have hUGamma : Complex.Gamma (c : ℂ) * Complex.Gamma ((c : ℂ) - (a : ℂ) - (b : ℂ)) *
      (Complex.Gamma ((c : ℂ) - (a : ℂ)))⁻¹ *
        (Complex.Gamma ((c : ℂ) - (b : ℂ)))⁻¹ = (u : ℂ) := by
    simpa [gaussConnectionMinusGammaCoefficient₁] using hU
  have hVGamma : Complex.Gamma (c : ℂ) * Complex.Gamma ((a : ℂ) + (b : ℂ) - (c : ℂ)) *
      (Complex.Gamma (a : ℂ))⁻¹ * (Complex.Gamma (b : ℂ))⁻¹ = (v : ℂ) := by
    simpa [gaussConnectionMinusGammaCoefficient₂] using hV
  have hWGamma : Complex.Gamma (2 - (c : ℂ)) *
      Complex.Gamma ((c : ℂ) - (a : ℂ) - (b : ℂ)) *
        (Complex.Gamma (1 - (a : ℂ)))⁻¹ * (Complex.Gamma (1 - (b : ℂ)))⁻¹ = (w : ℂ) := by
    simpa [gaussConnectionPlusGammaCoefficient₁] using hW
  have hXGamma : Complex.Gamma (2 - (c : ℂ)) *
      Complex.Gamma ((a : ℂ) + (b : ℂ) - (c : ℂ)) *
        (Complex.Gamma ((a : ℂ) - (c : ℂ) + 1))⁻¹ *
          (Complex.Gamma ((b : ℂ) - (c : ℂ) + 1))⁻¹ = (x : ℂ) := by
    simpa [gaussConnectionPlusGammaCoefficient₂] using hX
  have hcC : ∀ n : ℤ, (c : ℂ) ≠ (n : ℂ) := by
    intro n hn
    apply hc n
    exact_mod_cast hn
  have hδC : ∀ n : ℤ, (c : ℂ) - (a : ℂ) - (b : ℂ) ≠ (n : ℂ) := by
    intro n hn
    apply hδint n
    have hnCast : (n : ℂ) = ((n : ℝ) : ℂ) := by simp
    apply Complex.ofReal_injective
    exact hδcast.trans (hn.trans hnCast)
  have hminus := gauss_connection_minus hH (a : ℂ) (b : ℂ) (c : ℂ) hcC hδC
  have hplus := gauss_connection_plus hH (a : ℂ) (b : ℂ) (c : ℂ) hcC hδC
  have hcross := gaussGammaConnection_weighted_cross_eq_zero_of_constraint
    a b c α δ hconstraint
  rw [hU, hV, hW, hX] at hcross
  have hcrossR : α * u * v + δ * w * x = 0 := by
    apply Complex.ofReal_injective
    exact_mod_cast hcross
  intro z hz
  have hminus' : gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) z =
      (u : ℂ) * gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ) z +
        (v : ℂ) * gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ) z := by
    rw [hUGamma, hVGamma] at hminus
    exact hminus z hz
  have hplus' : gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z =
      (w : ℂ) * gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ) z +
        (x : ℂ) * gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ) z := by
    rw [hWGamma, hXGamma] at hplus
    exact hplus z hz
  have hnorm := real_diagonal_normSq_connection_change α δ u v w x
    (gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ) z)
    (gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ) z) hcrossR
  calc
    _ = α * Complex.normSq (gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) z) +
        δ * Complex.normSq (gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z) := by
      simp only [← Complex.normSq_eq_norm_sq]
    _ = α * Complex.normSq ((u : ℂ) * gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ) z +
          (v : ℂ) * gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ) z) +
        δ * Complex.normSq ((w : ℂ) * gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ) z +
          (x : ℂ) * gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ) z) := by
      rw [hminus', hplus']
    _ = (α * u ^ 2 + δ * w ^ 2) *
          Complex.normSq (gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ) z) +
        (α * v ^ 2 + δ * x ^ 2) *
          Complex.normSq (gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ) z) := hnorm
    _ = _ := by
      simp only [← Complex.normSq_eq_norm_sq]
      simp [u, v, w, x]

end DOZZ.Proofs

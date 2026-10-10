/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Hypergeom.GaussCoefficientRatio
public import DOZZ.Hypergeom.ODE.ConnectionGammaCoefficients

/-! Gamma algebra for the real diagonal connection constraint. -/

@[expose] public section

namespace DOZZ.Proofs

/-- On the nondegenerate `K₂` locus, the coefficient ratio of [KRV, (Fundrelation)] solves the
undivided diagonal constraint. The proof retains the cases where a denominator Gamma is a pole: then
both the corresponding `K₁` factor and the totalized quotient vanish. -/
theorem gaussCoefficientRatio_mul_K₂_add_K₁_eq_zero
    (a b c : ℝ) (hK₂ : gaussK₂ a b c ≠ 0) :
    gaussCoefficientRatio a b c * gaussK₂ a b c + gaussK₁ a b c = 0 := by
  let d : ℝ := Real.Gamma (c - a) * Real.Gamma (c - b) *
    Real.Gamma a * Real.Gamma b
  have hGamma₂c : Real.Gamma (2 - c) ≠ 0 := by
    intro h
    apply hK₂
    simp [gaussK₂, h]
  have hInv₁a : (Real.Gamma (1 - a))⁻¹ ≠ 0 := by
    intro h
    apply hK₂
    simp [gaussK₂, h]
  have hInv₁b : (Real.Gamma (1 - b))⁻¹ ≠ 0 := by
    intro h
    apply hK₂
    simp [gaussK₂, h]
  have hInvAc : (Real.Gamma (a - c + 1))⁻¹ ≠ 0 := by
    intro h
    apply hK₂
    simp [gaussK₂, h]
  have hInvBc : (Real.Gamma (b - c + 1))⁻¹ ≠ 0 := by
    intro h
    apply hK₂
    simp [gaussK₂, h]
  have hGamma₁a : Real.Gamma (1 - a) ≠ 0 := by
    intro h
    apply hInv₁a
    simp [h]
  have hGamma₁b : Real.Gamma (1 - b) ≠ 0 := by
    intro h
    apply hInv₁b
    simp [h]
  have hGammaAc : Real.Gamma (a - c + 1) ≠ 0 := by
    intro h
    apply hInvAc
    simp [h]
  have hGammaBc : Real.Gamma (b - c + 1) ≠ 0 := by
    intro h
    apply hInvBc
    simp [h]
  by_cases hd : d = 0
  · have hFactor : Real.Gamma (c - a) = 0 ∨ Real.Gamma (c - b) = 0 ∨
        Real.Gamma a = 0 ∨ Real.Gamma b = 0 := by
      dsimp [d] at hd
      rcases mul_eq_zero.mp hd with h | h
      · rcases mul_eq_zero.mp h with h | h
        · rcases mul_eq_zero.mp h with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
    have hK₁ : gaussK₁ a b c = 0 := by
      rcases hFactor with h | h | h | h <;>
        simp [gaussK₁, h]
    have hden : Real.Gamma (2 - c) ^ 2 * Real.Gamma (c - a) * Real.Gamma (c - b) *
        Real.Gamma a * Real.Gamma b = 0 := by
      calc
        _ = Real.Gamma (2 - c) ^ 2 * d := by dsimp [d]; ring
        _ = 0 := by rw [hd]; ring
    have hratio : gaussCoefficientRatio a b c = 0 := by
      simp [gaussCoefficientRatio, hden]
    rw [hratio, hK₁]
    simp
  · have hGammaCa : Real.Gamma (c - a) ≠ 0 := by
      intro h
      apply hd
      simp [d, h]
    have hGammaCb : Real.Gamma (c - b) ≠ 0 := by
      intro h
      apply hd
      simp [d, h]
    have hGammaA : Real.Gamma a ≠ 0 := by
      intro h
      apply hd
      simp [d, h]
    have hGammaB : Real.Gamma b ≠ 0 := by
      intro h
      apply hd
      simp [d, h]
    dsimp [gaussCoefficientRatio, gaussK₁, gaussK₂]
    field_simp [hGamma₂c, hGammaCa, hGammaCb, hGammaA, hGammaB,
      hGamma₁a, hGamma₁b, hGammaAc, hGammaBc]
    ring

/-- For real parameters, the four Gamma connection entries satisfy the weighted off-diagonal
cancellation dictated by [KRV, (Fundrelation)] on the nondegenerate `K₂` locus. -/
theorem gaussGammaConnection_weighted_cross_eq_zero
    (a b c : ℝ) (hK₂ : gaussK₂ a b c ≠ 0) :
    gaussConnectionMinusGammaCoefficient₁ (a, b, c) *
        gaussConnectionMinusGammaCoefficient₂ (a, b, c) +
      (gaussCoefficientRatio a b c : ℂ) *
        gaussConnectionPlusGammaCoefficient₁ (a, b, c) *
          gaussConnectionPlusGammaCoefficient₂ (a, b, c) = 0 := by
  let u : ℝ := Real.Gamma c * Real.Gamma (c - a - b) *
    (Real.Gamma (c - a))⁻¹ * (Real.Gamma (c - b))⁻¹
  let v : ℝ := Real.Gamma c * Real.Gamma (a + b - c) *
    (Real.Gamma a)⁻¹ * (Real.Gamma b)⁻¹
  let w : ℝ := Real.Gamma (2 - c) * Real.Gamma (c - a - b) *
    (Real.Gamma (1 - a))⁻¹ * (Real.Gamma (1 - b))⁻¹
  let x : ℝ := Real.Gamma (2 - c) * Real.Gamma (a + b - c) *
    (Real.Gamma (a - c + 1))⁻¹ * (Real.Gamma (b - c + 1))⁻¹
  have hδarg : ((c - a - b : ℝ) : ℂ) = (c : ℂ) - a - b := by
    push_cast
    ring
  have hnegδarg : ((a + b - c : ℝ) : ℂ) = (a : ℂ) + b - c := by
    push_cast
    ring
  have hcaarg : ((c - a : ℝ) : ℂ) = (c : ℂ) - a := by
    push_cast
    ring
  have hcbarg : ((c - b : ℝ) : ℂ) = (c : ℂ) - b := by
    push_cast
    ring
  have h2carg : ((2 - c : ℝ) : ℂ) = (2 : ℂ) - c := by
    push_cast
    ring
  have h1aarg : ((1 - a : ℝ) : ℂ) = (1 : ℂ) - a := by
    push_cast
    ring
  have h1barg : ((1 - b : ℝ) : ℂ) = (1 : ℂ) - b := by
    push_cast
    ring
  have hacarg : ((a - c + 1 : ℝ) : ℂ) = (a : ℂ) - c + 1 := by
    push_cast
    ring
  have hbcarg : ((b - c + 1 : ℝ) : ℂ) = (b : ℂ) - c + 1 := by
    push_cast
    ring
  have hu : gaussConnectionMinusGammaCoefficient₁ (a, b, c) = (u : ℂ) := by
    dsimp [gaussConnectionMinusGammaCoefficient₁, u]
    rw [← hδarg, ← hcaarg, ← hcbarg]
    simp only [Complex.Gamma_ofReal, Complex.ofReal_inv, Complex.ofReal_mul]
  have hv : gaussConnectionMinusGammaCoefficient₂ (a, b, c) = (v : ℂ) := by
    dsimp [gaussConnectionMinusGammaCoefficient₂, v]
    rw [← hnegδarg]
    simp only [Complex.Gamma_ofReal, Complex.ofReal_inv, Complex.ofReal_mul]
  have hw : gaussConnectionPlusGammaCoefficient₁ (a, b, c) = (w : ℂ) := by
    dsimp [gaussConnectionPlusGammaCoefficient₁, w]
    rw [← h2carg, ← hδarg, ← h1aarg, ← h1barg]
    simp only [Complex.Gamma_ofReal, Complex.ofReal_inv, Complex.ofReal_mul]
  have hx : gaussConnectionPlusGammaCoefficient₂ (a, b, c) = (x : ℂ) := by
    dsimp [gaussConnectionPlusGammaCoefficient₂, x]
    rw [← h2carg, ← hnegδarg, ← hacarg, ← hbcarg]
    simp only [Complex.Gamma_ofReal, Complex.ofReal_inv, Complex.ofReal_mul]
  have hfactor : u * v + gaussCoefficientRatio a b c * w * x =
      Real.Gamma (c - a - b) * Real.Gamma (a + b - c) *
        (gaussK₁ a b c + gaussCoefficientRatio a b c * gaussK₂ a b c) := by
    dsimp [u, v, w, x, gaussK₁, gaussK₂]
    ring
  have hratio := gaussCoefficientRatio_mul_K₂_add_K₁_eq_zero a b c hK₂
  have hratio' : gaussK₁ a b c + gaussCoefficientRatio a b c * gaussK₂ a b c = 0 := by
    simpa [add_comm] using hratio
  have hcrossR : u * v + gaussCoefficientRatio a b c * w * x = 0 := by
    rw [hfactor, hratio']
    ring
  rw [hu, hv, hw, hx]
  exact_mod_cast hcrossR

end DOZZ.Proofs

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ClassificationCutCrossingJets
public import DOZZ.Hypergeom.ClassificationHermitianMixedJet
public import DOZZ.Hypergeom.ClassificationReflection
public import DOZZ.Hypergeom.BasisRegularity
public import DOZZ.Hypergeom.GaussConnectionMinus
public import DOZZ.Hypergeom.GaussConnectionPlus
public import DOZZ.Hypergeom.ODE.CutPlaneTopology
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! The one-basis reflection and connection formulas force the diagonal coefficient relation. -/

@[expose] public section

open scoped Topology

namespace DOZZ.Proofs

/-- The product of a complex number and its conjugate is its complex norm square. -/
theorem complex_mul_star_eq_normSq (z : ℂ) :
    z * star z = (Complex.normSq z : ℂ) := by
  calc
    z * star z = (‖z‖ ^ 2 : ℝ) := by
      simpa [Complex.star_def] using Complex.mul_conj' z
    _ = (Complex.normSq z : ℂ) := by rw [Complex.normSq_eq_norm_sq]

/-- Reflection identifies the shifted zero basis with the one basis. -/
private theorem gaussFPlus_reflection_eq_gaussGPlus
    (H : ℂ → ℂ → ℂ → ℂ → ℂ) (a b c z : ℂ) :
    gaussFPlus H a b (1 + a + b - c) (1 - z) = gaussGPlus H a b c z := by
  have he : 1 - (1 + a + b - c) = c - a - b := by ring
  have hA : a - (1 + a + b - c) + 1 = c - b := by ring
  have hB : b - (1 + a + b - c) + 1 = c - a := by ring
  have hC : 2 - (1 + a + b - c) = 1 + c - a - b := by ring
  simp only [gaussFPlus, gaussGPlus, he, hA, hB, hC]

/-- A reflected real solution has a diagonal Hermitian representation in the one basis, and
comparison with its zero-basis representation forces the undivided coefficient constraint. -/
theorem realGaussSolution_canonical_diagonal_constraint
    {H : ℂ → ℂ → ℂ → ℂ → ℂ} (hH : IsGaussHypergeometricFamily H)
    (a b c : ℝ) (hc : ∀ n : ℤ, c ≠ (n : ℝ))
    (hδ : ∀ n : ℤ, c - a - b ≠ (n : ℝ))
    (T : ℂ → ℝ) (hT : IsRealGaussSolution a b c T) :
    ∃ α δ : ℝ,
      (∀ z ∈ gaussCutPlane,
        T z = α * ‖gaussFMinus H a b c z‖ ^ 2 +
          δ * ‖gaussFPlus H a b c z‖ ^ 2) ∧
      gaussK₁ a b c * α + gaussK₂ a b c * δ = 0 := by
  obtain ⟨α, δ, β, hrep, hβ⟩ :=
    realGaussSolution_canonical_hermitian_offDiagonal_zero hH a b c hc T hT
  let c₁ : ℝ := 1 + a + b - c
  have hc₁ : ∀ n : ℤ, c₁ ≠ (n : ℝ) := by
    intro n hn
    apply hδ (1 - n)
    dsimp [c₁] at hn
    push_cast at hn ⊢
    linarith
  let T₁ : ℂ → ℝ := fun z => T (1 - z)
  have hT₁ : IsRealGaussSolution a b c₁ T₁ := by
    simpa [T₁, c₁] using realGaussSolution_reflection a b c T hT
  obtain ⟨α₁, δ₁, β₁, hrep₁, hβ₁⟩ :=
    realGaussSolution_canonical_hermitian_offDiagonal_zero hH a b c₁ hc₁ T₁ hT₁
  let u : ℝ := Real.Gamma c * Real.Gamma (c - a - b) *
    (Real.Gamma (c - a))⁻¹ * (Real.Gamma (c - b))⁻¹
  let v : ℝ := Real.Gamma c * Real.Gamma (a + b - c) *
    (Real.Gamma a)⁻¹ * (Real.Gamma b)⁻¹
  let w : ℝ := Real.Gamma (2 - c) * Real.Gamma (c - a - b) *
    (Real.Gamma (1 - a))⁻¹ * (Real.Gamma (1 - b))⁻¹
  let x : ℝ := Real.Gamma (2 - c) * Real.Gamma (a + b - c) *
    (Real.Gamma (a - c + 1))⁻¹ * (Real.Gamma (b - c + 1))⁻¹
  let A : ℝ := α * u ^ 2 + δ * w ^ 2
  let B : ℝ := α * u * v + δ * w * x
  let D : ℝ := α * v ^ 2 + δ * x ^ 2
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
    have hn' : ((c - a - b : ℝ) : ℂ) = (n : ℂ) := by
      calc
        ((c - a - b : ℝ) : ℂ) = (c : ℂ) - (a : ℂ) - (b : ℂ) := hδcast
        _ = (n : ℂ) := hn
    exact_mod_cast hn'
  have hminusConn := gauss_connection_minus hH (a : ℂ) (b : ℂ) (c : ℂ) hcC hδC
  have hplusConn := gauss_connection_plus hH (a : ℂ) (b : ℂ) (c : ℂ) hcC hδC
  have hlocal := gauss_local_basis_one hH (a : ℂ) (b : ℂ) (c : ℂ) hδC
  have hGminus : AnalyticOnNhd ℂ (gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ)) gaussCutPlane :=
    hlocal.1.analyticOnNhd gaussCutPlane_isOpen
  have hGplus : AnalyticOnNhd ℂ (gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ)) gaussCutPlane :=
    hlocal.2.1.analyticOnNhd gaussCutPlane_isOpen
  have hmid : (1 / 2 : ℂ) ∈ gaussCutPlane := by
    norm_num [gaussCutPlane]
  have hwr := (hlocal.2.2.1 (1 / 2 : ℂ) hmid).2.2
  have hδ0 : (c : ℂ) - (a : ℂ) - (b : ℂ) ≠ 0 := by
    intro hz
    apply hδ 0
    have hz' : ((c - a - b : ℝ) : ℂ) = 0 := by rw [hδcast]; exact hz
    exact_mod_cast hz'
  have hmid0 : (1 / 2 : ℂ) ≠ 0 := by norm_num
  have hmid1 : 1 - (1 / 2 : ℂ) ≠ 0 := by norm_num
  have hpow0 : (1 / 2 : ℂ) ^ (-(c : ℂ)) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hmid0)
  have hpow1 : (1 - (1 / 2 : ℂ)) ^
      ((c : ℂ) - (a : ℂ) - (b : ℂ) - 1) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hmid1)
  have hWmid :
      gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ) (1 / 2 : ℂ) *
          deriv (gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ)) (1 / 2 : ℂ) -
        deriv (gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ)) (1 / 2 : ℂ) *
          gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ) (1 / 2 : ℂ) ≠ 0 := by
    rw [hwr]
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hδ0) hpow0) hpow1
  have hEq : ∀ z ∈ gaussCutPlane,
      hermitianQuadraticTensor (gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ))
        (gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ)) (A : ℂ) (B : ℂ) (B : ℂ) (D : ℂ) z =
      hermitianQuadraticTensor (gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ))
        (gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ)) (α₁ : ℂ) 0 0 (δ₁ : ℂ) z := by
    intro z hz
    have hminus := hminusConn z hz
    have hplus := hplusConn z hz
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
    have hOrig := hrep z hz
    rw [hβ] at hOrig
    have hOrigTensor : (T z : ℂ) = hermitianQuadraticTensor
        (gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ))
        (gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ)) (α : ℂ) 0 0 (δ : ℂ) z := by
      simpa [hermitianQuadraticTensor, star_mul, mul_comm, mul_left_comm, mul_assoc] using hOrig
    have hz' := one_sub_gaussCutPlane_subset_gaussCutPlane hz
    have hRef := hrep₁ (1 - z) hz'
    rw [hβ₁] at hRef
    have hRefTensor : (T z : ℂ) = hermitianQuadraticTensor
        (gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ))
        (gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ)) (α₁ : ℂ) 0 0 (δ₁ : ℂ) z := by
      calc
        (T z : ℂ) = (T (1 - (1 - z)) : ℂ) := by congr 1; ring_nf
        _ = (T₁ (1 - z) : ℂ) := rfl
        _ = hermitianQuadraticTensor
            (gaussFMinus H (a : ℂ) (b : ℂ) (c₁ : ℂ))
            (gaussFPlus H (a : ℂ) (b : ℂ) (c₁ : ℂ))
            (α₁ : ℂ) 0 0 (δ₁ : ℂ) (1 - z) := by
          simpa [hermitianQuadraticTensor, star_mul, mul_comm, mul_left_comm, mul_assoc] using hRef
        _ = hermitianQuadraticTensor
            (gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ))
            (gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ))
            (α₁ : ℂ) 0 0 (δ₁ : ℂ) z := by
          have hc₁cast : (c₁ : ℂ) = 1 + (a : ℂ) + (b : ℂ) - (c : ℂ) := by
            dsimp [c₁]
            push_cast
            ring
          have hfm : gaussFMinus H (a : ℂ) (b : ℂ) (c₁ : ℂ) (1 - z) =
              gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ) z := by
            rw [hc₁cast]
            rfl
          have hfp : gaussFPlus H (a : ℂ) (b : ℂ) (c₁ : ℂ) (1 - z) =
              gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ) z := by
            rw [hc₁cast]
            exact gaussFPlus_reflection_eq_gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ) z
          simp only [hermitianQuadraticTensor]
          rw [hfm, hfp]
    have hchange : hermitianQuadraticTensor
        (gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ))
        (gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ)) (α : ℂ) 0 0 (δ : ℂ) z =
      hermitianQuadraticTensor (gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ))
        (gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ)) (A : ℂ) (B : ℂ) (B : ℂ) (D : ℂ) z := by
      simp only [hermitianQuadraticTensor]
      rw [hminus', hplus']
      simp [A, B, D, star_add, star_mul, mul_add, add_mul]
      ring_nf
    calc
      _ = hermitianQuadraticTensor
          (gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ))
          (gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ)) (α : ℂ) 0 0 (δ : ℂ) z := hchange.symm
      _ = (T z : ℂ) := hOrigTensor.symm
      _ = hermitianQuadraticTensor
          (gaussGMinus H (a : ℂ) (b : ℂ) (c : ℂ))
          (gaussGPlus H (a : ℂ) (b : ℂ) (c : ℂ)) (α₁ : ℂ) 0 0 (δ₁ : ℂ) z := hRefTensor
  have hcoeff := hermitianTensor_coefficients_eq_of_eqOn gaussCutPlane_isOpen
    hGminus hGplus A B B D α₁ 0 0 δ₁ hmid hWmid hEq
  have hBcomplex : (B : ℂ) = 0 := hcoeff.2.1
  have hB : B = 0 := Complex.ofReal_injective hBcomplex
  have hGammaDelta : Real.Gamma (c - a - b) ≠ 0 := by
    apply Real.Gamma_ne_zero
    intro n hn
    apply hδ (-(n : ℤ))
    push_cast at hn ⊢
    linarith
  have hGammaNegDelta : Real.Gamma (a + b - c) ≠ 0 := by
    apply Real.Gamma_ne_zero
    intro n hn
    apply hδ n
    push_cast at hn ⊢
    linarith
  have hfactor : Real.Gamma (c - a - b) * Real.Gamma (a + b - c) ≠ 0 :=
    mul_ne_zero hGammaDelta hGammaNegDelta
  have hfactorization :
      B = Real.Gamma (c - a - b) * Real.Gamma (a + b - c) *
        (gaussK₁ a b c * α + gaussK₂ a b c * δ) := by
    dsimp [B, u, v, w, x, gaussK₁, gaussK₂]
    ring
  have hconstraint : gaussK₁ a b c * α + gaussK₂ a b c * δ = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hfactor
    rw [← hfactorization, hB]
  refine ⟨α, δ, ?_, hconstraint⟩
  intro z hz
  have hOrig := hrep z hz
  apply Complex.ofReal_injective
  calc
    (T z : ℂ) = gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) z *
        star ((α : ℂ) * gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) z) +
      gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z *
        star ((δ : ℂ) * gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z) := by
      simpa [hβ] using hOrig
    _ = (α : ℂ) * (gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) z *
          star (gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) z)) +
        (δ : ℂ) * (gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z *
          star (gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z)) := by
      simp only [star_mul, Complex.star_def, Complex.conj_ofReal]
      ring
    _ = (α : ℂ) * Complex.normSq (gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) z) +
        (δ : ℂ) * Complex.normSq (gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z) := by
      rw [complex_mul_star_eq_normSq, complex_mul_star_eq_normSq]
    _ = (α : ℂ) * (‖gaussFMinus H (a : ℂ) (b : ℂ) (c : ℂ) z‖ ^ 2 : ℝ) +
        (δ : ℂ) * (‖gaussFPlus H (a : ℂ) (b : ℂ) (c : ℂ) z‖ ^ 2 : ℝ) := by
      simp only [Complex.normSq_eq_norm_sq]
    _ = ((α * ‖gaussFMinus H a b c z‖ ^ 2 +
        δ * ‖gaussFPlus H a b c z‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring

end DOZZ.Proofs

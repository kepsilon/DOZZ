/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.LocalR2Limit
public import DOZZ.FourPoint.Fusion.LocalR1Coefficient

/-! # Exact normalization of the local mixed derivative coefficient -/

@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace DOZZ.Proofs

theorem fusion_mixed_coefficient (p e q E J : ℝ) (he : -1 < e) (A : ℂ)
    (hJ : ((q ^ 2 * J : ℝ) : ℂ) = (((e + 2) / 2) ^ 2 : ℝ) * A) :
    ((-2 * p * q ^ 2 : ℝ) : ℂ) *
      ((1 / ((e + 1) * (e + 2)) : ℝ) * ((J : ℂ) * (E : ℂ))) =
      ((-p / 2 * (e + 2) / (e + 1) : ℝ) : ℂ) * (A * (E : ℂ)) := by
  have h1 : ((e + 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have h2 : ((e + 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  push_cast at h1 h2
  calc
    _ = (-2 * p : ℂ) * ((1 / ((e + 1) * (e + 2)) : ℝ) : ℂ) *
        (((q ^ 2 * J : ℝ) : ℂ) * (E : ℂ)) := by push_cast; ring
    _ = _ := by rw [hJ]; push_cast; field_simp [h1, h2]

/-- The mixed local coefficient is the complementary planar ratio in the Taylor sum. -/
theorem fusionLocalR2_coefficient_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hlo : γ / 2 < α₁) (hsq : 2 < γ ^ 2) (hα₁ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (p : ℝ) (hp : 0 ≤ p) :
    Tendsto (fun z : ℂ => fusionLocalR2 P M γ α₁ α₂ α₃ p z /
      (‖z‖ ^ (γ * (Q γ - α₁)) : ℝ)) (nhdsWithin 0 {0}ᶜ)
      (nhds (((-p / 2 * (γ ^ 2 / 2 - γ * α₁ + 2) / (γ ^ 2 / 2 - γ * α₁ + 1) *
        gammaHalfRootedCoefficient P M γ α₁ α₂ α₃ p : ℝ) : ℂ))) := by
  obtain ⟨hk, hβ, hβ2, hβlin, _, _⟩ := fusion_taylor_parameters γ α₁ hγ hlo hsq hα₁
  have h := fusionLocalR2_normalized_tendsto P X hX γ hγ hγ2 M hM α₁ α₂ α₃
    hlo hsq hα₁ hα₂ hα₃ p hp
  have hJ := (planar_mixed_integral (γ ^ 2 / 2) (γ * α₁) hk hβ hβ2 1 (by norm_num)).2
  simp only [norm_one, Real.one_rpow, mul_one] at hJ
  have hq : γ ^ 2 / 2 / 2 = γ ^ 2 / 4 := by ring
  rw [hq] at hJ
  have he : 2 + γ ^ 2 / 2 - γ * α₁ = γ ^ 2 / 2 - γ * α₁ + 2 := by ring
  rw [he] at hJ
  have hc := fusion_mixed_coefficient p (γ ^ 2 / 2 - γ * α₁) (γ ^ 2 / 4)
    (∫⁻ ω, fusionMovingMass γ α₁ α₂ α₃ 1 0 (M ω) ^ (-p - 1) ∂P).toReal
    (∫ y : ℂ, planarMixedKernel (γ ^ 2 / 2) (γ * α₁) 1 y) (by linarith) _ hJ
  rw [hc, fusion_planarGauss_real _ _ hk hβ hβ2 hβlin,
    fusion_local_inverse_coefficient_eq P X hX γ hγ hγ2 M hM α₁ α₂ α₃ (-p - 1)] at h
  simpa only [gammaHalfRootedCoefficient, ENNReal.rpow_eq_pow, Complex.ofReal_mul, mul_assoc] using h

end DOZZ.Proofs

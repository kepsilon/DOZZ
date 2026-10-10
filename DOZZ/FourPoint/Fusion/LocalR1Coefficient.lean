/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.LocalR1Limit

/-! # Exact normalization of the local pure derivative coefficient -/

@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The exact Wirtinger integral and elementary time integral determine the pure coefficient. -/
theorem fusion_pure_coefficient (p e q E : ℝ) (he : -1 < e) (W A : ℂ)
    (hW : (q : ℂ) * (q - 1 : ℝ) * W = ((e + 2) / 2 : ℝ) * ((e + 2) / 2 - 1 : ℝ) * A) :
    ((-p * q * (q - 1) : ℝ) : ℂ) *
      ((1 / ((e + 1) * (e + 2)) : ℝ) * (W * (E : ℂ))) =
      ((-p / 4 * e / (e + 1) : ℝ) : ℂ) * (A * (E : ℂ)) := by
  have h1 : ((e + 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have h2 : ((e + 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  push_cast at h1 h2
  calc
    _ = (-p : ℂ) * ((1 / ((e + 1) * (e + 2)) : ℝ) : ℂ) *
        (((q : ℂ) * (q - 1 : ℝ) * W) * (E : ℂ)) := by push_cast; ring
    _ = _ := by rw [hW]; push_cast; field_simp [h1, h2]; ring

/-- The limiting moving inverse expectation is exactly the moment in
`gammaHalfRootedCoefficient`. -/
theorem fusion_local_inverse_coefficient_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ s : ℝ) :
    (∫⁻ ω, fusionMovingMass γ α₁ α₂ α₃ 1 0 (M ω) ^ s ∂P) =
      ∫⁻ ω, gammaHalfRootedMass γ α₁ α₂ α₃ M ω ^ s ∂P := by
  apply lintegral_congr_ae
  filter_upwards [fusionMovingMass_eq_rooted_ae P X hX γ hγ hγ2 M hM α₁ α₂ α₃ 1 0] with ω hω
  simpa only [mul_zero, gammaHalfRootedMass] using congrArg (fun a : ℝ≥0∞ => a ^ s) hω

/-- The local `r₁` coefficient is the exact rooted coefficient `gammaHalfRootedCoefficient`
times the planar ratio. -/
theorem fusionLocalR1_coefficient_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hlo : γ / 2 < α₁) (hsq : 2 < γ ^ 2) (hα₁ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (p : ℝ) (hp : 0 ≤ p) :
    Filter.Tendsto (fun z : ℂ => fusionLocalR1 P M γ α₁ α₂ α₃ p z /
      (‖z‖ ^ (γ * (Q γ - α₁)) : ℝ)) (nhdsWithin 0 {0}ᶜ)
      (nhds (((-p / 4 * (γ ^ 2 / 2 - γ * α₁) / (γ ^ 2 / 2 - γ * α₁ + 1) *
        gammaHalfRootedCoefficient P M γ α₁ α₂ α₃ p : ℝ) : ℂ))) := by
  obtain ⟨hk, hβ, hβ2, hβlin, _, _⟩ := fusion_taylor_parameters γ α₁ hγ hlo hsq hα₁
  have h := fusionLocalR1_normalized_tendsto P X hX γ hγ hγ2 M hM α₁ α₂ α₃
    hlo hsq hα₁ hα₂ hα₃ p hp
  have hW := (planar_wirtinger_integral (γ ^ 2 / 2) (γ * α₁) hk hβ hβ2 1 (by norm_num)).2
  simp only [norm_one, Real.one_rpow, one_pow, div_one, Complex.ofReal_one, mul_one] at hW
  have hq : γ ^ 2 / 2 / 2 = γ ^ 2 / 4 := by ring
  rw [hq] at hW
  have he : 2 + γ ^ 2 / 2 - γ * α₁ = γ ^ 2 / 2 - γ * α₁ + 2 := by ring
  rw [he] at hW
  have hc := fusion_pure_coefficient p (γ ^ 2 / 2 - γ * α₁) (γ ^ 2 / 4)
    (∫⁻ ω, fusionMovingMass γ α₁ α₂ α₃ 1 0 (M ω) ^ (-p - 1) ∂P).toReal
    (by linarith) _ _ hW
  rw [hc, fusion_planarGauss_real _ _ hk hβ hβ2 hβlin,
    fusion_local_inverse_coefficient_eq P X hX γ hγ hγ2 M hM α₁ α₂ α₃ (-p - 1)] at h
  simpa only [gammaHalfRootedCoefficient, ENNReal.rpow_eq_pow, Complex.ofReal_mul, mul_assoc] using h

end DOZZ.Proofs

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.ScaledSpatialBound
public import DOZZ.FourPoint.Fusion.ScaledLocalRooting
public import DOZZ.FourPoint.Fusion.ScaledLocalMixedRooting
public import DOZZ.FourPoint.Fusion.Parameters
/-! # Local spatial expectation power bounds -/
@[expose] public section
open MeasureTheory Set
namespace DOZZ.Proofs
/-- The local `r₁` spatial expectation is bounded by its scaling power. -/
theorem fusion_localR1_expectation_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hlo : γ / 2 < α₁) (hα₁ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (p : ℝ) (hp : 0 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z ≠ 0 → ‖z‖ ≤ 1 / 4 →
      ‖∫ ω, ((coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ ^ (-p - 1)).toReal : ℂ) *
        (∫ x in Metric.ball (0 : ℂ) (1 / 2),
          (gammaHalfKernel γ α₁ α₂ α₃ z x : ℂ) / (x - z) ^ 2 ∂M ω) ∂P‖ ≤
        C * ‖z‖ ^ (γ ^ 2 / 2 - γ * α₁) := by
  have hk : 0 < γ ^ 2 / 2 := by positivity
  have hβ : γ ^ 2 / 2 < γ * α₁ := by nlinarith [mul_lt_mul_of_pos_left hlo hγ]
  have hβ2 : γ * α₁ < 2 := by have h := (lt_div_iff₀ hγ).mp hα₁; nlinarith
  have hK : Integrable (planarWirtingerKernel (γ ^ 2 / 2) (γ * α₁) 1) volume := (planar_wirtinger_integral (γ ^ 2 / 2) (γ * α₁) hk hβ hβ2 1 (by norm_num)).1
  obtain ⟨C, hC, hb⟩ := fusionScaledIntegral_bound P X hX γ hγ hγ2 M hM α₁ α₂ α₃
    (-p - 1) (by linarith) _ hK
  refine ⟨C, hC, ?_⟩
  intro z hz hz4
  rw [fusion_localR1_rooting P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hβ hα₁ hα₂ hα₃
    (-p - 1) (by linarith) z hz hz4,
    fusion_localR1_reference_scaled P X hX γ hγ hγ2 M hM α₁ α₂ α₃ (-p - 1) z hz]
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have he : ‖(‖z‖ ^ (2 + γ ^ 2 / 2 - γ * α₁) : ℝ) / z ^ 2‖ =
      ‖z‖ ^ (γ ^ 2 / 2 - γ * α₁) := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), norm_pow]
    have hx : 2 + γ ^ 2 / 2 - γ * α₁ = (γ ^ 2 / 2 - γ * α₁) + 2 := by ring
    rw [hx, Real.rpow_add hn, Real.rpow_two, mul_div_cancel_right₀ _ (pow_ne_zero 2 hn.ne')]
  rw [norm_mul, he]
  calc
    _ ≤ ‖z‖ ^ (γ ^ 2 / 2 - γ * α₁) * C :=
      mul_le_mul_of_nonneg_left (hb z (by linarith)) (Real.rpow_nonneg (norm_nonneg _) _)
    _ = _ := mul_comm _ _

/-- The local `r₂` spatial expectation is bounded by its scaling power. -/
theorem fusion_localR2_expectation_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hlo : γ / 2 < α₁) (hα₁ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (p : ℝ) (hp : 0 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, z ≠ 0 → ‖z‖ ≤ 1 / 4 →
      ‖∫ ω, ((coulombMass γ (M ω) ![-γ / 2, α₁, α₂] ![z, 0, 1] α₃ ^ (-p - 1)).toReal : ℂ) *
        (∫ x in Metric.ball (0 : ℂ) (1 / 2),
          (gammaHalfKernel γ α₁ α₂ α₃ z x : ℂ) / (‖x - z‖ ^ 2 : ℝ) ∂M ω) ∂P‖ ≤
        C * ‖z‖ ^ (γ ^ 2 / 2 - γ * α₁) := by
  have hk : 0 < γ ^ 2 / 2 := by positivity
  have hβ : γ ^ 2 / 2 < γ * α₁ := by nlinarith [mul_lt_mul_of_pos_left hlo hγ]
  have hβ2 : γ * α₁ < 2 := by have h := (lt_div_iff₀ hγ).mp hα₁; nlinarith
  have hK : Integrable ((fun y : ℂ => (planarMixedKernel (γ ^ 2 / 2) (γ * α₁) 1 y : ℂ))) volume := (planar_mixed_integral (γ ^ 2 / 2) (γ * α₁) hk hβ hβ2 1 (by norm_num)).1.ofReal
  obtain ⟨C, hC, hb⟩ := fusionScaledIntegral_bound P X hX γ hγ hγ2 M hM α₁ α₂ α₃
    (-p - 1) (by linarith) _ hK
  refine ⟨C, hC, ?_⟩
  intro z hz hz4
  rw [fusion_localR2_rooting P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hβ hα₁ hα₂ hα₃
    (-p - 1) (by linarith) z hz hz4,
    fusion_localR2_reference_scaled P X hX γ hγ hγ2 M hM α₁ α₂ α₃ (-p - 1) z hz]
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  calc
    _ ≤ ‖z‖ ^ (γ ^ 2 / 2 - γ * α₁) * C :=
      mul_le_mul_of_nonneg_left (hb z (by linarith)) (Real.rpow_nonneg (norm_nonneg _) _)
    _ = _ := mul_comm _ _

end DOZZ.Proofs

/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.LocalR1Scaling
public import DOZZ.Statements.FourPoint.GammaHalfRootedCoefficient

/-! # The normalized local pure derivative limit -/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The planar constant is real in the Taylor-integrability window. -/
theorem fusion_planarGauss_real (k β : ℝ) (hk : 0 < k) (hβ : k < β)
    (hβ2 : β < 2) (hβlin : β < k + 1) :
    planarGaussConstant k β = ((planarGaussConstant k β).re : ℂ) := by
  have h := planarTaylor_constant_from_discrete_laplacian k β hk hβ hβ2 hβlin
  rw [← h]
  rfl

/-- The normalized local `r₁` term tends to its scaled spatial-time integral coefficient. -/
theorem fusionLocalR1_normalized_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hlo : γ / 2 < α₁) (hsq : 2 < γ ^ 2) (hα₁ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (p : ℝ) (hp : 0 ≤ p) :
    Tendsto (fun z : ℂ => fusionLocalR1 P M γ α₁ α₂ α₃ p z /
      (‖z‖ ^ (γ * (Q γ - α₁)) : ℝ)) (nhdsWithin 0 {0}ᶜ)
      (nhds (((-p * (γ ^ 2 / 4) * (γ ^ 2 / 4 - 1) : ℝ) : ℂ) *
        ((1 / ((γ ^ 2 / 2 - γ * α₁ + 1) * (γ ^ 2 / 2 - γ * α₁ + 2)) : ℝ) *
          ((∫ y : ℂ, planarWirtingerKernel (γ ^ 2 / 2) (γ * α₁) 1 y) *
            ((∫⁻ ω, fusionMovingMass γ α₁ α₂ α₃ 1 0 (M ω) ^ (-p - 1) ∂P).toReal : ℂ))))) := by
  obtain ⟨hk, hβ, hβ2, hβlin, _, _⟩ := fusion_taylor_parameters γ α₁ hγ hlo hsq hα₁
  have hK : Integrable (planarWirtingerKernel (γ ^ 2 / 2) (γ * α₁) 1) volume :=
    (planar_wirtinger_integral (γ ^ 2 / 2) (γ * α₁) hk hβ hβ2 1 (by norm_num)).1
  have hKm : Measurable (planarWirtingerKernel (γ ^ 2 / 2) (γ * α₁) 1) := by
    unfold planarWirtingerKernel
    exact (Complex.measurable_ofReal.comp
      ((measurable_id.sub_const (1 : ℂ)).norm.pow_const _)).div
      (((measurable_const.sub measurable_id).pow_const 2).mul
        (Complex.measurable_ofReal.comp (measurable_id.norm.pow_const _)))
  have h := fusionScaledTimeIntegral_tendsto P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hlo.le hα₁ hα₂ hα₃
    (-p - 1) (by linarith) _ hKm hK (γ ^ 2 / 2 - γ * α₁) (by linarith)
  have hc := (tendsto_const_nhds (x := ((-p * (γ ^ 2 / 4) * (γ ^ 2 / 4 - 1) : ℝ) : ℂ))).mul h
  apply (hc.mono_left (show nhdsWithin (0 : ℂ) {0}ᶜ ≤ nhds 0 from nhdsWithin_le_nhds)).congr' 
  have hz4 : ∀ᶠ z : ℂ in nhdsWithin 0 {0}ᶜ, ‖z‖ ≤ 1 / 4 := by
    have h : ∀ᶠ z : ℂ in nhds 0, ‖z‖ < 1 / 4 :=
      (continuous_norm.tendsto (0 : ℂ)).eventually_lt_const (by simp)
    exact (h.filter_mono nhdsWithin_le_nhds).mono fun _ h => h.le
  filter_upwards [hz4, self_mem_nhdsWithin] with z hz4 hz
  have hz0 : z ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hz
  rw [fusionLocalR1_scaled P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hβ hα₁ hα₂ hα₃ p hp z hz0 hz4]
  have hr : (‖z‖ ^ (γ * (Q γ - α₁)) : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos (norm_pos_iff.mpr hz0) _).ne'
  have hcancel (a b c : ℂ) (hb : b ≠ 0) : a * b * c / b = a * c := by
    rw [mul_assoc, mul_comm b c, ← mul_assoc, mul_div_cancel_right₀ _ hb]
  exact (hcancel _ _ _ (Complex.ofReal_ne_zero.mpr hr)).symm

end DOZZ.Proofs

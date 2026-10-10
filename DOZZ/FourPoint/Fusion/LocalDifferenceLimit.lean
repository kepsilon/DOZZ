/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.LocalDifferenceRooting
public import DOZZ.FourPoint.Fusion.InterpolatedTimeConvergence
public import DOZZ.Statements.FourPoint.GammaHalfRootedCoefficient
/-! # The signed local KRV coefficient limit -/
@[expose] public section
open MeasureTheory Set Filter Topology
namespace DOZZ.Proofs
/-- Spatial and time dominated convergence yields the normalized local mass difference. -/
theorem fusion_localDifference_normalized_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hlo : γ / 2 + 1 / γ < α₁) (hα₁ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (p : ℝ) (hp : 0 ≤ p) :
    Tendsto (fun z : ℂ => (∫ t in Icc (0 : ℝ) 1,
      ∫ ω, (fusionUnrootedSegment γ α₁ α₂ α₃ t z (M ω) ^ (-p - 1)).toReal *
        (∫ x in Metric.ball (0 : ℂ) (1 / 2), fusionDifferenceKernel γ α₁ α₂ α₃ z x ∂M ω) ∂P) /
      ‖z‖ ^ (γ * (Q γ - α₁))) (nhdsWithin 0 {0}ᶜ)
      (nhds (gammaHalfRootedCoefficient P M γ α₁ α₂ α₃ p)) := by
  obtain ⟨hk, hβ, hβ2, _, _⟩ := fusion_difference_parameters γ α₁ hγ hlo hα₁
  let K := planarDifferenceKernel (γ ^ 2 / 2) (γ * α₁) 1
  have hK : Integrable K volume := (planar_difference_integral _ _ hk hβ hβ2 1).1
  have hm : Measurable K := by
    unfold K planarDifferenceKernel
    exact (((measurable_id.sub_const (1 : ℂ)).norm.pow_const _).sub
      (measurable_id.norm.pow_const _)).div (measurable_id.norm.pow_const _)
  have hc := fusionInterpolatedTimeIntegral_tendsto P X hX γ hγ hγ2 M hM α₁ α₂ α₃
    (by have := div_pos (show (0 : ℝ) < 1 by norm_num) hγ; linarith)
    hα₁ hα₂ hα₃ (-p - 1) (by linarith) (fun y => (K y : ℂ))
    (Complex.measurable_ofReal.comp hm) (hK.ofReal)
  have hi : (∫ y : ℂ, (K y : ℂ)) = planarGaussConstant (γ ^ 2 / 2) (γ * α₁) := by
    simpa only [norm_one, Real.one_rpow, Complex.ofReal_one, one_mul] using
      (planar_difference_integral _ _ hk hβ hβ2 1).2
  rw [hi] at hc
  have hr := Complex.continuous_re.continuousAt.tendsto.comp hc
  have he : (∫⁻ ω, fusionMovingMass γ α₁ α₂ α₃ 1 0 (M ω) ^ (-p - 1) ∂P) =
      ∫⁻ ω, gammaHalfRootedMass γ α₁ α₂ α₃ M ω ^ (-p - 1) ∂P := by
    apply lintegral_congr_ae
    filter_upwards [fusionMovingMass_eq_rooted_ae P X hX γ hγ hγ2 M hM α₁ α₂ α₃ 1 0] with ω h
    simp only [mul_zero] at h
    rw [h]
    rfl
  simp only [Function.comp_def, ← Complex.ofReal_mul, integral_complex_ofReal, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, he] at hr
  change Tendsto _ _ (nhds (gammaHalfRootedCoefficient P M γ α₁ α₂ α₃ p)) at hr
  apply (hr.mono_left nhdsWithin_le_nhds).congr'
  have hz4 : ∀ᶠ z : ℂ in nhdsWithin 0 {0}ᶜ, ‖z‖ ≤ 1 / 4 :=
    (((continuous_norm.tendsto (0 : ℂ)).eventually_lt_const (by simp : ‖(0 : ℂ)‖ < (1 / 4 : ℝ))).filter_mono
      nhdsWithin_le_nhds).mono fun _ h => h.le
  filter_upwards [hz4, self_mem_nhdsWithin] with z hz4 hz
  have hz0 : z ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using hz
  have hi' : (∫ t in Icc (0 : ℝ) 1, ∫ ω,
      (fusionUnrootedSegment γ α₁ α₂ α₃ t z (M ω) ^ (-p - 1)).toReal *
        (∫ x in Metric.ball (0 : ℂ) (1 / 2), fusionDifferenceKernel γ α₁ α₂ α₃ z x ∂M ω) ∂P) =
      ‖z‖ ^ (γ * (Q γ - α₁)) * ∫ t in Icc (0 : ℝ) 1,
        ∫ y : ℂ, K y * fusionInterpolatedFactor P M γ α₁ α₂ α₃ (-p - 1) t y z := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact fusion_localDifference_rooting_scaled P X hX γ hγ hγ2 M hM α₁ α₂ α₃ hlo hα₁ hα₂ hα₃ p hp t ht z hz0 hz4
  rw [hi', mul_div_cancel_left₀ _ (Real.rpow_pos_of_pos (norm_pos_iff.mpr hz0) _).ne']
end DOZZ.Proofs

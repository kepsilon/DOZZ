/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.ScaledSpatialConvergence
public import DOZZ.FourPoint.TaylorTimeIntegration

/-! # Dominated time integration of the scaled rooted spatial observable -/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The time weight in the Taylor integral has its exact elementary value. -/
theorem fusion_time_weight_integral (e : ℝ) (he : -1 < e) :
    IntegrableOn (fun t : ℝ => (1 - t) * t ^ e) (Icc 0 1) volume ∧
      (∫ t in Icc (0 : ℝ) 1, (1 - t) * t ^ e) = 1 / ((e + 1) * (e + 2)) := by
  obtain ⟨h1, hv1⟩ := time_rpow_integral e he
  obtain ⟨h2, hv2⟩ := time_rpow_integral (e + 1) (by linarith)
  have heq : (fun t : ℝ => t ^ e - t ^ (e + 1)) =ᵐ[volume.restrict (Icc 0 1)]
      (fun t => (1 - t) * t ^ e) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (Measure.ae_ne volume (0 : ℝ))] with t ht ht0
    have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    rw [Real.rpow_add htpos, Real.rpow_one]
    ring
  refine ⟨(h1.sub h2).congr heq, ?_⟩
  rw [← integral_congr_ae heq, integral_sub h1 h2, hv1, hv2]
  field_simp [show e + 1 ≠ 0 by linarith, show e + 1 + 1 ≠ 0 by linarith,
    show e + 2 ≠ 0 by linarith]
  ring

/-- The spatial domination is uniform in time, leaving the integrable weight `t^e`. -/
theorem fusionScaledTimeIntegral_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hα : γ / 2 ≤ α₁) (hα₁ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (s : ℝ) (hs : s < 0)
    (K : ℂ → ℂ) (hKm : Measurable K) (hK : Integrable K volume)
    (e : ℝ) (he : -1 < e) :
    Tendsto (fun z : ℂ => ∫ t in Icc (0 : ℝ) 1, ((1 - t) * t ^ e : ℝ) *
      (∫ y : ℂ, K y * (fusionScaledFactor P M γ α₁ α₂ α₃ s y ((t : ℂ) * z) : ℂ)))
      (nhds 0) (nhds ((1 / ((e + 1) * (e + 2)) : ℝ) *
        ((∫ y : ℂ, K y) *
          ((∫⁻ ω, fusionMovingMass γ α₁ α₂ α₃ 1 0 (M ω) ^ s ∂P).toReal : ℂ)))) := by
  obtain ⟨B, hB, hb⟩ := fusionScaledFactor_uniform_bound P X hX γ hγ hγ2 M hM α₁ α₂ α₃ s hs.le
  let D := (∫ y : ℂ, ‖K y‖) * B
  have hD : 0 ≤ D := mul_nonneg (integral_nonneg fun _ => norm_nonneg _) hB
  have hspacebound : ∀ w : ℂ, ‖w‖ ≤ 1 →
      ‖∫ y : ℂ, K y * (fusionScaledFactor P M γ α₁ α₂ α₃ s y w : ℂ)‖ ≤ D := by
    intro w hw
    calc
      _ ≤ ∫ y : ℂ, ‖K y‖ * B := norm_integral_le_of_norm_le (hK.norm.mul_const B)
        (ae_of_all _ fun y => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hb y w hw) (norm_nonneg _))
      _ = D := integral_mul_const _ _
  have hsm := fusionScaledIntegral_measurable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ s K hKm
  have hsl := fusionScaledIntegral_tendsto P X hX γ hγ hγ2 M hM α₁ α₂ α₃
    hα hα₁ hα₂ hα₃ s hs K hK
  have hmeas : ∀ᶠ z : ℂ in nhds 0, AEStronglyMeasurable
      (fun t : ℝ => ((1 - t) * t ^ e : ℝ) *
        (∫ y : ℂ, K y * (fusionScaledFactor P M γ α₁ α₂ α₃ s y ((t : ℂ) * z) : ℂ)))
      (volume.restrict (Icc 0 1)) := by
    apply Eventually.of_forall
    intro z
    have ht : Measurable (fun t : ℝ => ((1 - t) * t ^ e : ℝ)) :=
      (measurable_const.sub measurable_id).mul (measurable_id.pow_const e)
    exact ((Complex.measurable_ofReal.comp ht).mul
      (hsm.comp (Complex.measurable_ofReal.mul_const z))).aestronglyMeasurable
  have hdom : ∀ᶠ z : ℂ in nhds 0, ∀ᵐ t : ℝ ∂volume.restrict (Icc 0 1),
      ‖((1 - t) * t ^ e : ℝ) *
        (∫ y : ℂ, K y * (fusionScaledFactor P M γ α₁ α₂ α₃ s y ((t : ℂ) * z) : ℂ))‖ ≤ t ^ e * D := by
    have hz : ∀ᶠ z : ℂ in nhds 0, ‖z‖ ≤ 1 :=
      ((continuous_norm.tendsto (0 : ℂ)).eventually_lt_const (by simp)).mono fun _ h => h.le
    filter_upwards [hz] with z hz
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have htz : ‖(t : ℂ) * z‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.1]
      calc
        t * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
        _ ≤ 1 := by simpa only [one_mul] using hz
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) (Real.rpow_nonneg ht.1 _))]
    have hweight : (1 - t) * t ^ e ≤ t ^ e := by
      exact mul_le_of_le_one_left (Real.rpow_nonneg ht.1 _) (by linarith only [ht.1])
    exact mul_le_mul hweight (hspacebound _ htz) (norm_nonneg _) (Real.rpow_nonneg ht.1 _)
  have hlim : ∀ᵐ t : ℝ ∂volume.restrict (Icc 0 1), Tendsto
      (fun z : ℂ => ((1 - t) * t ^ e : ℝ) *
        (∫ y : ℂ, K y * (fusionScaledFactor P M γ α₁ α₂ α₃ s y ((t : ℂ) * z) : ℂ)))
      (nhds 0) (nhds (((1 - t) * t ^ e : ℝ) *
        ((∫ y : ℂ, K y) *
          ((∫⁻ ω, fusionMovingMass γ α₁ α₂ α₃ 1 0 (M ω) ^ s ∂P).toReal : ℂ)))) := by
    apply ae_of_all
    intro t
    have ht : Tendsto (fun z : ℂ => (t : ℂ) * z) (nhds 0) (nhds 0) := by
      have hc : Continuous (fun z : ℂ => (t : ℂ) * z) := continuous_const.mul continuous_id
      simpa only [mul_zero] using hc.tendsto (0 : ℂ)
    exact tendsto_const_nhds.mul (hsl.comp ht)
  have h := tendsto_integral_filter_of_dominated_convergence (fun t : ℝ => t ^ e * D)
    hmeas hdom ((time_rpow_integral e he).1.mul_const D) hlim
  simpa only [integral_mul_const, integral_complex_ofReal, (fusion_time_weight_integral e he).2] using h

end DOZZ.Proofs

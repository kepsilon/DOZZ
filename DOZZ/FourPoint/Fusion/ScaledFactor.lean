/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.Fusion.MovingExpectationMeasurable

/-! # The bounded factor in the rescaled local rooting integrals -/

@[expose] public section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The unit-chart cutoff and the remaining insertion weight after `x = y*z`. -/
noncomputable def fusionScaledFactor {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (M : Ω → Measure ℂ) (γ α₁ α₂ α₃ s : ℝ) (y z : ℂ) : ℝ :=
  if ‖y * z‖ < 1 / 2 then ‖y * z - 1‖ ^ (-γ * α₂) *
    (∫⁻ ω, fusionMovingMass γ α₁ α₂ α₃ y z (M ω) ^ s ∂P).toReal else 0

theorem fusionScaledFactor_measurable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ s : ℝ) :
    Measurable (fun q : ℂ × ℂ => fusionScaledFactor P M γ α₁ α₂ α₃ s q.1 q.2) := by
  apply Measurable.ite
  · exact measurableSet_lt (measurable_fst.mul measurable_snd).norm measurable_const
  · exact (((measurable_fst.mul measurable_snd).sub_const (1 : ℂ)).norm.pow_const _).mul
      (fusionMovingMass_expectation_measurable P X hX γ hγ hγ2 M hM α₁ α₂ α₃ s).ennreal_toReal
  · exact measurable_const

/-- A uniform inverse moment bound also controls the entire remaining scaled factor. -/
theorem fusionScaledFactor_uniform_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ s : ℝ) (hs : s ≤ 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y z : ℂ, ‖z‖ ≤ 1 →
      |fusionScaledFactor P M γ α₁ α₂ α₃ s y z| ≤ B := by
  obtain ⟨C, hC, hbound⟩ := fusionMovingMass_inverse_moment_uniform P X hX γ hγ hγ2 M hM
    α₁ α₂ α₃ s hs
  let b := max ((1 / 2 : ℝ) ^ (-γ * α₂)) ((3 / 2 : ℝ) ^ (-γ * α₂))
  have hb : 0 ≤ b := le_trans (by positivity) (le_max_left _ _)
  refine ⟨b * C.toReal, mul_nonneg hb ENNReal.toReal_nonneg, ?_⟩
  intro y z hz
  dsimp only [fusionScaledFactor]
  split_ifs with hyz
  · have hl : (1 / 2 : ℝ) ≤ ‖y * z - 1‖ := by
      have h := norm_sub_norm_le (1 : ℂ) (y * z)
      rw [norm_one, norm_sub_rev] at h
      linarith
    have hu : ‖y * z - 1‖ ≤ (3 / 2 : ℝ) := by
      have h := norm_sub_le (y * z) (1 : ℂ)
      rw [norm_one] at h
      linarith
    have hrpow : ‖y * z - 1‖ ^ (-γ * α₂) ≤ b := by
      by_cases he : 0 ≤ -γ * α₂
      · exact (Real.rpow_le_rpow (norm_nonneg _) hu he).trans (le_max_right _ _)
      · exact (Real.rpow_le_rpow_of_nonpos (by norm_num) hl (le_of_not_ge he)).trans
          (le_max_left _ _)
    rw [abs_of_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) ENNReal.toReal_nonneg)]
    exact mul_le_mul hrpow (ENNReal.toReal_mono hC.ne (hbound y z hz))
      ENNReal.toReal_nonneg hb
  · simpa using mul_nonneg hb ENNReal.toReal_nonneg

/-- At each nonzero rescaled root the remaining factor tends to the common inverse expectation. -/
theorem fusionScaledFactor_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → Distr) (hX : IsEquatorGFF P X)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (hα : γ / 2 ≤ α₁) (hα₁ : α₁ < 2 / γ)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (y : ℂ) (hy : y ≠ 0)
    (s : ℝ) (hs : s < 0) :
    Tendsto (fusionScaledFactor P M γ α₁ α₂ α₃ s y) (nhds 0)
      (nhds ((∫⁻ ω, fusionMovingMass γ α₁ α₂ α₃ y 0 (M ω) ^ s ∂P).toReal)) := by
  have he := fusionMovingMass_inverse_expectation P X hX γ hγ hγ2 M hM α₁ α₂ α₃
    hα hα₁ hα₂ hα₃ y hy s hs
  have hfin := fusionMovingMass_inverse_expectation_finite P X hX γ hγ hγ2 M hM
    α₁ α₂ α₃ s hs.le y
  have he' := (ENNReal.continuousAt_toReal hfin.ne).tendsto.comp he
  have hw : Tendsto (fun z : ℂ => ‖y * z - 1‖ ^ (-γ * α₂)) (nhds 0) (nhds 1) := by
    have hn : Tendsto (fun z : ℂ => ‖y * z - 1‖) (nhds 0) (nhds 1) := by
      have hc : Continuous (fun z : ℂ => y * z - (1 : ℂ)) :=
        (continuous_const.mul continuous_id).sub continuous_const
      simpa using hc.norm.tendsto (0 : ℂ)
    simpa only [Function.comp_def, Real.one_rpow] using
      (Real.continuousAt_rpow_const 1 (-γ * α₂) (Or.inl one_ne_zero)).tendsto.comp hn
  have hcut : ∀ᶠ z : ℂ in nhds 0, ‖y * z‖ < 1 / 2 := by
    have hn : Tendsto (fun z : ℂ => ‖y * z‖) (nhds 0) (nhds 0) := by
      simpa using (continuous_const.mul continuous_id).norm.tendsto (0 : ℂ)
    exact hn.eventually_lt_const (by norm_num)
  have h := hw.mul he'
  simp only [one_mul, Function.comp_def] at h
  apply h.congr'
  filter_upwards [hcut] with z hz
  simp only [fusionScaledFactor, ite_eq_left hz]

end DOZZ.Proofs

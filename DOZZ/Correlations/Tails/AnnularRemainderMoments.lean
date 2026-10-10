/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.WeightedMomentModelLaw
public import DOZZ.GMC.BallAnnulus.Ball
public import DOZZ.GMC.WeightedCutoff.ReferenceUniform

/-! Uniform moments of insertion weights away from their singular center. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace DOZZ.Proofs

theorem annular_kernel_le (γ α A ρ : ℝ) (hγ : 0 < γ)
    (hα : 0 ≤ α) (hαA : α ≤ A) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (x z : ℂ) (hx : ρ ≤ ‖x-z‖) :
    (ENNReal.ofReal ‖x-z‖)^(-γ*α) ≤ ENNReal.ofReal (ρ^(-γ*A)) := by
  rw [ENNReal.ofReal_rpow_of_pos (hρ.trans_le hx)]
  apply ENNReal.ofReal_le_ofReal
  calc ‖x-z‖^(-γ*α) ≤ ρ^(-γ*α) :=
      Real.rpow_le_rpow_of_nonpos hρ hx (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hγ.le) hα)
    _ ≤ ρ^(-γ*A) := Real.rpow_le_rpow_of_exponent_ge hρ (hρ1)
      (by simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_left hαA hγ.le))

theorem annular_remainder_moment_uniform
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (K : Set ℂ) (hK : IsCompact K) (ρ A b R : ℝ)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hb : 0 ≤ b)
    (hR : 0 < R) (hRbulk : R < 4/γ^2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ z ∈ K, ∀ α r : ℝ,
      0 ≤ α → α ≤ A → 0 < r → r ≤ R →
      ∀ F : ℂ → ℝ, (∀ x, 0 ≤ F x ∧ F x ≤ b) →
      (∫⁻ ω, (∫⁻ x in Metric.ball z 1 \ Metric.ball z ρ,
        ENNReal.ofReal (F x)*(ENNReal.ofReal ‖x-z‖)^(-γ*α) ∂M ω)^r ∂P) ≤ C := by
  let : IsProbabilityMeasure P := hX.1
  obtain ⟨D,_,hbound⟩ := equatorGFF_GMC_ball_moment_bound P X hX γ hγ hγ2
    M hM R hRbulk K hK
  let k := ENNReal.ofReal (1+b*ρ^(-γ*A))
  have hkfin : k ≠ ⊤ := ENNReal.ofReal_ne_top
  have hk1 : 1 ≤ k := ENNReal.one_le_ofReal.mpr (by
    have hw : 0 ≤ b*ρ^(-γ*A) := mul_nonneg hb (Real.rpow_nonneg hρ.le _)
    linarith only [hw])
  refine ⟨k^R*(1+ENNReal.ofReal D),ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg hR.le hkfin) (by simp),?_⟩
  intro z hzk α r hα hαA hr hrR F hF
  have hpoint (ω : Ω) : (∫⁻ x in Metric.ball z 1 \ Metric.ball z ρ,
      ENNReal.ofReal (F x)*(ENNReal.ofReal ‖x-z‖)^(-γ*α) ∂M ω) ≤
      k*M ω (Metric.ball z 1) := by
    calc _ ≤ ∫⁻ x in Metric.ball z 1 \ Metric.ball z ρ, k ∂M ω := by
          apply setLIntegral_mono' (Metric.isOpen_ball.measurableSet.diff Metric.isOpen_ball.measurableSet)
          intro x hx
          have hxρ : ρ ≤ ‖x-z‖ := by
            simpa only [Metric.mem_ball,dist_eq_norm,not_lt] using hx.2
          calc ENNReal.ofReal (F x)*(ENNReal.ofReal ‖x-z‖)^(-γ*α)
              ≤ ENNReal.ofReal b*ENNReal.ofReal (ρ^(-γ*A)) :=
                mul_le_mul' (ENNReal.ofReal_le_ofReal (hF x).2)
                  (annular_kernel_le γ α A ρ hγ hα hαA hρ hρ1 x z hxρ)
            _ ≤ k := by
              rw [← ENNReal.ofReal_mul hb]
              exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left zero_le_one)
      _ ≤ k*M ω (Metric.ball z 1) := by
          rw [lintegral_const,Measure.restrict_apply_univ]
          exact mul_le_mul' le_rfl (measure_mono sdiff_subset)
  have hm := gmc_set_mass_aemeasurable_of_isGMCOf P X hX γ hγ hγ2 M hM
    (Metric.ball z 1) Metric.isOpen_ball.measurableSet
  have hsmall := lintegral_rpow_le_measure_add_larger_order P _ hm hr.le hrR
  have hmass : (∫⁻ ω, (M ω (Metric.ball z 1))^r ∂P) ≤ 1+ENNReal.ofReal D := by
    have hbig := (hbound z hzk 1 zero_lt_one le_rfl).2
    simp only [Real.rpow_eq_pow,Real.one_rpow,mul_one,gmcMassMoment,ENNReal.rpow_eq_pow] at hbig
    exact hsmall.trans (by simpa only [measure_univ,ENNReal.rpow_eq_pow] using add_le_add le_rfl hbig)
  calc _ ≤ ∫⁻ ω, (k*M ω (Metric.ball z 1))^r ∂P :=
        lintegral_mono fun ω => ENNReal.rpow_le_rpow (hpoint ω) hr.le
    _ = k^r*(∫⁻ ω, (M ω (Metric.ball z 1))^r ∂P) := by
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le]
        exact lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hr.le hkfin)
    _ ≤ k^R*(1+ENNReal.ofReal D) := mul_le_mul'
      (ENNReal.rpow_le_rpow_of_exponent_le hk1 hrR) hmass

theorem annular_remainder_moment_uniform_models
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (K : Set ℂ) (hK : IsCompact K) (ρ A b R : ℝ)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hb : 0 ≤ b)
    (hR : 0 < R) (hRbulk : R < 4/γ^2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (P' : Measure Ω) (X' : Ω → Distr) (N : Ω → Measure ℂ),
      IsEquatorGFF P' X' → IsGMCOf P' X' γ N →
      ∀ z ∈ K, ∀ α r : ℝ, 0 ≤ α → α ≤ A → 0 < r → r ≤ R →
      ∀ F : ℂ → ℝ, Measurable F → (∀ x, 0 ≤ F x ∧ F x ≤ b) →
      (∫⁻ ω, (∫⁻ x in Metric.ball z 1 \ Metric.ball z ρ,
        ENNReal.ofReal (F x)*(ENNReal.ofReal ‖x-z‖)^(-γ*α) ∂N ω)^r ∂P') ≤ C := by
  obtain ⟨C,hC,hbound⟩ := annular_remainder_moment_uniform
    P X hX γ hγ hγ2 M hM K hK ρ A b R hρ hρ1 hb hR hRbulk
  refine ⟨C,hC,?_⟩
  intro P' X' N hX' hN z hzk α r hα hαA hr hrR F hFm hF
  have hw : Measurable (fun x : ℂ => ENNReal.ofReal (F x)*
      (ENNReal.ofReal ‖x-z‖)^(-γ*α)) := by fun_prop
  have hd : MeasurableSet (Metric.ball z 1 \ Metric.ball z ρ) :=
    Metric.isOpen_ball.measurableSet.diff Metric.isOpen_ball.measurableSet
  have hm : Measurable (fun μ : Measure ℂ =>
      (∫⁻ x in Metric.ball z 1 \ Metric.ball z ρ,
        ENNReal.ofReal (F x)*(ENNReal.ofReal ‖x-z‖)^(-γ*α) ∂μ)^r) := by
    have h := (Measure.measurable_lintegral (hw.indicator hd)).pow_const r
    simpa only [lintegral_indicator hd] using h
  have hl := equatorGFF_GMC_law_transport P X hX P' X' hX' γ hγ hγ2 M hM N hN
    (fun _ μ => (∫⁻ x in Metric.ball z 1 \ Metric.ball z ρ,
      ENNReal.ofReal (F x)*(ENNReal.ofReal ‖x-z‖)^(-γ*α) ∂μ)^r)
    (hm.comp measurable_snd)
  rw [← hl]
  exact hbound z hzk α r hα hαA hr hrR F hF


end DOZZ.Proofs
